module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
import StacksCore.Tactic.StacksAttribute

/-!
# A left adjoint of the pullback of sheaves of modules

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi in the sense of
Stacks 01D3. Its pullback of sheaves of modules `f^*G = O_C ⊗_{f⁻¹O_D} f⁻¹G` of Stacks 03D6 is a
left adjoint, of the direct image `f_*`. This file gives a criterion for it to be a *right*
adjoint as well, i.e. for the **lower shriek** `f_!` left adjoint to `f^*` to exist:

* the structure map `f⁻¹O_D ⟶ O_C` is an isomorphism, so that extension of scalars along it is an
  equivalence rather than merely a left adjoint; and
* the inverse image of sheaves of modules has a left adjoint, which it does whenever `f⁻¹` is
  restriction along a continuous functor of sites whose source is essentially small.

Both hypotheses hold for the inclusion of a full subsite which is continuous and cocontinuous and
carries the restricted structure sheaf, which is the situation of Stacks 0788; the lower shriek it
produces is the one of Stacks 0789.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.lowerShriekModules`: the functor `f_!` on sheaves of modules,
  the left adjoint of `f^*`.
* `AlgebraicGeometry.RingedToposHom.lowerShriekAdjPullbackModules`: the adjunction
  `f_! ⊣ f^*`.

## Main results

* `SheafOfModules.isEquivalence_restrictScalars`: restriction of scalars along an isomorphism of
  sheaves of rings is an equivalence. This reads off
  `Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`, which already constructs that
  equivalence; nothing is reproved.
* `Stacks.Sheaves.ToposPullback.isRightAdjoint_restrictionModules`: restriction of sheaves of
  modules along a continuous functor of sites has a left adjoint when the source site is
  essentially small.
* `Stacks.Sheaves.ToposPullback.isRightAdjoint_pullbackModuleFunctor_restriction`: hence so does
  the inverse image of sheaves of modules along the morphism of topoi whose inverse image is that
  restriction.
* `AlgebraicGeometry.RingedToposHom.forgetRing_map_fSharpInverseImage`: the two forms of the
  inverse-image structure map — the one at `CommRingCat` obtained from `f♯` through the
  adjunction for sheaves of commutative rings, and the one at `RingCat` obtained from it through
  the adjunction for sheaves of rings — have the same underlying morphism of sheaves of sets.
  The docstring of `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing` records that this
  identification had not been made; it is made here, and it is what transports invertibility from
  the one form to the other.
* `AlgebraicGeometry.RingedToposHom.isIso_fSharpInverseImageRing`: consequently the `RingCat`
  form is invertible as soon as the `CommRingCat` form is.
* `AlgebraicGeometry.RingedToposHom.isRightAdjoint_extendScalarsFSharp`: extension of scalars
  along an invertible structure map has a left adjoint.
* `AlgebraicGeometry.RingedToposHom.isRightAdjoint_pullbackModules`: the pullback of sheaves of
  modules has a left adjoint.

## Implementation notes

The pullback of Stacks 03D6 is the inverse image followed by extension of scalars, and a composite
of two right adjoints is a right adjoint; so the criterion is proved factor by factor and no
identification of `f^*` with restriction is needed. That identification — the content of
Stacks 0788 for a subsite inclusion — would be a strictly stronger statement, and it is not
required for the existence of the lower shriek.

Invertibility of the structure map is stated for the `CommRingCat` form
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage`, because that is the form in which the
constructions of ringed topoi produce it, while extension of scalars consumes the `RingCat` form;
`forgetRing_map_fSharpInverseImage` is the bridge. It is proved by transposing both forms across
the *same* adjunction of sheaves of sets, which is legitimate because
`(sheafCompose Y.J (forget RingCat)).map f.fSharpRing` and `Y.forgetRing.map f.fSharp` are equal
on the nose: forgetting commutativity and then forgetting the ring operations is forgetting the
ring operations.

Restriction of scalars along an isomorphism is an equivalence, and that is what makes extension of
scalars along the structure map a *right* adjoint: it is a left adjoint of an equivalence, hence
the quasi-inverse of it, hence has an adjoint on both sides. The equivalence itself is
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`; only its registration as an
instance is added here.

Restriction of sheaves of modules along a continuous functor is
`SheafOfModules.pushforward` at the identity structure map, so its left adjoint is Mathlib's
`SheafOfModules.PullbackConstruction.adjunction`; the identity morphism of sheaves of rings is
written with its type ascribed, as the extension-by-zero declarations do, because `𝟙 R` does not
support field notation.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.RingedToposModules

namespace SheafOfModules

universe uw uv uu

variable {C : Type uu} [Category.{uv} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{uw}}

/-- **Restriction of scalars along an isomorphism of sheaves of rings is an equivalence** of the
categories of sheaves of modules. The equivalence is
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`, whose functor is restriction of
scalars along the *inverse* of the given isomorphism; applying it to the inverse isomorphism of
`α` therefore returns `restrictScalars α` on the nose. Instance, so that the quasi-inverse and
the adjunctions on both sides are available by instance search. -/
instance isEquivalence_restrictScalars (α : R ⟶ R') [IsIso α] :
    (restrictScalars.{uw} α).IsEquivalence :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso α).symm).isEquivalence_functor

end SheafOfModules

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [K.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{ww})
  [EssentiallySmall.{ww} C] [LocallySmall.{ww} D]
  [HasWeakSheafify K AddCommGrpCat.{ww}] [K.WEqualsLocallyBijective AddCommGrpCat.{ww}]

/-- The restriction of the sheaf of rings `O` along `G`, as a sheaf of rings on the source site.
The identity morphism of this sheaf is the structure map that presents restriction of sheaves of
modules as a pushforward. -/
@[sga "4 IV 14.1" "partial"]
abbrev restrictionRingSheaf : Sheaf J RingCat.{ww} :=
  (G.sheafPushforwardContinuous RingCat.{ww} J K).obj O

/-- **Restriction of sheaves of modules along a continuous functor of sites has a left adjoint**
as soon as the source site is essentially small in the universe of the sheaf of rings and of the
module sections. This is the lower shriek for modules over the restricted sheaf of rings. -/
instance isRightAdjoint_restrictionModules : (restrictionModules J K G O).IsRightAdjoint :=
  have _ : (PresheafOfModules.pushforward.{ww} (F := G) (R := O.obj)
      (S := (restrictionRingSheaf J K G O).obj)
      (𝟙 (restrictionRingSheaf J K G O) :
        restrictionRingSheaf J K G O ⟶ restrictionRingSheaf J K G O).hom).IsRightAdjoint :=
    PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{ww} _
  (SheafOfModules.PullbackConstruction.adjunction.{ww}
    (𝟙 (restrictionRingSheaf J K G O) :
      restrictionRingSheaf J K G O ⟶ restrictionRingSheaf J K G O)).isRightAdjoint

section

variable [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})]

/-- **The inverse image of sheaves of modules along the morphism of topoi presented by a
continuous functor of sites has a left adjoint**, when the source site is essentially small in the
universe of the sheaf of rings and of the module sections.

The inverse image is restriction of modules followed by restriction of scalars along the
comparison `Stacks.Sheaves.ToposPullback.restrictionRingIso` of the inverse-image sheaf of rings
with the restricted one (`restrictionModuleIso`, which is Stacks 03D2 for a continuous functor);
restriction has a left adjoint, and restriction of scalars along an isomorphism is an
equivalence. -/
instance isRightAdjoint_pullbackModuleFunctor_restriction :
    (pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) O).IsRightAdjoint :=
  have _ : (restrictionModules J K G O ⋙
      SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).IsRightAdjoint :=
    inferInstance
  Functor.isRightAdjoint_of_iso (restrictionModuleIso J K G O).symm

end

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- **The two forms of the inverse-image structure map agree on underlying sheaves of sets.** The
`CommRingCat` form `f.fSharpInverseImage` is the transpose of `f♯` under the adjunction
`f⁻¹ ⊣ f_*` for sheaves of commutative rings, and the `RingCat` form `f.fSharpInverseImageRing`
is the transpose of the same `f♯` under the adjunction for sheaves of rings; both transposes are
computed by the transpose for sheaves of sets, of one and the same morphism. -/
theorem forgetRing_map_fSharpInverseImage :
    X.forgetRing.map f.fSharpInverseImage =
      (sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImageRing := by
  refine (fSharpInverseImage_forget_homEquiv f).trans ?_
  exact (congrArg (f.toToposHom.adj.homEquiv _ _).symm (fSharpInverseImageRing_adjunct f)).trans
    (Equiv.symm_apply_apply _ _)

/-- If the `CommRingCat` form of the inverse-image structure map is invertible, so is the
`RingCat` form: the two have the same underlying morphism of sheaves of sets, and a morphism of
sheaves of rings whose underlying morphism of sheaves of sets is invertible is invertible. -/
instance isIso_fSharpInverseImageRing [IsIso f.fSharpInverseImage] :
    IsIso f.fSharpInverseImageRing := by
  have _ : IsIso ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImageRing) := by
    rw [← forgetRing_map_fSharpInverseImage]
    exact (X.forgetRing.mapIso (asIso f.fSharpInverseImage)).isIso_hom
  exact isIso_of_reflects_iso _ (sheafCompose X.J (forget RingCat.{w}))

section Modules

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- **Extension of scalars along an invertible structure map has a left adjoint.** Extension of
scalars is left adjoint to restriction of scalars along the same map, and restriction of scalars
along an isomorphism is an equivalence; so extension of scalars is the quasi-inverse of that
equivalence, which has an adjoint on both sides. -/
theorem isRightAdjoint_extendScalarsFSharp [IsIso f.fSharpInverseImage] :
    (extendScalarsFSharp f.toModulesHom).IsRightAdjoint := by
  have _ : IsIso (commRingSheafMap X.J (fSharpCommRing f.toModulesHom)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) := isIso_fSharpInverseImageRing f
  have h : extendScalarsFSharp f.toModulesHom ≅
      (SheafOfModules.restrictScalars.{w} (commRingSheafMap X.J (fSharpCommRing f.toModulesHom)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).asEquivalence.inverse :=
    (extendRestrictScalarsAdjunction X.J (fSharpCommRing f.toModulesHom) _ _).leftAdjointUniq
      (Functor.asEquivalence _).symm.toAdjunction
  exact ((Functor.asEquivalence _).toAdjunction.ofNatIsoRight h.symm).isRightAdjoint

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The pullback of sheaves of modules along a morphism of ringed topoi has a left adjoint**,
given that the structure map is invertible and that the inverse image of sheaves of modules has a
left adjoint. The pullback is the inverse image followed by extension of scalars, and a composite
of right adjoints is a right adjoint.

The adjointness of the inverse image is an explicit hypothesis rather than an instance: at the
morphisms this is applied to, the inverse image is read off a projection of the morphism of ringed
topoi, which instance search does not unfold. -/
theorem isRightAdjoint_pullbackModules [IsIso f.fSharpInverseImage]
    (h : (inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).IsRightAdjoint) :
    (f.toModulesHom.pullbackModules).IsRightAdjoint := by
  have _ := h
  have _ := isRightAdjoint_extendScalarsFSharp f
  exact ((Adjunction.ofIsRightAdjoint (extendScalarsFSharp f.toModulesHom)).comp
    (Adjunction.ofIsRightAdjoint (inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).isRightAdjoint

variable [(f.toModulesHom.pullbackModules).IsRightAdjoint]

/-- **The lower shriek `f_!` on sheaves of modules**: the left adjoint of the pullback `f^*` of
Stacks 03D6, when it exists. -/
def lowerShriekModules :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (f.toModulesHom.pullbackModules).leftAdjoint

/-- **The adjunction `f_! ⊣ f^*`** defining the lower shriek on sheaves of modules. -/
def lowerShriekAdjPullbackModules : f.lowerShriekModules ⊣ f.toModulesHom.pullbackModules :=
  Adjunction.ofIsRightAdjoint _

end Modules

end AlgebraicGeometry.RingedToposHom

end
