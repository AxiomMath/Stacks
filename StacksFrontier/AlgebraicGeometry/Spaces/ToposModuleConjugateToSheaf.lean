module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardAbelianSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso

/-!
# The abelian sheaf underlying an inverse image of modules along a conjugate

`Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso` is the compatibility of Stacks 03D1
with the forgetful functor to abelian sheaves for a transporting functor of sheaves of sets that
is *isomorphic to restriction* along a continuous functor of sites: its comparison datum
`ε : Φ ≅ G.sheafPushforwardContinuous …` forces that shape.  A functor conjugated by an
equivalence of sheaf categories — which is what the direct image of Stacks 03G2, part (1) becomes
on the small étale sites of algebraic spaces once the comparison equivalences of Stacks 03G1 are
inserted — is not of that shape, and the restriction form of the statement cannot be
instantiated at it.

This file supplies the two closure properties that get a conjugate from the restriction case: the
compatibility composes along a composite of transporting functors, and it holds for the *inverse*
of an equivalence induced by a continuous functor.  A three-factor conjugate is then two
compositions and one inverse.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackModuleToSheafIsoComp`: the compatibility for a composite
  `Ψ ⋙ Φ` of transporting functors, from the compatibility for each factor.
* `Stacks.Sheaves.ToposPullback.pullbackModuleInverseToSheafIso`: the compatibility for the
  inverse of the equivalence of sheaf categories induced by a continuous functor of sites.

## Implementation notes

The hypotheses of `Stacks.Sheaves.ToposPullback.pullbackModuleToSheafIsoComp` are families of
isomorphisms indexed by the sheaf of rings, not single isomorphisms: the outer factor is applied
to the inverse image `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` of the sheaf of rings along
the inner one, so one instance of each hypothesis is not enough.  No naturality in the sheaf of
rings is used, so no coherence is asked of the families.

Two identifications in the chain are definitional and are left as such rather than carried as
isomorphisms: restriction of scalars is invisible to the forgetful functor to abelian sheaves,
`SheafOfModules.restrictScalars a ⋙ SheafOfModules.toSheaf _ = SheafOfModules.toSheaf _`, which
is what absorbs the comparisons of inverse-image sheaves of rings that
`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso` and
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` introduce; and restriction along
the identity functor of a site *is* the identity functor of its sheaf category, at both
coefficient categories, so the identity case of the restriction statement needs no comparison
functor.

Every statement below keeps its transporting functors as *variables*.  That is not presentation:
the chain of isomorphisms matches up only through the definitional absorption of restriction of
scalars above, and at an abstract transporting functor the kernel checks that in no time, while
at the three-factor conjugate of the small étale sites — where the factors are a right Kan
extension and the inverse of an equivalence — the same check exhausts the kernel's budget.  So
`Stacks.Sheaves.ToposPullback.pullbackModuleInverseToSheafIso` is assembled from two statements
with a free functor each, and the conjugate only ever appears as an argument.

The inverse case is proved by composing with the equivalence rather than by inverting the
isomorphism: the compatibility for the inverse whiskered by the equivalence collapses, through
`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso` and the counit of the equivalence, to the
identity case, and the inverse form is recovered from the unit.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu' vv'' uu''

section Absorb

variable {C : Type uu} [Category.{vv} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] {R R' : Sheaf J RingCat.{ww}}

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- **Restriction of scalars is invisible to the forgetful functor to abelian sheaves.**  The
sections of a sheaf of modules read over a smaller sheaf of rings are the same sections with the
same addition. -/
theorem restrictScalars_comp_toSheaf (a : R ⟶ R') :
    SheafOfModules.restrictScalars a ⋙ SheafOfModules.toSheaf.{ww} R =
      SheafOfModules.toSheaf.{ww} R' := rfl

/-- `Stacks.Sheaves.ToposPullback.restrictScalars_comp_toSheaf` as the isomorphism that absorbs a
restriction of scalars standing between a functor into sheaves of modules and the forgetful
functor to abelian sheaves.

It is stated separately, and with its sheaves of rings free, because the same identification made
in place forces the kernel to unfold the two sheaves of rings it compares; here it is checked once
and afterwards only instantiated. -/
def compRestrictScalarsToSheafIso {𝒜 : Type uu''} [Category.{vv''} 𝒜]
    (B : 𝒜 ⥤ SheafOfModules.{ww} R') (a : R ⟶ R') :
    (B ⋙ SheafOfModules.restrictScalars a) ⋙ SheafOfModules.toSheaf.{ww} R ≅
      B ⋙ SheafOfModules.toSheaf.{ww} R' :=
  Functor.associator B (SheafOfModules.restrictScalars a)
      (SheafOfModules.toSheaf.{ww} R) ≪≫
    Functor.isoWhiskerLeft B (eqToIso (restrictScalars_comp_toSheaf a))

end Absorb

section Comp

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {E : Type uu''} [Category.{vv''} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [L.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [L.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (Ψ : Sheaf L (Type ww) ⥤ Sheaf K (Type ww)) [PreservesFiniteProducts Ψ]
  (Φa : Sheaf K AddCommGrpCat.{ww} ⥤ Sheaf J AddCommGrpCat.{ww})
  (Ψa : Sheaf L AddCommGrpCat.{ww} ⥤ Sheaf K AddCommGrpCat.{ww})

/-- **The compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves composes.**
If the abelian sheaf underlying the inverse image of a module along `Ψ` is the image under `Ψa`
of the abelian sheaf underlying it, and likewise for `Φ` and `Φa`, then the same holds for the
composite `Ψ ⋙ Φ` and `Ψa ⋙ Φa`.

The two hypotheses are indexed by the sheaf of rings because the outer one is used at the inverse
image of the sheaf of rings along the inner functor. -/
def pullbackModuleToSheafIsoComp
    (hΦ : ∀ O : Sheaf K RingCat.{ww},
      pullbackModuleFunctor J Φ O ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ O) ≅
        SheafOfModules.toSheaf.{ww} O ⋙ Φa)
    (hΨ : ∀ R : Sheaf L RingCat.{ww},
      pullbackModuleFunctor K Ψ R ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf K Ψ R) ≅
        SheafOfModules.toSheaf.{ww} R ⋙ Ψa)
    (R : Sheaf L RingCat.{ww}) :
    pullbackModuleFunctor J (Ψ ⋙ Φ) R ⋙
        SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J (Ψ ⋙ Φ) R) ≅
      SheafOfModules.toSheaf.{ww} R ⋙ Ψa ⋙ Φa :=
  (Functor.isoWhiskerRight (pullbackModuleCompIso J K Φ Ψ R)
        (SheafOfModules.toSheaf.{ww}
          (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R)))).symm ≪≫
    Functor.isoWhiskerLeft (pullbackModuleFunctor K Ψ R) (hΦ (pullbackRingSheaf K Ψ R)) ≪≫
    Functor.isoWhiskerRight (hΨ R) Φa

end Comp

section Inverse

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf J RingCat.{ww})

/-- The identity case of `Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso`: the abelian
sheaf underlying the inverse image of a module along the identity functor of a sheaf category is
the abelian sheaf underlying the module.

Restriction along the identity functor of the site *is* the identity functor, at both coefficient
categories, so this is the restriction statement at `G = 𝟭`. -/
def pullbackModuleIdToSheafIso :
    pullbackModuleFunctor J (𝟭 (Sheaf J (Type ww))) O ⋙
        SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J (𝟭 (Sheaf J (Type ww))) O) ≅
      SheafOfModules.toSheaf.{ww} O :=
  pullbackModuleCompToSheafIso J J (𝟭 C) O (𝟭 (Sheaf J (Type ww))) (Iso.refl _) ≪≫
    Functor.rightUnitor _

section Section

variable (Φ : Sheaf J (Type ww) ⥤ Sheaf K (Type ww)) [PreservesFiniteProducts Φ]

/-- **The compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves for a
section of a restriction functor, whiskered by that restriction.**  Let `G` be a continuous
functor of sites and `Φ` a finite-product-preserving functor of sheaves of sets in the opposite
direction whose composite with restriction along `G` is the identity.  Then the abelian sheaf
underlying the inverse image of a module along `Φ`, restricted along `G`, is the abelian sheaf
underlying the module.

The restriction case turns the outer factor into an inverse image of modules,
`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso` merges the two inverse images into one along
`Φ ⋙ G.sheafPushforwardContinuous`, and `ε` identifies that composite with the identity, where
`Stacks.Sheaves.ToposPullback.pullbackModuleIdToSheafIso` finishes. -/
def pullbackModuleSectionToSheafIso
    (ε : Φ ⋙ G.sheafPushforwardContinuous (Type ww) J K ≅ 𝟭 (Sheaf J (Type ww))) :
    pullbackModuleFunctor K Φ O ⋙
        SheafOfModules.toSheaf.{ww} (pullbackRingSheaf K Φ O) ⋙
          G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K ≅
      SheafOfModules.toSheaf.{ww} O :=
  Functor.isoWhiskerLeft (pullbackModuleFunctor K Φ O)
      (pullbackModuleCompToSheafIso J K G (pullbackRingSheaf K Φ O)
        (G.sheafPushforwardContinuous (Type ww) J K) (Iso.refl _)).symm ≪≫
    (Functor.associator (pullbackModuleFunctor K Φ O)
      (pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K)
        (pullbackRingSheaf K Φ O))
      (SheafOfModules.toSheaf.{ww}
        (pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K)
          (pullbackRingSheaf K Φ O)))).symm ≪≫
    Functor.isoWhiskerRight
      (pullbackModuleCompIso J K (G.sheafPushforwardContinuous (Type ww) J K) Φ O)
      (SheafOfModules.toSheaf.{ww}
        (pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K)
          (pullbackRingSheaf K Φ O))) ≪≫
    compRestrictScalarsToSheafIso
      (pullbackModuleFunctor J (Φ ⋙ G.sheafPushforwardContinuous (Type ww) J K) O)
      (pullbackRingSheafCompIso J K (G.sheafPushforwardContinuous (Type ww) J K) Φ O).hom ≪≫
    Functor.isoWhiskerRight
      (pullbackModuleFunctorIsoOfNatIso J O ε (pullbackRingSheafMapOfNatTrans J O ε.hom)
        (ringSheafMap_pullbackRingSheafMapOfNatTrans J O ε.hom))
      (SheafOfModules.toSheaf.{ww}
        (pullbackRingSheaf J (Φ ⋙ G.sheafPushforwardContinuous (Type ww) J K) O)) ≪≫
    compRestrictScalarsToSheafIso
      (pullbackModuleFunctor J (𝟭 (Sheaf J (Type ww))) O)
      (pullbackRingSheafMapOfNatTrans J O ε.hom) ≪≫
    pullbackModuleIdToSheafIso J O

end Section

/-- Transposing a comparison across the equivalence of abelian sheaf categories induced by `G`:
a functor whose composite with the restriction is the abelian sheaf underlying a module is the
abelian sheaf underlying the module read through the inverse of the equivalence.

This is the unit of the equivalence, and it is stated with the comparing functor free so that the
chain is checked once, at an abstract functor. -/
def toSheafIsoInvOfCompIso [(G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K).IsEquivalence]
    {𝒜 : Type uu''} [Category.{vv''} 𝒜] (A : 𝒜 ⥤ Sheaf K AddCommGrpCat.{ww})
    (T : 𝒜 ⥤ Sheaf J AddCommGrpCat.{ww})
    (h : A ⋙ G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K ≅ T) :
    A ≅ T ⋙ (G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K).inv :=
  (Functor.rightUnitor A).symm ≪≫
    Functor.isoWhiskerLeft A
      (G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K).asEquivalence.unitIso ≪≫
    Functor.isoWhiskerRight h
      (G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K).inv

/-- **The compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves, for the
inverse of an equivalence.**  Let `G` be a continuous functor of sites whose restriction functor
is an equivalence of sheaf categories at both sets and abelian groups — the comparison of
Stacks 03G1 is such a functor.  Then the abelian sheaf underlying the inverse image of a module
along the *inverse* of that equivalence is the image, under the inverse of the abelian
equivalence, of the abelian sheaf underlying the module.

The isomorphism is obtained by composing with the equivalence, not by inverting:
`Stacks.Sheaves.ToposPullback.pullbackModuleSectionToSheafIso` at the counit of the equivalence
is the statement whiskered by the restriction functor, and
`Stacks.Sheaves.ToposPullback.toSheafIsoInvOfCompIso` puts the inverse back. -/
def pullbackModuleInverseToSheafIso
    [(G.sheafPushforwardContinuous (Type ww) J K).IsEquivalence]
    [(G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K).IsEquivalence] :
    pullbackModuleFunctor K (G.sheafPushforwardContinuous (Type ww) J K).inv O ⋙
        SheafOfModules.toSheaf.{ww}
          (pullbackRingSheaf K (G.sheafPushforwardContinuous (Type ww) J K).inv O) ≅
      SheafOfModules.toSheaf.{ww} O ⋙
        (G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K).inv :=
  toSheafIsoInvOfCompIso J K G _ _
    (pullbackModuleSectionToSheafIso J K G O
      (G.sheafPushforwardContinuous (Type ww) J K).inv
      (G.sheafPushforwardContinuous (Type ww) J K).asEquivalence.counitIso)

end Inverse

end Stacks.Sheaves.ToposPullback

end
