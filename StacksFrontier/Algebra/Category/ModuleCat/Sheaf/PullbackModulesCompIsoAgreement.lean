module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep1CompositionLaw
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardIsoSections
public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# The two compositors of Stacks 03D8 agree

Stacks 03D8 asserts that the pullback of sheaves of modules is pseudo-functorial,
`(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*`, and the draft carries **two** constructions of that comparison, built
from the two presentations of the adjunction of Stacks 03D7:

* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`, built from the adjunction for the
  *two-field* morphism of ringed topoi of Stacks 01D3 part (2). This is the one the simplicial
  development consumes: `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition` is its
  inverse followed by the 2-morphism's transformation of pullbacks.
* `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso`, built from the adjunction for the
  *four-field* morphism of ringed topoi, which is what the chain of bijections of Tag 03EL is
  stated at. `Stacks.SheafOfModules.pullbackModulesCompAdjIso` is that comparison at the
  identity comparison `Stacks.SheafOfModules.compPushforwardToposIso` of the geometric direct
  images, and the six composition-law lemmas of the 03EL chain are stated at it.

The two have the same type — the two-field pullback functor *is* the four-field one at
`AlgebraicGeometry.RingedToposHom.toModulesHom`, by definition — but nothing said they are the
same isomorphism, so a consumer holding one of them could not use a law stated at the other.
This file closes that gap.

## Main results

* `Stacks.SheafOfModules.pullbackModulesCompAdjIso_eq`: **the two compositors of Stacks 03D8
  agree**, as isomorphisms of functors and unconditionally.
* `Stacks.SheafOfModules.pullbackModulesCompAdjIso_hom`,
  `Stacks.SheafOfModules.pullbackModulesCompAdjIso_inv`: the same for the two transformations,
  which is the form `moduleFiberTransition` consumes.
* `Stacks.SheafOfModules.pullbackModulesCompAdjIso_hom_app`,
  `Stacks.SheafOfModules.pullbackModulesCompAdjIso_inv_app`: the same at a sheaf of modules,
  which is the form the composition laws of the 03EL chain consume.

## Implementation notes

*Why there is anything to prove.* Both comparisons are
`CategoryTheory.Adjunction.leftAdjointUniq` of the adjunction for the composite — transported
along the comparison of the direct images — against the composite of the two adjunctions. But
the two pairs of adjunctions are different: the two-field adjunction
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is the four-field one with its
right adjoint read through `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`, and the
two comparisons of direct images are likewise two different natural isomorphisms between two
different pairs of functors. So the two `leftAdjointUniq`s are taken at two genuinely different
pairs of adjunctions and have to be compared.

*The shape of the comparison.* Transporting the right adjoint of each factor of a composite of
adjunctions is transporting the composite along the whiskered isomorphism
(`CategoryTheory.Adjunction.comp_ofNatIsoRight_left` and `.comp_ofNatIsoRight_right`), and two
successive transports are one (`CategoryTheory.Adjunction.ofNatIsoRight_trans`). So both pairs
of adjunctions are one pair, with each member transported along one and the same isomorphism
`σ` of right adjoints — provided the two comparisons of direct images are compatible with `σ`,
which is `pushforwardModulesCompIso_symm_trans_whiskerIso` below. And transporting both
adjunctions of a `leftAdjointUniq` along one isomorphism does not change it
(`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_congr`).

*Where the mathematics is.* Entirely in the compatibility of the two comparisons of direct
images, and there it is immediate: every one of the four natural transformations involved is the
identity on underlying sheaves of sets — the comparison of the two direct images by
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id`, the
two-field comparison of direct images along a composite because `MorphismOfTopoi.comp` composes
the direct images on the nose, and the four-field one because the comparison `τ` it is taken at
is `Stacks.SheafOfModules.compPushforwardToposIso`, which is `Iso.refl`. A morphism of sheaves
of modules is determined by the underlying morphism of sheaves of sets
(`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`), so the compatibility holds.

*Why the two sides are spelled through `Eq.refl` first.* Each comparison is two or four
definitional unfoldings away from the `leftAdjointUniq` term the general lemmas apply to, and
discharging them inside the rewrite chain is what exceeds the elaborator's limits on terms this
deep; each is therefore discharged separately into a hypothesis, as in the composition law for
step 1 of the 03EL chain.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

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
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The compatibility of the two comparisons of direct images along a composite, at a single
sheaf of modules: all four transformations are the identity on underlying sheaves of sets, so
the two routes from the four-field `ψ_*(φ_*M)` to the two-field `(ψ ∘ φ)_*M` agree. -/
private theorem pushforwardModulesCompIso_symm_trans_whiskerIso_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
            (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)).inv.app M ≫
        (pushforwardModules ψ.toModulesHom).map (φ.toModulesPushforwardIso.hom.app M) ≫
          ψ.toModulesPushforwardIso.hom.app
            ((AlgebraicGeometry.RingedToposHom.pushforwardModules φ).obj M) =
      (ψ.comp φ).toModulesPushforwardIso.hom.app M ≫
        (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso φ ψ).hom.app M := by
  have hfour : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
          (compPushforwardToposIso φ ψ)
          (compPushforwardToposIso_fSharpSet φ ψ)).inv.app M) =
      (compPushforwardToposIso φ ψ).inv.app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :=
    moduleSheafFunctor_map_pushforwardModulesCompInv φ.toModulesHom ψ.toModulesHom
      (ψ.comp φ).toModulesHom M (compPushforwardToposIso φ ψ)
      (compPushforwardToposIso_fSharpSet φ ψ)
  have hwhisker : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((pushforwardModules ψ.toModulesHom).map (φ.toModulesPushforwardIso.hom.app M)) =
      CategoryStruct.id (ψ.toModulesHom.toToposHom.pushforward.obj
        (φ.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) :=
    (moduleSheafFunctor_map_pushforwardModules_map ψ.toModulesHom
        (φ.toModulesPushforwardIso.hom.app M)).trans
      ((congrArg ψ.toModulesHom.toToposHom.pushforward.map
      (AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id
        φ M)).trans
        (CategoryTheory.Functor.map_id ψ.toModulesHom.toToposHom.pushforward
          (φ.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))))
  have htwo : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso φ ψ).hom.app M) =
    CategoryStruct.id (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      ((AlgebraicGeometry.RingedToposHom.pushforwardModules (ψ.comp φ)).obj M)) := rfl
  refine hom_ext_moduleSheafFunctor ?_
  simp only [CategoryTheory.Functor.map_comp, hfour, hwhisker, htwo,
    AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id]
  exact Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The two comparisons of direct images along a composite are compatible with the comparison
of the two direct images.** Reading the four-field comparison `ψ_*(φ_*-) ≅ (ψ ∘ φ)_*-` backwards
and then passing to the two-field direct images factor by factor is passing to the two-field
direct image of the composite and then reading the two-field comparison forwards.

This is the whole mathematical content of the agreement of the two compositors of Stacks 03D8;
it is `pushforwardModulesCompIso_symm_trans_whiskerIso_app` at every sheaf of modules. -/
private theorem pushforwardModulesCompIso_symm_trans_whiskerIso :
    (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
          (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)).symm ≪≫
        (Functor.isoWhiskerRight φ.toModulesPushforwardIso
            (pushforwardModules ψ.toModulesHom) ≪≫
          Functor.isoWhiskerLeft (AlgebraicGeometry.RingedToposHom.pushforwardModules φ)
            ψ.toModulesPushforwardIso) =
      (ψ.comp φ).toModulesPushforwardIso ≪≫
        AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso φ ψ :=
  Iso.ext (NatTrans.ext (funext fun M ↦ by
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    exact pushforwardModulesCompIso_symm_trans_whiskerIso_app φ ψ M))

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Transporting the right adjoint of each factor of the composite of the two four-field
adjunctions of Stacks 03D7 is transporting the composite along the whiskered isomorphism. -/
private theorem comp_ofNatIsoRight_toModulesPushforwardIso :
    ((pullbackAdjPushforwardModules ψ.toModulesHom).ofNatIsoRight
          ψ.toModulesPushforwardIso).comp
        ((pullbackAdjPushforwardModules φ.toModulesHom).ofNatIsoRight
          φ.toModulesPushforwardIso) =
      ((pullbackAdjPushforwardModules ψ.toModulesHom).comp
          (pullbackAdjPushforwardModules φ.toModulesHom)).ofNatIsoRight
        (Functor.isoWhiskerRight φ.toModulesPushforwardIso
            (pushforwardModules ψ.toModulesHom) ≪≫
          Functor.isoWhiskerLeft (AlgebraicGeometry.RingedToposHom.pushforwardModules φ)
            ψ.toModulesPushforwardIso) := by
  rw [Adjunction.comp_ofNatIsoRight_left, Adjunction.comp_ofNatIsoRight_right,
    Adjunction.ofNatIsoRight_trans]

omit [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The adjunction the two-field compositor of Stacks 03D8 is `leftAdjointUniq` of, written as
the four-field adjunction for the composite transported along the four-field comparison of
direct images and then along the whiskered comparison of the two direct images. -/
private theorem ofNatIsoRight_pushforwardModulesCompIso_eq :
    ((pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom).ofNatIsoRight
          (ψ.comp φ).toModulesPushforwardIso).ofNatIsoRight
        (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso φ ψ) =
      ((pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom).ofNatIsoRight
          (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
            (compPushforwardToposIso φ ψ)
            (compPushforwardToposIso_fSharpSet φ ψ)).symm).ofNatIsoRight
        (Functor.isoWhiskerRight φ.toModulesPushforwardIso
            (pushforwardModules ψ.toModulesHom) ≪≫
          Functor.isoWhiskerLeft (AlgebraicGeometry.RingedToposHom.pushforwardModules φ)
            ψ.toModulesPushforwardIso) := by
  rw [Adjunction.ofNatIsoRight_trans, Adjunction.ofNatIsoRight_trans,
    pushforwardModulesCompIso_symm_trans_whiskerIso]

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The two compositors of Stacks 03D8 agree.** The comparison
`(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of sheaves of modules built from the adjunction of
Stacks 03D7 for the *four-field* morphism of ringed topoi — the comparison the chain of
bijections of Tag 03EL and its six composition laws are stated at — is the comparison
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` built from the adjunction for the
*two-field* morphism of ringed topoi of Stacks 01D3 part (2), which is what the simplicial
development consumes. The two have the same type, the two-field pullback being the four-field
one at `AlgebraicGeometry.RingedToposHom.toModulesHom` by definition.

No hypothesis is needed: the two agree for every pair of composable morphisms of ringed
topoi. -/
theorem pullbackModulesCompAdjIso_eq :
    pullbackModulesCompAdjIso φ ψ =
      AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso φ ψ := by
  have hfour : pullbackModulesCompAdjIso φ ψ =
      Adjunction.leftAdjointUniq
        ((pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom).ofNatIsoRight
          (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
            (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)).symm)
        ((pullbackAdjPushforwardModules ψ.toModulesHom).comp
          (pullbackAdjPushforwardModules φ.toModulesHom)) := rfl
  have htwo : AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso φ ψ =
      Adjunction.leftAdjointUniq
        (((pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom).ofNatIsoRight
            (ψ.comp φ).toModulesPushforwardIso).ofNatIsoRight
          (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso φ ψ))
        (((pullbackAdjPushforwardModules ψ.toModulesHom).ofNatIsoRight
            ψ.toModulesPushforwardIso).comp
          ((pullbackAdjPushforwardModules φ.toModulesHom).ofNatIsoRight
            φ.toModulesPushforwardIso)) := rfl
  rw [hfour, htwo, ofNatIsoRight_pushforwardModulesCompIso_eq,
    comp_ofNatIsoRight_toModulesPushforwardIso,
    Adjunction.leftAdjointUniq_ofNatIsoRight_congr]

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The two compositors of Stacks 03D8 agree**, read on the transformation
`(ψ ∘ φ)^* ⟶ ψ^* ⋙ φ^*`. -/
theorem pullbackModulesCompAdjIso_hom :
    (pullbackModulesCompAdjIso φ ψ).hom =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso φ ψ).hom :=
  congrArg Iso.hom (pullbackModulesCompAdjIso_eq φ ψ)

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The two compositors of Stacks 03D8 agree**, read on the transformation
`ψ^* ⋙ φ^* ⟶ (ψ ∘ φ)^*`. This is the form
`CategoryTheory.SimplicialSiteSituation.moduleFiberTransition` consumes. -/
theorem pullbackModulesCompAdjIso_inv :
    (pullbackModulesCompAdjIso φ ψ).inv =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso φ ψ).inv :=
  congrArg Iso.inv (pullbackModulesCompAdjIso_eq φ ψ)

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The two compositors of Stacks 03D8 agree**, at a sheaf of modules. -/
theorem pullbackModulesCompAdjIso_hom_app
    (G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (pullbackModulesCompAdjIso φ ψ).hom.app G =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso φ ψ).hom.app G :=
  congrArg (fun α ↦ α.app G) (pullbackModulesCompAdjIso_hom φ ψ)

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The two compositors of Stacks 03D8 agree**, at a sheaf of modules, read backwards. This is
the form the composition laws of the chain of Tag 03EL consume. -/
theorem pullbackModulesCompAdjIso_inv_app
    (G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (pullbackModulesCompAdjIso φ ψ).inv.app G =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso φ ψ).inv.app G :=
  congrArg (fun α ↦ α.app G) (pullbackModulesCompAdjIso_inv φ ψ)

end Stacks.SheafOfModules

end
