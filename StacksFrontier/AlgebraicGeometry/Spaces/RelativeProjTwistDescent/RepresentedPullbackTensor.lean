module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PullbackTensorTransportComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackGood

/-!
# The square of ringed topoi of a morphism of representable algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` and `φ` the morphism of
representable algebraic spaces `yoneda.obj T' ⟶ yoneda.obj T` it represents.  The small étale
ringed topos of `yoneda.obj U` is identified with that of the scheme underlying `U` by the
comparison of Stacks 04M0, and the module functor of that identification is the pullback of
modules along a morphism of ringed topoi, the reindexing of
`Stacks.SheafOfModules.reindexRingedToposModulesHom`.  So the square

```
  (yoneda T')_étale ---- φ ----> (yoneda T)_étale
        |                              |
     reindex                        reindex
        v                              v
     T'_étale ---- base change g ---> T_étale
```

has four sides that are morphisms of ringed topoi in the shape the comparison of Stacks 03EL
consumes.  This file records the four sides, takes the composite of the lower route as the
diagonal, and identifies the geometric direct image of the upper route with that of the diagonal.

## Main definitions

* `AlgebraicGeometry.Space.representedReindexHom`: the reindexing of the small étale ringed topos
  of the scheme underlying `U` to that of `yoneda.obj U`, as a morphism of ringed topoi.
* `AlgebraicGeometry.Space.representedSchemeBaseChangeHom`: small étale base change of schemes
  along `g`, as a morphism of ringed topoi
  (`AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom`).
* `AlgebraicGeometry.Space.representedSquareHom`: the diagonal of the square, the composite of
  the reindexing of `T'` with base change along `g`.
* `AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`: the square of site functors,
  `e_T⁻¹ ⋙ (chart base change along φ) ≅ (base change along g) ⋙ e_{T'}⁻¹`, conjugated from
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`.
* `AlgebraicGeometry.Space.representedSquareDirectImageIso`: **the geometric direct images of the
  two routes agree**, `φ_* ⋙ (reindex_T)_* ≅ (diagonal)_*` on sheaves of sets.

* `Stacks.SheafOfModules.factorizationPullbackIso`: for a morphism of ringed topoi with two
  factorizations, the comparison of the two composite pullbacks read off the comparisons of
  pullbacks of the factorizations.
* `AlgebraicGeometry.Space.representedSquareModulePullbackIso`: at the square of `g`,
  `(base change along g) ⋙ E_{T'} ≅ E_T ⋙ φ^*` on sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.fSharpSetComp_representedSquareDirectImageIso`: that comparison of
  direct images carries the composite structure map of the upper route to the structure map of the
  diagonal.
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso`: the
  transported comparisons of Stacks 03EL along two factorizations agree through
  `factorizationPullbackIso`.
* `AlgebraicGeometry.Space.representedSquare_pullbackTensorIsoTransport`: **Stacks 03EL is
  compatible with the square of `g`**: through `representedSquareModulePullbackIso`, the 03EL of
  base change of schemes read on `yoneda.obj T'` is the 03EL of the inverse image along `φ` after
  the comparison of Stacks 04M0 for `T`.

## Implementation notes

The composite `Stacks.Sheaves.RingedToposModules.RingedToposHom.comp` is applied by its full name
(inside `AlgebraicGeometry` the short name is `AlgebraicGeometry.RingedToposHom.comp`) and with its
universes given explicitly: left to unification they are fixed at `0` before the arguments are
seen, and the elaboration fails.

The direct image of `φ` is that of Stacks 03G8, built through the comparison equivalence of
Stacks 03G1; it is identified with restriction along chart base change by
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` and `AlgebraicGeometry.Space.chartRanIso`,
which is the identification the structure map of Stacks 03G8 is compared along in
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`.

The two continuity instances below restate, for the projection `.J` of the small étale ringed
site of a scheme, continuity facts known for the topology itself; the direct images of the
morphisms of ringed topoi are stated at the projections and instance search does not unfold them.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

universe u

namespace Stacks.SheafOfModules

universe wX vX uX wZ vZ uZ wA vA uA wB vB uB

/-- The comparison of two factorizations read off two comparisons of pullbacks `c₁, c₂` and the
identifications `α`, followed by the identifications, is the second comparison. -/
private theorem comp_factorizationIso_hom_app {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁]
    [Category 𝒴₂] [Category 𝒳] {χs : 𝒵 ⥤ 𝒳} {ψ₁s Lψ₁ : 𝒵 ⥤ 𝒴₁} {φ₁s Lφ₁ : 𝒴₁ ⥤ 𝒳}
    {ψ₂s Lψ₂ : 𝒵 ⥤ 𝒴₂} {φ₂s : 𝒴₂ ⥤ 𝒳} (c₁ : χs ≅ ψ₁s ⋙ φ₁s) (c₂ : χs ≅ ψ₂s ⋙ φ₂s)
    (αψ₁ : ψ₁s ≅ Lψ₁) (αφ₁ : φ₁s ≅ Lφ₁) (αψ₂ : ψ₂s ≅ Lψ₂) (M : 𝒵) :
    c₁.hom.app M ≫ φ₁s.map (αψ₁.hom.app M) ≫ αφ₁.hom.app (Lψ₁.obj M) ≫
        (Functor.isoWhiskerLeft Lψ₁ αφ₁.symm ≪≫ Functor.isoWhiskerRight αψ₁.symm φ₁s ≪≫
          c₁.symm ≪≫ c₂ ≪≫ Functor.isoWhiskerRight αψ₂ φ₂s).hom.app M =
      c₂.hom.app M ≫ φ₂s.map (αψ₂.hom.app M) ≫ (Iso.refl φ₂s).hom.app (Lψ₂.obj M) := by
  simp [← Functor.map_comp_assoc]

variable {X : AlgebraicGeometry.RingedTopos.{vX, uX, wX}}
    {Z : AlgebraicGeometry.RingedTopos.{vZ, uZ, wZ}}
    {Y₁ : AlgebraicGeometry.RingedTopos.{vA, uA, wA}}
    {Y₂ : AlgebraicGeometry.RingedTopos.{vB, uB, wB}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wX} RingCat.{wX})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{wZ} RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [X.J.HasSheafCompose (forget RingCat.{wX})] [Z.J.HasSheafCompose (forget RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget RingCat.{wA})] [Y₂.J.HasSheafCompose (forget RingCat.{wB})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wX})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{wA})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [HasWeakSheafify X.J AddCommGrpCat.{wX}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wX}]
  [HasWeakSheafify Z.J AddCommGrpCat.{wZ}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{wZ}]
  [HasWeakSheafify Y₁.J AddCommGrpCat.{wA}] [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{wA}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{wB}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  (φ₁ : RingedToposHom X Y₁) (ψ₁ : RingedToposHom Y₁ Z)
  (φ₂ : RingedToposHom X Y₂) (ψ₂ : RingedToposHom Y₂ Z) (χ : RingedToposHom X Z)
  (τ₁ : φ₁.toToposHom.pushforward ⋙ ψ₁.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₁ : fSharpSetComp φ₁ ψ₁ ≫
    τ₁.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  (τ₂ : φ₂.toToposHom.pushforward ⋙ ψ₂.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₂ : fSharpSetComp φ₂ ψ₂ ≫
    τ₂.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  {Lφ₁ : _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O) ⥤
    _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
  {Lψ₁ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O)}
  {Lψ₂ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O)}
  (αφ₁ : φ₁.pullbackModules ≅ Lφ₁) (αψ₁ : ψ₁.pullbackModules ≅ Lψ₁) (αψ₂ : ψ₂.pullbackModules ≅ Lψ₂)

/-- The comparison of two factorizations of a morphism of ringed topoi `χ`, through `φ₁, ψ₁` and
through `φ₂, ψ₂`, on the functors `L` identified with the pullbacks by the isomorphisms `α`: the
comparison of pullbacks `χ^* ≅ ψ₁^* ⋙ φ₁^*` read backwards through `α_φ₁, α_ψ₁`, followed by the
comparison `χ^* ≅ ψ₂^* ⋙ φ₂^*` read through `α_ψ₂`. -/
noncomputable def factorizationPullbackIso : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ φ₂.pullbackModules :=
  Functor.isoWhiskerLeft Lψ₁ αφ₁.symm ≪≫ Functor.isoWhiskerRight αψ₁.symm φ₁.pullbackModules ≪≫
    (pullbackModulesCompIso φ₁ ψ₁ χ τ₁ hτ₁).symm ≪≫ pullbackModulesCompIso φ₂ ψ₂ χ τ₂ hτ₂ ≪≫
    Functor.isoWhiskerRight αψ₂ φ₂.pullbackModules

/-- **The transported comparisons of Stacks 03EL along two factorizations agree through the
comparison of the factorizations.**  This is
`Stacks.SheafOfModules.pullbackTensorIsoTransport_square` at
`Stacks.SheafOfModules.factorizationPullbackIso`, which corresponds to the two comparisons of
pullbacks by construction. -/
theorem pullbackTensorIsoTransport_square_factorizationPullbackIso
    (F G : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O)) :
    Lφ₁.map (pullbackTensorIsoTransport ψ₁ αψ₁ F G).hom ≫
        (pullbackTensorIsoTransport φ₁ αφ₁ (Lψ₁.obj F) (Lψ₁.obj G)).hom ≫
          ((Tensor.sheafTensor X.O).map
            ((factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂).hom.app F)).app
              (Lφ₁.obj (Lψ₁.obj G)) ≫
            ((Tensor.sheafTensor X.O).obj (φ₂.pullbackModules.obj (Lψ₂.obj F))).map
              ((factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂).hom.app G) =
      (factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂).hom.app
          (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        φ₂.pullbackModules.map (pullbackTensorIsoTransport ψ₂ αψ₂ F G).hom ≫
          (pullbackTensorIsoTransport φ₂ (Iso.refl _) (Lψ₂.obj F) (Lψ₂.obj G)).hom :=
  pullbackTensorIsoTransport_square φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ (Iso.refl _) αψ₂
    (factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂)
    (fun M => comp_factorizationIso_hom_app (pullbackModulesCompIso φ₁ ψ₁ χ τ₁ hτ₁)
      (pullbackModulesCompIso φ₂ ψ₂ χ τ₂ hτ₂) αψ₁ αφ₁ αψ₂ M) F G

/-- `Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso` with the
components of the comparison of the factorizations replaced by any description `f` of them. -/
theorem pullbackTensorIsoTransport_square_factorizationPullbackIso_of_app
    (f : ∀ F : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O),
      Lφ₁.obj (Lψ₁.obj F) ⟶ φ₂.pullbackModules.obj (Lψ₂.obj F))
    (hf : ∀ F, (factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂).hom.app F = f F)
    (F G : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O)) :
    Lφ₁.map (pullbackTensorIsoTransport ψ₁ αψ₁ F G).hom ≫
        (pullbackTensorIsoTransport φ₁ αφ₁ (Lψ₁.obj F) (Lψ₁.obj G)).hom ≫
          ((Tensor.sheafTensor X.O).map (f F)).app (Lφ₁.obj (Lψ₁.obj G)) ≫
            ((Tensor.sheafTensor X.O).obj (φ₂.pullbackModules.obj (Lψ₂.obj F))).map (f G) =
      f (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        φ₂.pullbackModules.map (pullbackTensorIsoTransport ψ₂ αψ₂ F G).hom ≫
          (pullbackTensorIsoTransport φ₂ (Iso.refl _) (Lψ₂.obj F) (Lψ₂.obj G)).hom := by
  have h := pullbackTensorIsoTransport_square_factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂
    hτ₂ αφ₁ αψ₁ αψ₂ F G
  rw [hf F, hf G, hf] at h
  exact h

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The reindexing of the small étale ringed topos of the scheme underlying `U` to the small étale
ringed topos of the representable algebraic space `yoneda.obj U`, along the comparison of Stacks
04M0, as a morphism of ringed topoi.  Its pullback of modules is the functor of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, by
`Stacks.SheafOfModules.pullbackModulesReindexIso`. -/
abbrev representedReindexHom (U : BigFppfOver B S hS) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
        U.left.property).toRingedTopos :=
  Stacks.SheafOfModules.reindexRingedToposModulesHom (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U) (representedSchemeCommRingStructureSheaf B S hS U)

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- Small étale base change of schemes along the morphism underlying `g`, as a morphism of ringed
topoi.  Its pullback of modules is
`SheafOfModules.pullback (AlgebraicGeometry.Space.representedSchemeStructureMapRing B S hS g)`, by
`AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso`. -/
abbrev representedSchemeBaseChangeHom :=
  _root_.AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom (associatedBigEtaleSite B)
    g.left

/-- The diagonal of the square of ringed topoi of `g`: the reindexing of `T'` followed by small
étale base change of schemes along `g`. -/
abbrev representedSquareHom :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.comp.{u, u, u + 1, u, u + 1, u, u + 1}
    (representedSchemeBaseChangeHom B S hS g) (representedReindexHom B S hS T')

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

/-- **The square of site functors of `g`, read with the inverses of the comparisons of Stacks
04M0.**  Passing from an étale scheme over `T` to the étale chart of `yoneda.obj T` it is, and base
changing that chart along `φ`, is base changing the scheme along `g` and passing to the étale chart
of `yoneda.obj T'`.

This is `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, stated with the functors of
the comparisons, conjugated by the unit and counit of the two comparison equivalences. -/
def representedEquivInverseBaseChangeIso :
    (representedSmallEtaleEquivalence B S hS T).inverse ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS g) hg ≅
      representedSchemeBaseChange B S hS g ⋙ (representedSmallEtaleEquivalence B S hS T').inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (representedSmallEtaleEquivalence B S hS T').unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (representedSmallEtaleBaseChangeIso B S hS g hg) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (representedSmallEtaleEquivalence B S hS T).counitIso _ ≪≫
      Functor.leftUnitor _) _

/-- Base change of schemes along `g` followed by the inverse of the comparison of Stacks 04M0 for
`T'` is a continuous functor. -/
instance isContinuous_representedSchemeBaseChange_comp_inverse :
    (representedSchemeBaseChange B S hS g ⋙
        (representedSmallEtaleEquivalence B S hS T').inverse).IsContinuous
      (representedSchemeSmallEtaleTopology B S hS T)
      (SmallEtale.topology B S hS (yoneda.obj T')) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_representedSchemeBaseChange B S hS g) inferInstance

/-- Base change of schemes along `g` is continuous, with the topologies spelled as the projections
of the ringed sites the direct images of `representedReindexHom` and
`representedSchemeBaseChangeHom` are stated at. -/
instance isContinuous_representedSchemeBaseChange_ringedSite :
    (representedSchemeBaseChange B S hS g).IsContinuous
      (Stacks.SheafOfModules.siteRingedSite (representedSchemeSmallEtaleTopology B S hS T)
        (representedSchemeCommRingStructureSheaf B S hS T)).J
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
        T'.left.property).J :=
  isContinuous_representedSchemeBaseChange B S hS g

/-- The inverse of the comparison of Stacks 04M0 is continuous, with the topology of the scheme
spelled as the projection of its small étale ringed site. -/
instance isContinuous_representedSmallEtaleEquivalence_inverse_ringedSite
    (U : BigFppfOver B S hS) :
    (representedSmallEtaleEquivalence B S hS U).inverse.IsContinuous
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
        U.left.property).J
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS U).inverse.IsContinuous
    (representedSchemeSmallEtaleTopology B S hS U) (SmallEtale.topology B S hS (yoneda.obj U)))

/-- **The geometric direct images of the two routes round the square of `g` agree.**  On sheaves
of sets on the small étale site of `yoneda.obj T'`, the direct image of Stacks 03G8 along `φ`
followed by reindexing to the scheme `T` is reindexing to the scheme `T'` followed by the direct
image along base change of schemes, which is the direct image of
`AlgebraicGeometry.Space.representedSquareHom`.

The direct image along `φ` is restriction along chart base change
(`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso`, `AlgebraicGeometry.Space.chartRanIso`),
and the two composite site functors agree by
`AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`.  This is the comparison `τ` of
direct images that the comparison `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` of
pullbacks along the upper route is taken at. -/
def representedSquareDirectImageIso :
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)).toToposHom.pushforward ⋙
        (representedReindexHom B S hS T).toToposHom.pushforward ≅
      (representedSquareHom B S hS g).toToposHom.pushforward :=
  Functor.isoWhiskerRight (smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
      chartRanIso B S hS (representedSpaceMap B S hS g) hg) _ ≪≫
    Functor.sheafPushforwardContinuousComp' (representedEquivInverseBaseChangeIso B S hS g hg)
      _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

/-- On sections, the direct image under the reindexing of `T` of the structure map of `φ` is the
structure map of the two-field morphism of Stacks 03G8 over the chart `e_T⁻¹ W`. -/
private theorem pushforward_map_fSharpSet_apply
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ) (y) :
    (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
      ((representedReindexHom B S hS T).toToposHom.pushforward.map
      (fSharpSet (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)))) y =
      (Sheaf.sectionsFunctor _
        (Opposite.op ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop))).map
        ((AlgebraicGeometry.RingedTopos.forgetRing _).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).fSharp) y :=
    congrArg (fun f => (Sheaf.sectionsFunctor _ W).map
      ((representedReindexHom B S hS T).toToposHom.pushforward.map f) y)
      (AlgebraicGeometry.RingedToposHom.ringFsharp_forget
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))

/-- On sections over `W`, the comparison `representedSquareDirectImageIso` is the chart
comparison over `e_T⁻¹ W` followed by restriction along the inverse of
`representedEquivInverseBaseChangeIso`. -/
private theorem representedSquareDirectImageIso_hom_app_apply
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ) (z) :
    (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
      ((representedSquareDirectImageIso B S hS g hg).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))) z =
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)).obj.map
        ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W.unop).op
        ((Sheaf.sectionsFunctor _
        (Opposite.op ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop))).map
          ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
            chartRanIso B S hS (representedSpaceMap B S hS g) hg).hom.app
            (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS
                ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))) z) :=
  rfl

/-- On sections over a chart `V`, the structure map of Stacks 03G8 read through the chart
comparison is pullback of regular functions along base change of charts
(`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`). -/
private theorem chartRanIso_apply_fSharp (V : SmallEtale B S hS (yoneda.obj T)) (y) :
    (Sheaf.sectionsFunctor _ (Opposite.op V)).map
          ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
            chartRanIso B S hS (representedSpaceMap B S hS g) hg).hom.app
            (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)))
      ((Sheaf.sectionsFunctor _ (Opposite.op V)).map
        ((AlgebraicGeometry.RingedTopos.forgetRing _).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).fSharp) y) =
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg).hom.app
        (Opposite.op V) y := by
  have h := structureSharp_comp_chartRanIso B S hS (representedSpaceMap B S hS g) hg
  rw [← forgetCommRingSheaf_map_fSharp] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (·.hom) h) (Opposite.op V)) y

/-- On sections over a chart `V`, pullback along base change of charts is pullback along base
change of schemes followed by restriction along `representedSmallEtaleBaseChangeIso`
(`AlgebraicGeometry.Space.representedStructureMapRing_square`). -/
private theorem smallBaseChangeSharp_apply_eq (V : SmallEtale B S hS (yoneda.obj T))
    (x : (representedSchemeStructureSheaf B S hS T).obj.obj
      (Opposite.op ((representedSmallEtaleEquivalence B S hS T).functor.obj V))) :
    (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg).hom.app (Opposite.op V) x =
      (representedSchemeStructureSheaf B S hS T').obj.map
        ((representedSmallEtaleBaseChangeIso B S hS g hg).hom.app V).op
        ((representedSchemeStructureMapRing B S hS g).hom.app
          (Opposite.op ((representedSmallEtaleEquivalence B S hS T).functor.obj V)) x) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (·.hom) (representedStructureMapRing_square B S hS g hg)) (Opposite.op V)) x).symm

/-- For an isomorphism `r : F ⋙ e_C ≅ e_A ⋙ G` conjugated by two equivalences, as in
`AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`, the functor of `e_C` carries the
inverse of the conjugate, followed by `r` and `G` of the counit of `e_A`, to the counit of
`e_C`. -/
private theorem equivInverseConj_inv_app {A A' C C' : Type*} [Category A] [Category A']
    [Category C] [Category C'] (eA : A ≌ A') (eC : C ≌ C') (F : A ⥤ C) (G : A' ⥤ C')
    (r : F ⋙ eC.functor ≅ eA.functor ⋙ G) (W : A') :
    eC.functor.map (((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (eA.inverse ⋙ F) eC.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft eA.inverse r ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eA.counitIso G ≪≫
        Functor.leftUnitor _) eC.inverse).inv.app W) ≫
      r.hom.app (eA.inverse.obj W) ≫ G.map (eA.counit.app W) = eC.counit.app (G.obj W) := by
  simp

/-- The comparison functor of `T'` carries the inverse of `representedEquivInverseBaseChangeIso` at
`W`, followed by `representedSmallEtaleBaseChangeIso` and base change of the counit, to the
counit. -/
private theorem map_representedEquivInverseBaseChangeIso_inv_app
    (W : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    (representedSmallEtaleEquivalence B S hS T').functor.map
        ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W) ≫
      (representedSmallEtaleBaseChangeIso B S hS g hg).hom.app
        ((representedSmallEtaleEquivalence B S hS T).inverse.obj W) ≫
        (representedSchemeBaseChange B S hS g).map
          ((representedSmallEtaleEquivalence B S hS T).counit.app W) =
      (representedSmallEtaleEquivalence B S hS T').counit.app
        ((representedSchemeBaseChange B S hS g).obj W) :=
  equivInverseConj_inv_app _ _ _ _ _ W

/-- `map_representedEquivInverseBaseChangeIso_inv_app` read on regular functions. -/
private theorem restrict_representedEquivInverseBaseChangeIso_inv_app
    (W : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (z : (representedSchemeStructureSheaf B S hS T').obj.obj
      (Opposite.op ((representedSchemeBaseChange B S hS g).obj W))) :
    (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)).obj.map
        ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W).op
      ((representedSchemeStructureSheaf B S hS T').obj.map
        ((representedSmallEtaleBaseChangeIso B S hS g hg).hom.app
          ((representedSmallEtaleEquivalence B S hS T).inverse.obj W)).op
        ((representedSchemeStructureSheaf B S hS T').obj.map
          ((representedSchemeBaseChange B S hS g).map
            ((representedSmallEtaleEquivalence B S hS T).counit.app W)).op z)) =
      (representedSchemeStructureSheaf B S hS T').obj.map
        ((representedSmallEtaleEquivalence B S hS T').counit.app
          ((representedSchemeBaseChange B S hS g).obj W)).op z := by
  have hz := congrArg (fun k => (representedSchemeStructureSheaf B S hS T').obj.map k.op z)
    (map_representedEquivInverseBaseChangeIso_inv_app B S hS g hg W)
  simp only [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply] at hz
  exact hz

/-- On sections, the structure map of the reindexing of `U` is restriction along the counit. -/
private theorem fSharpSet_representedReindexHom_apply (U : BigFppfOver B S hS)
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ)
    (x : (representedSchemeStructureSheaf B S hS U).obj.obj W) :
    (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS U) W).map
        (fSharpSet (representedReindexHom B S hS U)) x =
      (representedSchemeStructureSheaf B S hS U).obj.map
        ((representedSmallEtaleEquivalence B S hS U).counit.app W.unop).op x :=
  congrArg (fun f => (Sheaf.sectionsFunctor _ W).map f x)
    (show fSharpSet (representedReindexHom B S hS U) = _ from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget.{u, u + 1, u, u, u + 1, u} _)

/-- On sections, the structure map of base change of schemes is
`representedSchemeStructureMapRing`. -/
private theorem fSharpSet_representedSchemeBaseChangeHom_apply
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ)
    (x : (representedSchemeStructureSheaf B S hS T).obj.obj W) :
    (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
        (fSharpSet (representedSchemeBaseChangeHom B S hS g)) x =
      (representedSchemeStructureMapRing B S hS g).hom.app W x :=
  congrArg (fun f => (Sheaf.sectionsFunctor _ W).map f x)
    (show fSharpSet (representedSchemeBaseChangeHom B S hS g) = _ from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget.{u, u + 1, u, u, u + 1, u} _)

/-- Naturality of `representedSchemeStructureMapRing` along the counit of the comparison for
`T`. -/
private theorem representedSchemeStructureMapRing_apply_counit
    (W : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (x : (representedSchemeStructureSheaf B S hS T).obj.obj (Opposite.op W)) :
    (representedSchemeStructureMapRing B S hS g).hom.app
        (Opposite.op ((representedSmallEtaleEquivalence B S hS T).functor.obj
          ((representedSmallEtaleEquivalence B S hS T).inverse.obj W)))
        ((representedSchemeStructureSheaf B S hS T).obj.map
          ((representedSmallEtaleEquivalence B S hS T).counit.app W).op x) =
      (representedSchemeStructureSheaf B S hS T').obj.map
        ((representedSchemeBaseChange B S hS g).map
          ((representedSmallEtaleEquivalence B S hS T).counit.app W)).op
        ((representedSchemeStructureMapRing B S hS g).hom.app (Opposite.op W) x) :=
  ConcreteCategory.congr_hom ((representedSchemeStructureMapRing B S hS g).hom.naturality
    ((representedSmallEtaleEquivalence B S hS T).counit.app W).op) x

/-- On sections, the composite structure map of the upper route of the square, read through
`representedSquareDirectImageIso`. -/
private theorem fSharpSetComp_representedSquareDirectImageIso_apply
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ)
    (x : (representedSchemeStructureSheaf B S hS T).obj.obj W) :
    (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
        (fSharpSetComp (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
          (representedReindexHom B S hS T) ≫
        (representedSquareDirectImageIso B S hS g hg).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))) x =
      (representedSchemeStructureSheaf B S hS T').obj.map
        ((representedSmallEtaleEquivalence B S hS T').counit.app
          ((representedSchemeBaseChange B S hS g).obj W.unop)).op
        ((representedSchemeStructureMapRing B S hS g).hom.app W x) :=
  (congrArg (fun w => (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
      ((representedSquareDirectImageIso B S hS g hg).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)))
      ((Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
        ((representedReindexHom B S hS T).toToposHom.pushforward.map
          (fSharpSet (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)))) w))
    (fSharpSet_representedReindexHom_apply B S hS T W x)).trans <|
  (congrArg (fun w => (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
      ((representedSquareDirectImageIso B S hS g hg).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))) w)
    (pushforward_map_fSharpSet_apply B S hS g W _)).trans <|
  (representedSquareDirectImageIso_hom_app_apply B S hS g hg W _).trans <|
  (congrArg ((Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)).obj.map
        ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W.unop).op)
    ((chartRanIso_apply_fSharp B S hS g hg _ _).trans
      ((smallBaseChangeSharp_apply_eq B S hS g hg _ _).trans
      (congrArg ((representedSchemeStructureSheaf B S hS T').obj.map
        ((representedSmallEtaleBaseChangeIso B S hS g hg).hom.app
          ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop)).op)
        (representedSchemeStructureMapRing_apply_counit B S hS g W.unop x))))).trans <|
  restrict_representedEquivInverseBaseChangeIso_inv_app B S hS g hg W.unop _

/-- **The comparison of direct images of the square of `g` carries the composite structure map of
the upper route to the structure map of the diagonal.**  The structure map of `φ` followed by the
direct image under the reindexing of `T` of the structure map of the reindexing, read through
`AlgebraicGeometry.Space.representedSquareDirectImageIso`, is the structure map of
`AlgebraicGeometry.Space.representedSquareHom`.  This is the hypothesis on the comparison `τ` of
direct images that `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` asks for.

Over an étale `W / T` both sides send a regular function to its pullback along the projection
`W ×_T T' ⟶ W`: the upper route through the structure map of Stacks 03G8 at the chart `e_T⁻¹ W`,
which is pullback along base change of charts
(`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`), and base change of charts is base
change of schemes up to `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`
(`AlgebraicGeometry.Space.representedStructureMapRing_square`). -/
theorem fSharpSetComp_representedSquareDirectImageIso :
    fSharpSetComp (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) ≫
      (representedSquareDirectImageIso B S hS g hg).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)) =
      fSharpSet (representedSquareHom B S hS g) := by
  refine Eq.trans ?_ (RingedToposHom.fSharpSetComp_comp.{u, u, u + 1, u, u + 1, u, u + 1}
    (representedSchemeBaseChangeHom B S hS g) (representedReindexHom B S hS T'))
  refine Sheaf.hom_ext_sections fun W x ↦
    (fSharpSetComp_representedSquareDirectImageIso_apply B S hS g hg W x).trans ?_
  exact ((congrArg (fun y => (Sheaf.sectionsFunctor _
      (Opposite.op ((representedSchemeBaseChange B S hS g).obj W.unop))).map
        (fSharpSet (representedReindexHom B S hS T')) y)
      (fSharpSet_representedSchemeBaseChangeHom_apply B S hS g W x)).trans
    (fSharpSet_representedReindexHom_apply B S hS T' _ _)).symm


/-- The structure map of `AlgebraicGeometry.Space.representedSquareHom` is the composite structure
map of the lower route (`Stacks.Sheaves.RingedToposModules.RingedToposHom.fSharpSetComp_comp`). -/
theorem fSharpSetComp_representedSquareHom :
    fSharpSetComp (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g) ≫
      (Iso.refl ((representedReindexHom B S hS T').toToposHom.pushforward ⋙
        (representedSchemeBaseChangeHom B S hS g).toToposHom.pushforward)).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)) =
      fSharpSet (representedSquareHom B S hS g) :=
  RingedToposHom.fSharpSetComp_comp.{u, u, u + 1, u, u + 1, u, u + 1}
    (representedSchemeBaseChangeHom B S hS g) (representedReindexHom B S hS T')

/-- The comparison of pullbacks of modules along the lower route of the square of `g`: the pullback
along the diagonal `AlgebraicGeometry.Space.representedSquareHom` is the pullback along base
change of schemes followed by the pullback along the reindexing of `T'`
(`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso`, the diagonal being the composite). -/
noncomputable abbrev representedSchemeRoutePullbackCompIso :=
  pullbackModulesCompIso (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
    (representedSquareHom B S hS g) (Iso.refl _) (fSharpSetComp_representedSquareHom B S hS g)

/-- The comparison of pullbacks of modules along the upper route of the square of `g`: the pullback
along the diagonal is the pullback along the reindexing of `T` followed by the inverse image of
Stacks 03LU along `φ`, through the comparison of direct images
`AlgebraicGeometry.Space.representedSquareDirectImageIso`. -/
noncomputable abbrev representedSpaceRoutePullbackCompIso :=
  pullbackModulesCompIso (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
    (representedReindexHom B S hS T) (representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g hg)
    (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)


section Reindex

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The equivalence of Stacks 04M0 between sheaves of modules on the small étale site of the
scheme underlying `U` and on the small étale site of `yoneda.obj U`
(`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`), with the two categories
spelled as the sides of `AlgebraicGeometry.Space.representedReindexHom`. -/
noncomputable abbrev representedReindexEquivalence (U : BigFppfOver B S hS) : @Equivalence
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
        U.left.property).toRingedTopos.O))
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)) _ _ :=
  representedSmallEtaleModuleEquivalence B S hS U

/-- The direct image of modules along the reindexing of `U` is the inverse of the comparison of
Stacks 04M0: both are restriction along the inverse of the comparison of sites, and the two
agree on underlying sheaves of sets
(`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral`). -/
noncomputable abbrev representedReindexPushforwardIso (U : BigFppfOver B S hS) :
    @Iso ((_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)) ⥤
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
        U.left.property).toRingedTopos.O))) _
      (pushforwardModules.{u, u, u, u + 1, u, u + 1} (representedReindexHom B S hS U))
      (representedReindexEquivalence B S hS U).inverse :=
  (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U)).pushforwardModulesToposIsoGeneral

/-- The pullback of modules along the reindexing of `U` is the functor of the comparison of
Stacks 04M0: both are left adjoints of the inverse of that comparison, the pullback through
`AlgebraicGeometry.Space.representedReindexPushforwardIso`.  This is
`Stacks.SheafOfModules.pullbackModulesReindexIso` read at the sides of
`AlgebraicGeometry.Space.representedReindexHom`; it is built from the adjunction of the pullback
along `AlgebraicGeometry.Space.representedReindexHom` itself, so that its mate is
`AlgebraicGeometry.Space.representedReindexPushforwardIso` with no change of spelling. -/
noncomputable abbrev representedReindexPullbackIso (U : BigFppfOver B S hS) :
    (representedReindexHom B S hS U).pullbackModules ≅
      (representedSmallEtaleModuleEquivalence B S hS U).functor :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules (representedReindexHom B S hS U)).ofNatIsoRight
      (representedReindexPushforwardIso B S hS U))
    (representedReindexEquivalence B S hS U).toAdjunction

end Reindex

/-- **The two routes round the square of `g` have the same pullback of modules.**  It is
`Stacks.SheafOfModules.factorizationPullbackIso` at the square of `g`.  Base change of
schemes along `g` followed by the comparison of Stacks 04M0 for `T'` is the comparison for `T`
followed by the inverse image of Stacks 03LU along `φ`: both are the pullback of modules along
the diagonal `AlgebraicGeometry.Space.representedSquareHom`, by the comparisons of pullbacks
`AlgebraicGeometry.Space.representedSchemeRoutePullbackCompIso` and
`AlgebraicGeometry.Space.representedSpaceRoutePullbackCompIso` of the two factorizations. -/
noncomputable def representedSquareModulePullbackIso :
    SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').functor ≅
      (representedSmallEtaleModuleEquivalence B S hS T).functor ⋙
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)).pullbackModules :=
  Stacks.SheafOfModules.factorizationPullbackIso
    (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
    (representedReindexHom B S hS T) (representedSquareHom B S hS g) (Iso.refl _)
    (fSharpSetComp_representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g hg)
    (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)
    (representedReindexPullbackIso B S hS T')
    (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
    (representedReindexPullbackIso B S hS T)




/-- **Stacks 03EL is compatible with the square of a morphism of representable algebraic spaces.**
For sheaves of modules `M, N` on the small étale site of the scheme underlying `T`, the comparison
of Stacks 03EL for small étale base change of schemes along `g`
(`AlgebraicGeometry.SmallEtale.baseChangeTensorIso`) read on `yoneda.obj T'` by the comparison of
Stacks 04M0 (`Stacks.SheafOfModules.reindexTensorIso`), and carried along
`AlgebraicGeometry.Space.representedSquareModulePullbackIso`, is the comparison of Stacks 04M0 for
`T` followed by the comparison of Stacks 03EL for the inverse image of Stacks 03LU along `φ`.

The statement is that of
`Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso` at the square
of `g`; it is written through `type_of%` so that it is that statement verbatim: a separately
written copy differs from it in the spelling of the categories of modules, and comparing the two
spellings exhausts the elaboration budget. -/
theorem representedSquare_pullbackTensorIsoTransport
    (M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :
    type_of% (Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso
      (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)
      (representedReindexPullbackIso B S hS T')
      (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
      (representedReindexPullbackIso B S hS T) M N) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso
    (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
    (representedReindexHom B S hS T) (representedSquareHom B S hS g) (Iso.refl _)
    (fSharpSetComp_representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g hg)
    (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)
    (representedReindexPullbackIso B S hS T')
    (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
    (representedReindexPullbackIso B S hS T) M N

end AlgebraicGeometry.Space

end
