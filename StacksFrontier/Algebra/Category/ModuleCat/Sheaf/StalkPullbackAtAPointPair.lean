module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafifyLocallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkSheafExact
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a pullback of sheaves of modules, at a matched pair of points

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi, let `Φ` be a point of `C`
and let `Ψ` be a point of `D` whose stalk functor on sheaves of sets is the inverse image along
`f` followed by the stalk functor of `Φ`.  Stacks 05V5 computes the stalk at `Φ` of the
pullback of a sheaf of `𝒪'`-modules as a base change of its stalk at `Ψ`:

`(f^*G)_Φ ≅ G_Ψ ⊗_{𝒪'_Ψ} 𝒪_Φ`,

naturally in `G`, along a homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings read off the structure map
of `f`.

The pullback of Stacks 03D6 is the inverse image of Stacks 03D2 followed by extension of
scalars along the inverse-image form `f⁻¹𝒪' ⟶ 𝒪` of the structure map, so the computation is in
two steps.  The inverse image contributes Stacks 05V1 at `Ψ`, the identification `G_Ψ ≅
(f⁻¹G)_Φ` semilinear over an isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings.  The extension of
scalars of Stacks 03CZ contributes the stalkwise formula for a sectionwise tensor product,
`(𝒪 ⊗_{f⁻¹𝒪'} F)_Φ ≅ 𝒪_Φ ⊗_{(f⁻¹𝒪')_Φ} F_Φ`, which survives the sheafification that extension
of scalars performs because the stalk does not see it.

## Main definitions

* `Stacks.Sheaves.StalkPullback.commRingStalkEquiv`: the isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of
  stalk rings, read between `CommRingCat`-valued stalks.
* `Stacks.Sheaves.StalkPullback.stalkRingMap`: the homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings
  along which the comparison extends scalars.

## Main results

* `Stacks.Sheaves.StalkPullback.stalkFunctorIso`: **Stacks 05V5** at the matched pair `(Φ, Ψ)`,
  as a natural isomorphism of stalk functors.  `Stacks.Sheaves.StalkPullback.targetSitePoint`
  builds the pair from `f` and `Φ` alone, and
  `Stacks.Sheaves.StalkPullback.pointStalkFunctorIso` is the resulting unconditional form.
* `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso`: the base-change input, stated
  for a site whose object and morphism universes are independent of the universe of the
  sheaves.

## Implementation notes

The comparison already exists for a morphism of ringed topoi presented by a morphism of the
underlying *sites*, as
`Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkFunctorIso`.  There the point
`Ψ` and the identification of stalk functors are produced from the site functor by part (2) of
Stacks 00YA.  Everything else is that argument verbatim, with `Ψ` and the identification taken
as data so that the chain can be run at a morphism of ringed topoi that is not presented by a
functor of the two sites — the canonical morphism of small étale ringed topoi of a morphism of
algebraic spaces is one, since a morphism of algebraic spaces does not pull étale charts of the
target back to étale charts of the source.

Taking them as data is a convenience of this file and not a limitation: *every* morphism of
ringed topoi transports points, because `Φ` is a point of the topos `Sh(C)` by Stacks 00YA
part (1) and the composite `q = f ∘ Φ` is then a point of `Sh(D)` to which Stacks 00YA part (2)
applies, with no presentation by site functors involved.  That is carried out in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkPullbackAtAPoint.lean`, which feeds the pair
below with `Ψ` and the identification built from `f` and `Φ` alone.

One of its inputs is restated rather than used.
`Stacks.SitePointBaseChange.extendScalarsSheafStalkNatIso` is stated for a site whose objects
and morphisms live in the universe of the sheaves; the small étale site of an algebraic space
does not, its objects forming a type one universe larger than its sheaves.  It is built from
`asIso` of a comparison that is itself universe-polymorphic
(`Stacks.moduleFiberSheafificationComparison`), so the restriction is not a mathematical one
and `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso` below is the same term with the
universes left free. The stalk of a sheafification is
`Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.fiberSheafifyNatIso`, which already
leaves them free.

The chain is written out link by link, as in the morphism-of-sites case: consecutive links
differ by associativity of functor composition and by the unfolding of one definition, and
naming each keeps every definitional unfolding local.

Three spellings of the stalk functor on sheaves of modules occur and agree by `rfl`:
`Stacks.sheafModuleFiberOfCommRing Φ 𝒪` over the structure sheaf of a ringed topos,
`Stacks.Sheaves.StalkPullback.sheafStalk Φ A h` over a presheaf of commutative rings whose
underlying presheaf of rings is a sheaf, and the composite of
`Stacks.sheafModuleFiber` with restriction of scalars along `Stacks.toRingFiber`.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.StalkInverseImage

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

noncomputable section

universe w v u v' u'

namespace Stacks.Sheaves.StalkPullback

/-! ### The two generic inputs, with the universes of the site left free -/

section Generic

open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The stalk functor at `Φ` on sheaves of modules over a presheaf of commutative rings whose
underlying presheaf of rings is a sheaf, valued in modules over the `CommRingCat`-valued stalk
of that presheaf. -/
abbrev sheafStalk (A : Cᵒᵖ ⥤ CommRingCat.{w}) (h : Presheaf.IsSheaf J (ringPresheaf A)) :
    SheafOfModules.{w} (commRingSheaf J A h) ⥤ ModuleCat.{w} (Stacks.ringFiber Φ A) :=
  SheafOfModules.forget (commRingSheaf J A h) ⋙ Stacks.presheafModuleFiberOfCommRing Φ A

/-- **The base-change colimit interchange at a point of a site, for sheaves of modules.**
Taking stalks at `Φ` carries extension of scalars of sheaves of modules along `θ` to extension
of scalars along the stalk of `θ`.

This is `Stacks.SitePointBaseChange.extendScalarsSheafStalkNatIso` with the object and morphism
universes of the site independent of the universe of the sheaves. -/
def extendScalarsSheafStalkNatIso {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
    (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂)) :
    Stacks.Sheaves.RingedToposModules.extendScalars J θ h₁ h₂ ⋙ sheafStalk Φ A₂ h₂ ≅
      sheafStalk Φ A₁ h₁ ⋙ ModuleCat.extendScalars (SitePointBaseChange.stalkRingHom θ Φ) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙ changeOfRings θ)
        (Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.fiberSheafifyNatIso Φ
          (commRingSheaf J A₂ h₂)).symm)
      (ModuleCat.restrictScalars.{w} (Stacks.toRingFiber Φ A₂)) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.forget (commRingSheaf J A₁ h₁))
      (SitePointBaseChange.extendScalarsStalkNatIso θ Φ).symm

end Generic

/-! ### The comparison at a matched pair of points -/

section Pair

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [LocallySmall.{w} X.C] [LocallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (Φ : X.J.Point.{w}) (Ψ : Y.J.Point.{w})
  (e : Ψ.sheafFiber (A := Type w) ≅
    f.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type w))

/-- The inverse image `f⁻¹𝒪'` of the structure sheaf of the target, as a presheaf of
commutative rings on the source site. -/
abbrev inverseImageStructure : X.Cᵒᵖ ⥤ CommRingCat.{w} := inverseImageStructureCommRing f

/-- The inverse image `f⁻¹𝒪'` of the structure sheaf of the target, as a sheaf of rings on the
source site. -/
abbrev inverseImageStructureRing : Sheaf X.J RingCat.{w} :=
  inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The inverse image of sheaves of modules along `f`, Stacks 03D2. -/
abbrev inverseImageFunctor :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (inverseImageStructureRing f) :=
  inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The stalk at `Φ` of a sheaf of `f⁻¹𝒪'`-modules, over the `RingCat`-valued stalk of
`f⁻¹𝒪'`. -/
abbrev inverseImageStalkFunctor := Stacks.sheafModuleFiber Φ (inverseImageStructureRing f)

/-- The comparison of the `CommRingCat`-valued stalk of `f⁻¹𝒪'` at `Φ` with its `RingCat`-valued
stalk. -/
abbrev toInverseImageStalkRing := Stacks.toRingFiber Φ (inverseImageStructure f)

/-- The comparison of the `CommRingCat`-valued stalk `𝒪'_Ψ` with the `RingCat`-valued stalk of
the sheaf of rings underlying `𝒪'`. -/
abbrev toTargetStalkRing := Stacks.toRingFiber Ψ Y.O.obj

/-- The stalk at `Φ` of the inverse-image form of the structure map of `f`. -/
abbrev fSharpStalk := SitePointBaseChange.stalkRingHom (fSharpCommRing f) Φ

/-- The `CommRingCat`-valued germ of a section is the germ read through the stalk comparison of
the underlying sheaf of rings. -/
private theorem commRingPresheafFiberIso_ringStalkComparison_germ
    {D : Type u'} [Category.{v'} D] [LocallySmall.{w} D] {K : GrothendieckTopology D}
    (Φ : K.Point.{w})
    [K.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    (A : Dᵒᵖ ⥤ CommRingCat.{w})
    (hA : Presheaf.IsSheaf K (A ⋙ forget₂ CommRingCat RingCat.{w}))
    (W : D) (u : Φ.fiber.obj W) (t : A.obj (Opposite.op W)) :
    (Stacks.commRingPresheafFiberIso Φ A).hom.hom
        (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ
          ⟨A ⋙ forget₂ CommRingCat RingCat, hA⟩
          (Φ.toPresheafFiber W u
            ((sheafCompose K (forget RingCat.{w})).obj
              ⟨A ⋙ forget₂ CommRingCat RingCat, hA⟩).obj t)) =
      Φ.toPresheafFiber W u A t :=
  (congrArg _ (Stacks.Sheaves.StalkTransport.ringStalkComparison_germ Φ
    ⟨A ⋙ forget₂ CommRingCat RingCat, hA⟩ W u t)).trans
    (ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
        (F := forget₂ CommRingCat.{w} RingCat.{w}) W u A) t)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [LocallySmall.{w} Y.C] in
/-- **The stalk of the structure map, read across the two forgetful comparisons.**  Applying the
stalk at `Φ` of the inverse-image form of the structure map to the `CommRingCat`-valued reading
of an element of the fibre of the inverse image of the underlying sheaf of sets gives the
`CommRingCat`-valued reading of the fibre of the set-level structure map applied to that
element.

Both sides carry the germ of a section to the germ of its image, and germs of the fibre of a
sheaf of sets are jointly surjective, so the identity is checked on germs: each of its factors
is one of the two comparisons "the stalk commutes with a forgetful functor", and each of those
carries germs to germs. -/
theorem fSharpStalk_commRingPresheafFiberIso_ringStalkComparison
    (z : (Φ.sheafFiber (A := Type w)).obj
      ((sheafCompose X.J (forget RingCat.{w})).obj (inverseImageStructureRing f))) :
    fSharpStalk f Φ
        ((Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).hom.hom
          (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ
            (inverseImageStructureRing f) z)) =
      (Stacks.commRingPresheafFiberIso Φ X.O.obj).hom.hom
        (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((Φ.sheafFiber (A := Type w)).map
            ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) z)) := by
  obtain ⟨W, u, t, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := ((sheafCompose X.J (forget RingCat.{w})).obj (inverseImageStructureRing f)).obj) z
  have hleft : fSharpStalk f Φ
        ((Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).hom.hom
          (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ (inverseImageStructureRing f)
            (Φ.toPresheafFiber W u
              ((sheafCompose X.J (forget RingCat.{w})).obj
                (inverseImageStructureRing f)).obj t))) =
      Φ.toPresheafFiber W u X.O.obj ((fSharpCommRing f).app (Opposite.op W) t) :=
    (congrArg (fSharpStalk f Φ) (commRingPresheafFiberIso_ringStalkComparison_germ Φ
      (inverseImageStructure f) (inverseImageStructureRing f).property W u t)).trans
      (Φ.toPresheafFiber_naturality_apply (fSharpCommRing f) W u t)
  have hright : (Stacks.commRingPresheafFiberIso Φ X.O.obj).hom.hom
        (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (Φ.presheafFiber.map
            ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage).hom
            (Φ.toPresheafFiber W u
              ((sheafCompose X.J (forget RingCat.{w})).obj
                (inverseImageStructureRing f)).obj t))) =
      Φ.toPresheafFiber W u X.O.obj ((fSharpCommRing f).app (Opposite.op W) t) :=
    (congrArg (fun y ↦ (Stacks.commRingPresheafFiberIso Φ X.O.obj).hom.hom
      (Stacks.Sheaves.StalkTransport.ringStalkComparison Φ
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) y))
      (Φ.toPresheafFiber_naturality_apply
        ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage).hom W u t)).trans
      (commRingPresheafFiberIso_ringStalkComparison_germ Φ X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property W u _)
  exact hleft.trans hright.symm

/-- **The isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of `CommRingCat`-valued stalk rings.**  It is the
comparison of `RingCat`-valued stalks of Stacks 05V1, conjugated at either end by the
comparison of the `RingCat`-valued stalk of a presheaf of commutative rings with its
`CommRingCat`-valued one. -/
def commRingStalkEquiv :
    Stacks.ringFiber Ψ Y.O.obj ≃+* Stacks.ringFiber Φ (inverseImageStructure f) :=
  (((Stacks.commRingPresheafFiberIso Ψ Y.O.obj).ringCatIsoToRingEquiv.symm.trans
        (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e)).trans
    (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).ringCatIsoToRingEquiv)

/-- **The homomorphism `𝒪'_Ψ ⟶ 𝒪_Φ` of stalk rings.**  It is the isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ`
followed by the stalk at `Φ` of the inverse-image form `f⁻¹𝒪' ⟶ 𝒪` of the structure map
of `f`. -/
def stalkRingMap : Stacks.ringFiber Ψ Y.O.obj →+* Stacks.ringFiber Φ X.O.obj :=
  (fSharpStalk f Φ).comp (commRingStalkEquiv f Φ Ψ e).toRingHom

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The isomorphism `𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of `CommRingCat`-valued stalks is compatible with the
comparisons to the `RingCat`-valued stalks and with the isomorphism of Stacks 05V1. -/
theorem toInverseImageStalkRing_comp_commRingStalkEquiv :
    (toInverseImageStalkRing f Φ).comp (commRingStalkEquiv f Φ Ψ e).toRingHom =
      (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          Φ Ψ e).toRingHom.comp
        (toTargetStalkRing Ψ) :=
  RingHom.ext fun _ ↦ RingEquiv.symm_apply_apply
    (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f)).ringCatIsoToRingEquiv _

/-- The stalk at `Φ` of the extension of scalars along `f⁻¹𝒪' ⟶ 𝒪` is the extension of scalars
along the stalk of that map: Stacks 05V5 for the second half of the pullback. -/
def stalkIsoStepOne :
    f.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ ⋙
        ModuleCat.restrictScalars (toInverseImageStalkRing f Φ) ⋙
          ModuleCat.extendScalars (fSharpStalk f Φ) :=
  Functor.isoWhiskerLeft (inverseImageFunctor f)
    (extendScalarsSheafStalkNatIso Φ (fSharpCommRing f)
      (inverseImageStructureRing f).property (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)

/-- Precomposing the restriction and the extension of scalars with the isomorphism
`𝒪'_Ψ ≅ (f⁻¹𝒪')_Φ` of stalk rings leaves their composite unchanged. -/
def stalkIsoStepTwo :
    inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ ⋙
        ModuleCat.restrictScalars (toInverseImageStalkRing f Φ) ⋙
          ModuleCat.extendScalars (fSharpStalk f Φ) ≅
      inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ ⋙
        ModuleCat.restrictScalars ((toInverseImageStalkRing f Φ).comp
            (commRingStalkEquiv f Φ Ψ e).toRingHom) ⋙
          ModuleCat.extendScalars (stalkRingMap f Φ Ψ e) :=
  Functor.isoWhiskerLeft (inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ)
    (ModuleCat.restrictExtendScalarsCompIso (toInverseImageStalkRing f Φ)
      (fSharpStalk f Φ) (commRingStalkEquiv f Φ Ψ e)).symm

/-- The restriction of scalars along the composite `𝒪'_Ψ ⟶ (f⁻¹𝒪')_Φ` of the two comparisons of
stalk rings is the successive restriction along each of them. -/
def stalkIsoStepThree :
    inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ ⋙
        ModuleCat.restrictScalars ((toInverseImageStalkRing f Φ).comp
            (commRingStalkEquiv f Φ Ψ e).toRingHom) ⋙
          ModuleCat.extendScalars (stalkRingMap f Φ Ψ e) ≅
      inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ ⋙
        (ModuleCat.restrictScalars
              (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                Φ Ψ e).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing Ψ)) ⋙
          ModuleCat.extendScalars (stalkRingMap f Φ Ψ e) :=
  Functor.isoWhiskerLeft (inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ)
    (Functor.isoWhiskerRight
      (ModuleCat.restrictScalarsComp' (toTargetStalkRing Ψ)
        (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e).toRingHom _
        (toInverseImageStalkRing_comp_commRingStalkEquiv f Φ Ψ e))
      (ModuleCat.extendScalars (stalkRingMap f Φ Ψ e)))

/-- Stacks 05V1 at `Ψ`: the stalk functor at `Ψ` is the inverse image followed by the stalk
functor at `Φ` and restriction of scalars. -/
def stalkIsoStepFour :
    inverseImageFunctor f ⋙ inverseImageStalkFunctor f Φ ⋙
        (ModuleCat.restrictScalars
              (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                Φ Ψ e).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing Ψ)) ⋙
          ModuleCat.extendScalars (stalkRingMap f Φ Ψ e) ≅
      Stacks.sheafModuleFiberOfCommRing Ψ Y.O ⋙
        ModuleCat.extendScalars (stalkRingMap f Φ Ψ e) :=
  (Functor.isoWhiskerRight
    (stalkNatIso f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e)
    (ModuleCat.restrictScalars (toTargetStalkRing Ψ) ⋙
      ModuleCat.extendScalars (stalkRingMap f Φ Ψ e))).symm

/-- **Stacks 05V5 at a matched pair of points**, as a natural isomorphism of stalk functors:
the stalk at `Φ` of the pullback of a sheaf of `𝒪'`-modules is the extension of scalars along
`𝒪'_Ψ ⟶ 𝒪_Φ` of its stalk at `Ψ`.

This is the clause of Stacks 05V5 that
`AlgebraicGeometry.RingedToposHom.pullbackModulesSquareIso` states for a commutative square of
morphisms of ringed topoi without constructing the square over a point; here the point of the
target topos and the identification of stalk functors are the data `Ψ` and `e`. -/
@[stacks 05V5 "the formula `(f^*G)_Φ ≅ G_Ψ ⊗_{O'_Ψ} O_Φ`, naturally in the `O'`-module `G`, for
a morphism of ringed topoi together with a point `Ψ` of the target site whose stalk functor on
sheaves of sets is the inverse image followed by the stalk functor at `Φ`"]
def stalkFunctorIso :
    f.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      Stacks.sheafModuleFiberOfCommRing Ψ Y.O ⋙
        ModuleCat.extendScalars (stalkRingMap f Φ Ψ e) :=
  stalkIsoStepOne f Φ ≪≫ stalkIsoStepTwo f Φ Ψ e ≪≫ stalkIsoStepThree f Φ Ψ e ≪≫
    stalkIsoStepFour f Φ Ψ e

end Pair

end Stacks.Sheaves.StalkPullback

end

end
