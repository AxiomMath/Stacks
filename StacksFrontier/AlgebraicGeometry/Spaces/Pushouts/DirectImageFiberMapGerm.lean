module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModuleStalkCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageFiberGerm

/-!
# The germ formula for the comparison of geometric module fibres along a direct image

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `ȳ` a geometric point of `Y` with image `x̄`,
and `M` an `𝒪_Y`-module.  The comparison `θ_M : (f_*M)_x̄ ⟶ M_ȳ` of
`AlgebraicGeometry.Space.directImageFiberMap` is defined as a transpose along extension of
scalars: the identification `𝒪_{Y,ȳ} ⊗ (f_*M)_x̄ ≅ (f^*f_*M)_ȳ` of Stacks 05V5 followed by the
fibre of the counit `f^*f_*M ⟶ M`.  This file computes it on germs.

A section `t` of `f_*M` over an étale chart `U` of `X` is a section of the spaces-étale sheaf of
sets `E⁻¹M` over `U ×_X Y`, `E` being the comparison equivalence of Stacks 03G1.  Given a chart
`W` of `Y`, a lift `w` of `ȳ` to `W` and a morphism `h : W ⟶ U ×_X Y` of spaces étale over `Y`
carrying `w` to the lift of `ȳ` that the cartesian square of Stacks 03G2, part (1) assigns to a
lift `u` of `x̄` to `U`, the germ of `t` at `(U, u)` goes to the germ at `(W, w)` of the
restriction of `t` along `h`, read in `M(W)` through the counit of `E`:

`θ_M (germ_{x̄}(U, u, t)) = germ_{ȳ}(W, w, ε_W (t|_W))`.

## Main results

* `AlgebraicGeometry.Space.directImageFiberMap_germ`: the germ formula.
* `Stacks.Sheaves.StalkPullback.stalkFunctorIso_inv_app_one_tmul`: Stacks 05V5 read backwards on
  `1 ⊗ n`, at a matched pair of points of an arbitrary morphism of ringed topoi: the stalk of the
  unit of extension of scalars, applied to the image of `n` under Stacks 05V1.
* `StalkPullback.sheafModuleFiberOfCommRing_map_counit_stalkFunctorIso_inv_app_one_tmul`:
  the fibre of the counit of Stacks 03D7, precomposed with Stacks 05V5 on `1 ⊗ -`, is the fibre of
  the counit `f⁻¹f_* ⟶ id` of sheaves of sets precomposed with the fibre comparison.
* `AlgebraicGeometry.Space.sheafFiber_map_counit_smallEtaleInverseImageFiberIso_germ`: the
  set-level germ formula for that composite on the small étale sites.

## Implementation notes

The module level is reduced to the set level in general: Stacks 05V5 is a chain of four
identifications, three of which fix `1 ⊗ n` on the nose and the fourth of which is the
mate computation `Stacks.Sheaves.StalkPullback.unit_square_app`; the counit of Stacks 03D7 is
the extension-of-scalars counit after the Stacks 03D3 counit, and the triangle identity of the
first cancels the unit coming out of Stacks 05V5.  What is left is the counit of `f⁻¹ ⊣ f_*` on
the underlying sheaf of sets, by
`RingedToposModules.moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app`.

The set level is the argument of `AlgebraicGeometry.Space.stalkStructureMap_eq` with the
structure sheaf replaced by an arbitrary sheaf of sets: the fibre comparison is the conjugate of
the skyscraper comparison, so the composite is the transpose of the direct image of the
skyscraper unit followed by that comparison, whose components are computed by
`AlgebraicGeometry.Space.smallEtaleSkyscraperIso_hom_app_π`.

The space-level comparison `AlgebraicGeometry.Space.modulePullbackFiberIso` is passed to the
general statement as a variable together with the equation identifying it with
`Stacks.Sheaves.StalkPullback.stalkFunctorIso`, and the two spellings
`(smallEtaleRingedToposModulesHom f).toToposHom` and `(smallEtaleRingedToposHom f).toToposHom` of
the morphism of topoi are only ever compared through their components: unifying the two
morphisms as wholes, or the two comparisons as unfolded terms, does not finish within the
heartbeat budget.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe u'

variable {R S : Type u'} [CommRing R] [CommRing S]

/-- Along a ring isomorphism `α`, the identification of restriction followed by extension of
scalars with the identity carries `1 ⊗ p` to `p`. -/
theorem restrictExtendScalarsSelfIso_hom_app_one_tmul (α : R ≃+* S) (P : ModuleCat.{u'} S)
    (p : P) :
    (restrictExtendScalarsSelfIso α).hom.app P
        ((1 : S) ⊗ₜ[R, α.toRingHom] (show (restrictScalars.{u'} α.toRingHom).obj P from p)) =
      p := by
  have h := ConcreteCategory.congr_hom (Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictScalarsAdj.{u', u', u'} α.toRingHom)
    (restrictScalarsEquivalenceOfRingEquiv.{u', u', u'} α).symm.toAdjunction
    ((restrictScalars.{u'} α.toRingHom).obj P)) p
  exact (congrArg ((restrictScalarsEquivalenceOfRingEquiv.{u', u', u'} α).unitIso.inv.app P)
    h).trans rfl

variable {T A : Type u'} [Ring T] [CommRing A]

/-- The identification `ModuleCat.restrictExtendScalarsCompIso` of the composites of restriction
and extension of scalars before and after precomposing with a ring isomorphism carries `1 ⊗ q`
to `1 ⊗ q`. -/
theorem restrictExtendScalarsCompIso_hom_app_one_tmul (ρ : S →+* T) (ψ : S →+* A) (α : R ≃+* S)
    (Q : ModuleCat.{u'} T) (q : Q) :
    (restrictExtendScalarsCompIso ρ ψ α).hom.app Q
        ((1 : A) ⊗ₜ[R, ψ.comp α.toRingHom]
          (show (restrictScalars.{u'} (ρ.comp α.toRingHom)).obj Q from q)) =
      (1 : A) ⊗ₜ[S, ψ] (show (restrictScalars.{u'} ρ).obj Q from q) := by
  have h2 := extendScalarsComp_hom_app_one_tmul α.toRingHom ψ
    ((restrictScalars.{u'} α.toRingHom).obj ((restrictScalars.{u'} ρ).obj Q)) q
  have h3 := restrictExtendScalarsSelfIso_hom_app_one_tmul α ((restrictScalars.{u'} ρ).obj Q) q
  refine (congrArg (ConcreteCategory.hom ((extendScalars ψ).map
    ((restrictExtendScalarsSelfIso α).hom.app ((restrictScalars.{u'} ρ).obj Q)))) h2).trans ?_
  refine (ExtendScalars.map_tmul _ _ _ _).trans ?_
  exact congrArg (fun z => (1 : A) ⊗ₜ[S, ψ] z) h3

/-- **Transport across an isomorphism in the source of a comparison
`P : L ⋙ F_Y ≅ F_X ⋙ extendScalars φ`.**  For `i : A ≅ A'` and `c : L A ⟶ B`, the image of
`1 ⊗ F_X(i)(m)` under `P⁻¹` at `A'`, followed by `F_Y(L(i⁻¹) ≫ c)`, is the image of `1 ⊗ m` under
`P⁻¹` at `A` followed by `F_Y(c)`: naturality of `P⁻¹` at `i⁻¹`. -/
theorem map_comp_inv_app_one_tmul_map_hom {C : Type*} [Category C] {D : Type*} [Category D]
    (L : C ⥤ D) (FX : C ⥤ ModuleCat.{u'} R) (FY : D ⥤ ModuleCat.{u'} S) (φ : R →+* S)
    (P : L ⋙ FY ≅ FX ⋙ extendScalars.{u', u', u'} φ) {A A' : C} (i : A ≅ A') {B : D}
    (c : L.obj A ⟶ B) (m : FX.obj A) :
    FY.map (L.map i.inv ≫ c) (P.inv.app A' ((1 : S) ⊗ₜ[R, φ] FX.map i.hom m)) =
      FY.map c (P.inv.app A ((1 : S) ⊗ₜ[R, φ] m)) := by
  have h1 := ConcreteCategory.congr_hom (P.inv.naturality i.inv)
    ((1 : S) ⊗ₜ[R, φ] FX.map i.hom m)
  have h2 : FX.map i.inv (FX.map i.hom m) = m :=
    ConcreteCategory.congr_hom (FX.mapIso i).hom_inv_id m
  rw [Functor.map_comp, ConcreteCategory.comp_apply]
  refine congrArg (FY.map c) (Eq.trans h1.symm ?_)
  exact congrArg (P.inv.app A) ((ExtendScalars.map_tmul _ _ _ _).trans (congrArg _ h2))

end ModuleCat

namespace Stacks.Sheaves.StalkPullback

open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.StalkInverseImage Stacks.Sheaves.StalkTransport

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe w v₁ u₁ v₂ u₂

variable {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
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

/-- **Stacks 05V5 on `1 ⊗ n`.**  At a matched pair of points `(Φ, Ψ)` of a morphism of ringed
topoi `f`, the comparison `(f^*N)_Φ ≅ 𝒪_Φ ⊗ N_Ψ` read backwards carries `1 ⊗ n` to the stalk of
the unit `f⁻¹N ⟶ 𝒪 ⊗_{f⁻¹𝒪'} f⁻¹N` of Stacks 03CZ applied to the image of `n` under the
identification `N_Ψ ≅ (f⁻¹N)_Φ` of Stacks 05V1 (the identification of the two stalks of a
restriction of scalars, `Stacks.Sheaves.StalkPullback.restrictScalarsStalkHom`, being the identity
on elements).  The last three links of `Stacks.Sheaves.StalkPullback.stalkFunctorIso` fix `1 ⊗ n`;
the first is `Stacks.Sheaves.StalkPullback.unit_square_app`. -/
theorem stalkFunctorIso_inv_app_one_tmul
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (n : (Stacks.sheafModuleFiberOfCommRing Ψ Y.O).obj N) :
    (stalkFunctorIso f Φ Ψ e).inv.app N
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e] n) =
      restrictScalarsStalkHom Φ (fSharpCommRing f)
        ((extendScalarsFSharp f).obj ((inverseImageFunctor f).obj N)).val
        ((sheafStalk Φ (inverseImageStructure f) (inverseImageStructureRing f).property).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageStructureRing f).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageFunctor f).obj N))
          (stalkModuleMap f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e N
            n)) := by
  let k := stalkModuleMap f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e N n
  have h4 : (stalkIsoStepFour f Φ Ψ e).inv.app N
      ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e] n) =
      (1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
        (show ((ModuleCat.restrictScalars
              (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ
                e).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing Ψ)).obj
              ((inverseImageStalkFunctor f Φ).obj ((inverseImageFunctor f).obj N))) from k) := rfl
  have h3 : (stalkIsoStepThree f Φ Ψ e).inv.app N
      ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
        (show ((ModuleCat.restrictScalars
              (stalkRingEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ
                e).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing Ψ)).obj
              ((inverseImageStalkFunctor f Φ).obj ((inverseImageFunctor f).obj N))) from k)) =
      (1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
        (show (ModuleCat.restrictScalars ((toInverseImageStalkRing f Φ).comp
            (commRingStalkEquiv f Φ Ψ e).toRingHom)).obj
              ((inverseImageStalkFunctor f Φ).obj ((inverseImageFunctor f).obj N)) from k) := rfl
  have h2 := ModuleCat.restrictExtendScalarsCompIso_hom_app_one_tmul (toInverseImageStalkRing f Φ)
    (fSharpStalk f Φ) (commRingStalkEquiv f Φ Ψ e)
    ((inverseImageStalkFunctor f Φ).obj ((inverseImageFunctor f).obj N)) k
  have h1 := unit_square_app Φ (fSharpCommRing f) (inverseImageStructureRing f).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((inverseImageFunctor f).obj N) k
  exact (congrArg (fun z =>
      (stalkIsoStepOne f Φ).inv.app N ((stalkIsoStepTwo f Φ Ψ e).inv.app N z))
    ((congrArg (fun z => (stalkIsoStepThree f Φ Ψ e).inv.app N z) h4).trans h3)).trans
    ((congrArg (fun z => (stalkIsoStepOne f Φ).inv.app N z) h2).trans h1)

/-- **Stacks 05V5 on `1 ⊗ n`, followed by a map out of the pullback.**  For a map
`φ : f^*N ⟶ M` and an element `z` of the fibre at `Ψ` of the sheaf of sets underlying `N`, the
fibre of `φ` at `Φ` applied to the image of `1 ⊗ z` under Stacks 05V5 read backwards is the fibre
at `Φ`, on underlying sheaves of sets, of the transpose `f⁻¹N ⟶ M` of `φ` along extension of
scalars, applied to the image of `z` under the fibre comparison `e`. -/
theorem sheafModuleFiberOfCommRing_map_stalkFunctorIso_inv_app_one_tmul
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (φ : f.pullbackModules.obj N ⟶ M)
    (z : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) N)) :
    (Stacks.sheafModuleFiberOfCommRing Φ X.O).map φ ((stalkFunctorIso f Φ Ψ e).inv.app N
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
          moduleStalkComparison Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) N z)) =
      moduleStalkComparison Φ (inverseImageStructureRing f)
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)
        ((Φ.sheafFiber (A := Type w)).map
          ((Sheaf.moduleSheafFunctor (inverseImageStructureRing f)).map
            ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
              (inverseImageStructureRing f).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
                ((inverseImageFunctor f).obj N) ≫
              (SheafOfModules.restrictScalars f.fSharpInverseImage).map φ))
          (e.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) N) z)) := by
  have e1 := stalkFunctorIso_inv_app_one_tmul f Φ Ψ e N
    (moduleStalkComparison Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) N z)
  have e2 := stalkModuleMap_moduleStalkComparison f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ Ψ e N z
  have e3 := moduleStalkComparison_naturality Φ (inverseImageStructureRing f)
    ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageStructureRing f).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
        ((inverseImageFunctor f).obj N) ≫
      (SheafOfModules.restrictScalars f.fSharpInverseImage).map φ)
    (e.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) N) z)
  refine (congrArg (fun q => (Stacks.sheafModuleFiberOfCommRing Φ X.O).map φ q) e1).trans ?_
  refine Eq.trans ?_ e3.symm
  refine (congrArg (fun q => (Stacks.sheafModuleFiberOfCommRing Φ X.O).map φ
    (restrictScalarsStalkHom Φ (fSharpCommRing f)
        ((extendScalarsFSharp f).obj ((inverseImageFunctor f).obj N)).val
        ((sheafStalk Φ (inverseImageStructure f) (inverseImageStructureRing f).property).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageStructureRing f).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageFunctor f).obj N)) q))) e2).trans ?_
  have ha : ∀ q, (sheafStalk Φ (inverseImageStructure f) (inverseImageStructureRing f).property).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageStructureRing f).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageFunctor f).obj N)) q =
      (Stacks.sheafModuleFiber Φ (inverseImageStructureRing f)).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageStructureRing f).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
              ((inverseImageFunctor f).obj N)) q := fun q => rfl
  have hb : ∀ q, (Stacks.sheafModuleFiberOfCommRing Φ X.O).map φ
      (restrictScalarsStalkHom Φ (fSharpCommRing f)
        ((extendScalarsFSharp f).obj ((inverseImageFunctor f).obj N)).val q) =
      (Stacks.sheafModuleFiber Φ (inverseImageStructureRing f)).map
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).map φ) q := fun q => rfl
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    ((Stacks.sheafModuleFiber Φ (inverseImageStructureRing f)).map_comp
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
        (inverseImageStructureRing f).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageFunctor f).obj N))
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).map φ)) _).symm
  exact (hb _).trans (congrArg _ (ha _))

/-- **The fibre of the counit of Stacks 03D7, read through Stacks 05V5, is the fibre of the
counit on sheaves of sets.**  The fibre at `Φ` of the counit `f^*f_*M ⟶ M`, applied to the image
of `1 ⊗ z` under Stacks 05V5 read backwards, is the fibre at `Φ` of the counit `f⁻¹f_*M ⟶ M` of
the underlying sheaves of sets applied to the image of `z` under the fibre comparison `e`.  The
transpose of the counit along extension of scalars is the counit of Stacks 03D3 by the triangle
identity, and that one is the counit on sheaves of sets by
`RingedToposModules.moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app`. -/
theorem sheafModuleFiberOfCommRing_map_counit_stalkFunctorIso_inv_app_one_tmul
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (z : (Ψ.sheafFiber (A := Type w)).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M))) :
    (Stacks.sheafModuleFiberOfCommRing Φ X.O).map ((pullbackAdjPushforwardModules f).counit.app M)
        ((stalkFunctorIso f Φ Ψ e).inv.app ((pushforwardModules f).obj M)
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
          moduleStalkComparison Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((pushforwardModules f).obj M) z)) =
      moduleStalkComparison Φ (inverseImageStructureRing f)
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)
        ((Φ.sheafFiber (A := Type w)).map
          (f.toToposHom.adj.counit.app (Sheaf.moduleSheaf (inverseImageStructureRing f)
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)))
          (e.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((pushforwardModules f).obj M)) z)) := by
  let adj₂ := extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
    (inverseImageStructureRing f).property (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
  let a := (inverseImageAdjDirectImageModules f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)
  have hε : (pullbackAdjPushforwardModules f).counit.app M =
      (extendScalarsFSharp f).map a ≫ adj₂.counit.app M :=
    Adjunction.comp_counit_app _ _ M
  have htri : adj₂.unit.app ((inverseImageFunctor f).obj ((pushforwardModules f).obj M)) ≫
      (SheafOfModules.restrictScalars f.fSharpInverseImage).map
        ((extendScalarsFSharp f).map a ≫ adj₂.counit.app M) = a :=
    (adj₂.homEquiv_unit _ _ ((extendScalarsFSharp f).map a ≫ adj₂.counit.app M)).symm.trans
      ((congrArg (adj₂.homEquiv _ _) (adj₂.homEquiv_counit _ _ a).symm).trans
        (Equiv.apply_symm_apply _ _))
  have hcounit := moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app
    f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)
  refine (sheafModuleFiberOfCommRing_map_stalkFunctorIso_inv_app_one_tmul f Φ Ψ e _ M _ z).trans ?_
  refine (congrArg (fun (k : (inverseImageFunctor f).obj ((pushforwardModules f).obj M) ⟶
      (SheafOfModules.restrictScalars f.fSharpInverseImage).obj M) =>
      moduleStalkComparison Φ (inverseImageStructureRing f)
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)
        ((Φ.sheafFiber (A := Type w)).map
          ((Sheaf.moduleSheafFunctor (inverseImageStructureRing f)).map k)
          (e.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((pushforwardModules f).obj M)) z)))
    ((congrArg (fun g =>
      adj₂.unit.app ((inverseImageFunctor f).obj ((pushforwardModules f).obj M)) ≫
      (SheafOfModules.restrictScalars f.fSharpInverseImage).map g) hε).trans htri)).trans ?_
  exact congrArg (fun k => moduleStalkComparison Φ (inverseImageStructureRing f)
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj M)
        ((Φ.sheafFiber (A := Type w)).map k
          (e.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((pushforwardModules f).obj M)) z))) hcounit

/-- **The fibre of the counit of Stacks 03D7 on the germ of a section of a direct image**, read
through Stacks 05V5: the previous statement at the germ of a section `t` of `f_*M`, for any
spelling `P` of the comparison of Stacks 05V5 (the equation `hP` identifies it).  Taking the
comparison as a variable lets a caller pass its own name for it without the two being unfolded
and compared. -/
theorem sheafModuleFiberOfCommRing_map_counit_stalkFunctorIso_inv_app_one_tmul_germ
    (P : f.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      Stacks.sheafModuleFiberOfCommRing Ψ Y.O ⋙ ModuleCat.extendScalars (stalkRingMap f Φ Ψ e))
    (hP : P = stalkFunctorIso f Φ Ψ e)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : Y.C)
    (v : Ψ.fiber.obj U) (t : ((pushforwardModules f).obj M).val.obj (Opposite.op U)) :
    (Stacks.sheafModuleFiberOfCommRing Φ X.O).map ((pullbackAdjPushforwardModules f).counit.app M)
        (P.inv.app ((pushforwardModules f).obj M)
        ((1 : Stacks.ringFiber Φ X.O.obj) ⊗ₜ[Stacks.ringFiber Ψ Y.O.obj, stalkRingMap f Φ Ψ e]
          Stacks.toPresheafModuleFiber Ψ ((pushforwardModules f).obj M).val U v t)) =
      moduleStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
        ((Φ.sheafFiber (A := Type w)).map
          (f.toToposHom.adj.counit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
          (e.hom.app (f.toToposHom.pushforward.obj
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
            (Ψ.toPresheafFiber U v (f.toToposHom.pushforward.obj
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)).obj t))) := by
  subst hP
  rw [← moduleStalkComparison_germ Ψ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    ((pushforwardModules f).obj M) U v t]
  exact sheafModuleFiberOfCommRing_map_counit_stalkFunctorIso_inv_app_one_tmul f Φ Ψ e M _

end Stacks.Sheaves.StalkPullback

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section SetLevel

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1)

/-- The unit of the skyscraper adjunction at `ȳ`, at a sheaf of sets `F` on the small étale site
of `Y`: germ formation at `ȳ`, read as a map into the skyscraper with value the fibre `F_ȳ`. -/
abbrev fiberSkyscraperUnit (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    F ⟶ (etaleSitePoint B S hS Y.1 y Y.2).skyscraperSheafFunctor.obj
      ((etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.obj F) :=
  ((etaleSitePoint B S hS Y.1 y Y.2).skyscraperSheafAdjunction (A := Type u)).homEquiv
    F ((etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.obj F) (𝟙 _)

/-- The map `f_*F ⟶ x̄_*(F_ȳ)` whose transpose across the skyscraper adjunction at `x̄` is the
fibre comparison of Stacks 04K2, part (4), followed by the fibre of the counit `f⁻¹f_*F ⟶ F`: the
direct image of the skyscraper unit at `ȳ`, followed by the skyscraper comparison
`AlgebraicGeometry.Space.smallEtaleSkyscraperIso`. -/
abbrev fiberCounitSkyscraperHom (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F ⟶
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).skyscraperSheafFunctor.obj
        ((etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.obj F) :=
  (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
      (fiberSkyscraperUnit B S hS y F) ≫
    (smallEtaleSkyscraperIso B S hS f y).hom.app
      ((etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.obj F)

/-- **The fibre comparison followed by the fibre of the counit is a transpose.**  For a sheaf of
sets `F` on the small étale site of `Y`, the fibre comparison `(f_*F)_x̄ ≅ (f⁻¹f_*F)_ȳ` of
Stacks 04K2, part (4), followed by the fibre at `ȳ` of the counit `f⁻¹f_*F ⟶ F`, is the transpose
of `AlgebraicGeometry.Space.fiberCounitSkyscraperHom`.  This is
`CategoryTheory.Adjunction.conjugate_comp`, the fibre comparison being the conjugate of the
skyscraper comparison. -/
theorem smallEtaleInverseImageFiberIso_hom_app_comp_map_counit
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (smallEtaleInverseImageFiberIso B S hS f y).hom.app
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F) ≫
      (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.map
        ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.counit.app F) =
    (((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).skyscraperSheafAdjunction
          (A := Type u)).homEquiv _ _).symm (fiberCounitSkyscraperHom B S hS f y F) := by
  have h := Adjunction.conjugate_comp (smallEtaleRingedToposHom B S hS f).toToposHom.adj
    ((etaleSitePoint B S hS Y.1 y Y.2).skyscraperSheafAdjunction (A := Type u))
    ((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).skyscraperSheafAdjunction
      (A := Type u))
    (smallEtaleSkyscraperIso B S hS f y)
    (𝟙 ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F))
    (𝟙 ((etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.obj F)) _ (Equiv.apply_symm_apply _ _).symm
  rw [Adjunction.homEquiv_symm_id, Category.comp_id] at h
  exact h

/-- **The set-level germ formula.**  For a sheaf of sets `F` on the small étale site of `Y`, a
section `t` of `f_*F` over an étale chart `U` of `X` (a section of `E⁻¹F` over `U ×_X Y`), a lift
`u` of `x̄` to `U`, and a morphism `h : W ⟶ U ×_X Y` from a chart `W` of `Y` with a lift `w` of `ȳ`
carried to the lift of `ȳ` assigned to `u`, the fibre comparison followed by the fibre of the
counit `f⁻¹f_*F ⟶ F` carries the germ of `t` at `(U, u)` to the germ at `(W, w)` of the
restriction of `t` along `h`, read in `F(W)` through the counit of the comparison equivalence. -/
theorem sheafFiber_map_counit_smallEtaleInverseImageFiberIso_germ
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (hw : (spacesEtaleSitePoint y).fiber.map h w =
      (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u)
    (t : ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj.obj (op U)) :
    (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.map
        ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.counit.app F)
      ((smallEtaleInverseImageFiberIso B S hS f y).hom.app
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F)
        ((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
          ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj t)) =
      (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w F.obj
        (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app F).hom.app
          (op W)
          (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj F).obj.map
            h.op t)) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  let M := (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.obj F
  let H := (spacesEtaleSitePoint y).skyscraperSheafFunctor.obj M
  let E := (smallEtaleComparisonRestriction B S hS Y).asEquivalence
  -- the map of spaces-étale sheaves `E⁻¹F ⟶ H` underlying the direct image of the unit
  let φ : E.inverse.obj F ⟶ H :=
    E.inverse.map (fiberSkyscraperUnit B S hS y F) ≫ E.unitIso.inv.app H
  have hφ : E.functor.map φ = E.counitIso.hom.app F ≫ fiberSkyscraperUnit B S hS y F := by
    have h1 : E.functor.map (E.unitIso.inv.app H) = E.counitIso.hom.app (E.functor.obj H) :=
      (E.counit_app_functor H).symm
    refine (E.functor.map_comp _ _).trans (Eq.trans (congrArg
      (fun k => E.functor.map (E.inverse.map (fiberSkyscraperUnit B S hS y F)) ≫ k) h1) ?_)
    exact E.counitIso.hom.naturality (fiberSkyscraperUnit B S hS y F)
  -- step 1: transpose
  have h1 := ConcreteCategory.congr_hom
    (Point.toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
    ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F) M
    (fiberCounitSkyscraperHom B S hS f y F) U u) t
  rw [← smallEtaleInverseImageFiberIso_hom_app_comp_map_counit] at h1
  refine h1.trans ?_
  -- step 2: the skyscraper comparison
  have h2 := ConcreteCategory.congr_hom (smallEtaleSkyscraperIso_hom_app_π B S hS f y M U u)
    (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
      (fiberSkyscraperUnit B S hS y F)).hom.app (op U) t)
  refine h2.trans ?_
  rw [← hw]
  have h3 := ConcreteCategory.congr_hom
    (Point.skyscraperPresheaf_map_π (spacesEtaleSitePoint y) h M w)
    (φ.hom.app (op ((spacesBaseChange B S hS f).functor.obj
      ((comparisonFunctor B S hS X).obj U))) t)
  refine h3.symm.trans ?_
  have h4 := NatTrans.naturality_apply φ.hom h.op t
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg (Pi.π (fun _ : (spacesEtaleSitePoint y).fiber.obj
    ((comparisonFunctor B S hS Y).obj W) => M) w) h4.symm).trans ?_
  have h5 := congrArg (fun k => k.hom.app (op W)
    (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj F).obj.map h.op t)) hφ
  refine (congrArg (Pi.π (fun _ : (spacesEtaleSitePoint y).fiber.obj
    ((comparisonFunctor B S hS Y).obj W) => M) w) h5).trans ?_
  exact ConcreteCategory.congr_hom
    (Point.skyscraperSheafAdjunction_unit_π (etaleSitePoint B S hS Y.1 y Y.2) F W w) _

/-- The counit of `AlgebraicGeometry.Space.modulePullbackAdjunction`: the pullback of the
comparison `AlgebraicGeometry.Space.modulePushforwardIso`, followed by the counit of Stacks 03D7
for the morphism of small étale ringed topoi. -/
theorem modulePullbackAdjunction_counit_app (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackAdjunction B S hS f).counit.app M =
      (modulePullback B S hS f).map ((modulePushforwardIso B S hS f).inv.app M) ≫
        (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposModulesHom B S hS f)).counit.app M :=
  rfl

/-- **θ through Stacks 05V5.**  On an element of the fibre of the direct image of the morphism
of ringed topoi, carried to the fibre of `f_*M` by the comparison
`AlgebraicGeometry.Space.modulePushforwardIso`, `θ_M` is Stacks 05V5 read backwards on `1 ⊗ m`
followed by the fibre of the counit of Stacks 03D7 for the morphism of ringed topoi. -/
theorem directImageFiberMap_app_map_modulePushforwardIso (M : Modules.{u, u} B S hS Y.1 Y.2)
    (m : (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
      (smallEtaleRingedTopos B S hS X).O).obj
        ((pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj M)) :
    ((directImageFiberMap B S hS f y).app M).hom
        ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O).map ((modulePushforwardIso B S hS f).hom.app M) m) =
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O).map
        ((pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposModulesHom B S hS f)).counit.app M)
        ((modulePullbackFiberIso B S hS f y).inv.app
          ((pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj M)
          ((1 : Stacks.ringFiber (etaleSitePoint B S hS Y.1 y Y.2)
              (smallEtaleRingedTopos B S hS Y).O.obj) ⊗ₜ[Stacks.ringFiber
                (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
                (smallEtaleRingedTopos B S hS X).O.obj, smallEtaleStalkPullbackRingMap B S hS f y]
            m)) := by
  let fibX := Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2) (smallEtaleRingedTopos B S hS X).O
  let fibY := Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
      (smallEtaleRingedTopos B S hS Y).O
  let ext := ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)
  let iso := modulePushforwardIso B S hS f
  let x : ext.obj (fibX.obj ((modulePushforward B S hS f).obj M)) :=
    (1 : Stacks.ringFiber (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O.obj) ⊗ₜ[Stacks.ringFiber
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O.obj, smallEtaleStalkPullbackRingMap B S hS f y]
      (fibX.map (iso.hom.app M) m)
  have h0 : ((directImageFiberMap B S hS f y).app M).hom (fibX.map (iso.hom.app M) m) =
      fibY.map ((modulePullbackAdjunction B S hS f).counit.app M)
        ((modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M) x) := rfl
  refine h0.trans ?_
  refine (congrArg (fun k => fibY.map k
      ((modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M) x))
    (modulePullbackAdjunction_counit_app B S hS f M)).trans ?_
  exact ModuleCat.map_comp_inv_app_one_tmul_map_hom (modulePullback B S hS f) fibX fibY
    (smallEtaleStalkPullbackRingMap B S hS f y) (modulePullbackFiberIso B S hS f y) (iso.app M)
    ((pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposModulesHom B S hS f)).counit.app M) m

/-- The germ of a section of `f_*M` at a lift of `x̄`, read through the comparison
`AlgebraicGeometry.Space.modulePushforwardIso` of the two direct images of modules, which is
the identity on sections. -/
theorem toPresheafModuleFiber_modulePushforward (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (t : ((modulePushforward B S hS f).obj M).val.obj (op U)) :
    Stacks.toPresheafModuleFiber
        (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
        ((modulePushforward B S hS f).obj M).val U u t =
      (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O).map ((modulePushforwardIso B S hS f).hom.app M)
        (Stacks.toPresheafModuleFiber
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          ((pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj M).val U u t) :=
  ((Stacks.toPresheafModuleFiber_naturality _
    ((modulePushforwardIso B S hS f).hom.app M).val U u t).trans
    (congrArg (Stacks.toPresheafModuleFiber
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
      ((modulePushforward B S hS f).obj M).val U u)
      (modulePushforwardIso_hom_app_val_app B S hS f M (op U) t))).symm


end SetLevel

/-- **The germ formula for the comparison `θ : (f_*M)_x̄ ⟶ M_ȳ` of geometric module fibres.**
Let `t` be a section of `f_*M` over an étale chart `U` of `X` — a section of `E⁻¹M` over
`U ×_X Y`, `E` the comparison equivalence of Stacks 03G1 — and `u` a lift of `x̄` to `U`.  For a
chart `W` of `Y` with a lift `w` of `ȳ` and a morphism `h : W ⟶ U ×_X Y` of spaces étale over `Y`
carrying `w` to the lift of `ȳ` that the cartesian square of Stacks 03G2, part (1) assigns to
`u`, `θ_M` carries the germ of `t` at `(U, u)` to the germ at `(W, w)` of the restriction of `t`
along `h`, read in `M(W)` through the counit of `E`. -/
theorem directImageFiberMap_germ {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (hw : (spacesEtaleSitePoint y).fiber.map h w =
      (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u)
    (t : ((modulePushforward B S hS f).obj M).val.obj (op U)) :
    ((directImageFiberMap B S hS f y).app M).hom
        (Stacks.toPresheafModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          ((modulePushforward B S hS f).obj M).val U u t) =
      Stacks.toPresheafModuleFiber (etaleSitePoint B S hS Y.1 y Y.2) M.val W w
        (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
            (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.app (op W)
          (((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
            (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.map
              h.op t)) := by
  refine (congrArg (fun q => ((directImageFiberMap B S hS f y).app M).hom q)
    (toPresheafModuleFiber_modulePushforward B S hS f y M U u t)).trans ?_
  refine (directImageFiberMap_app_map_modulePushforwardIso B S hS f y M _).trans ?_
  open Stacks.Sheaves.StalkPullback in
  refine
    (sheafModuleFiberOfCommRing_map_counit_stalkFunctorIso_inv_app_one_tmul_germ
      (smallEtaleRingedToposModulesHom B S hS f) (etaleSitePoint B S hS Y.1 y Y.2)
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
      (smallEtaleInverseImageFiberIso B S hS f y) (modulePullbackFiberIso B S hS f y) rfl
      M U u t).trans ?_
  refine Eq.trans ?_ (Stacks.Sheaves.StalkTransport.moduleStalkComparison_germ
    (etaleSitePoint B S hS Y.1 y Y.2)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O) M W w _)
  refine congrArg (Stacks.Sheaves.StalkTransport.moduleStalkComparison
    (etaleSitePoint B S hS Y.1 y Y.2)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O) M) ?_
  exact sheafFiber_map_counit_smallEtaleInverseImageFiberIso_germ B S hS f y _ U u W w h hw t

end AlgebraicGeometry.Space

end
