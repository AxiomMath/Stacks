module

public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineRingedTopos
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleObjectZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian

/-!
# Higher direct images of associated modules on the small étale site

Let `f : T ⟶ S` be a quasi-compact quasi-separated morphism of schemes and `𝓕` a quasi-coherent
`𝒪_T`-module.  Descent, Lemma 071N says that `R^i f_{small,*}(𝓕^a) = (R^i f_* 𝓕)^a` on the small
étale site of `S`.  By Stacks 03Q8 the left side is the sheaf associated to the presheaf
`V ↦ H^i(T ×_S V, 𝓕^a)`, so it is enough to identify that presheaf with `(R^i f_* 𝓕)^a` on the
affine objects `V`, naturally in `V`.

This file supplies the sheaf-theoretic half of that argument: on the small étale site of a
scheme, a presheaf which agrees with a sheaf on the affine objects, naturally, sheafifies to that
sheaf.  The affine objects form a dense subsite (Stacks 04HR), so the isomorphism on affine
objects extends to a morphism of presheaves into the sheaf, and that morphism is bijective on
affine objects, which cover every object; it is therefore locally bijective.

## Main results

* `AlgebraicGeometry.SmallEtale.W_of_bijective_app_of_isAffine`: a morphism of presheaves of
  abelian groups which is bijective on the affine objects becomes an isomorphism after
  sheafification.
* `AlgebraicGeometry.SmallEtale.presheafToSheafObjIsoOfAffine`: a presheaf isomorphic to a sheaf
  on the affine objects, naturally, sheafifies to that sheaf.
* `AlgebraicGeometry.SmallEtale.preimageCohomologyPresheafIso`: the presheaf
  `V ↦ H^p(X ×_Y V, E)` of Stacks 03Q8 is the étale cohomology presheaf
  `AlgebraicGeometry.SmallEtale.cohomologyPresheaf` read along base change.
* `AlgebraicGeometry.SmallEtale.higherDirectImageIsoOfAffine` and
  `AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedSheafIsoOfAffine`: `R^p a_* E ≅ H`,
  respectively `R^p a_*(𝓕^a) ≅ 𝓖^a`, from an isomorphism natural in the affine objects.
* `AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedSheafIsoOfZariski`: the same from
  Zariski cohomology of the pullback of `𝓕` to `X ×_Y V`, with the pullback maps of Stacks 01FA,
  through Stacks 03P2 at an object of the small étale site.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section AffineLocal

/-- **A morphism of presheaves on the small étale site which is bijective on the affine objects
becomes an isomorphism after sheafification**: the affine opens of an object lying over affine
opens of `S` cover it, so such a morphism is locally injective and locally surjective. -/
theorem W_of_bijective_app_of_isAffine
    [HasWeakSheafify (topology B S hS) AddCommGrpCat.{w}]
    [(topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P Q : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : P ⟶ Q)
    (hφ : ∀ T : SmallEtale B S hS, AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      Function.Bijective (φ.app (op T))) :
    (topology B S hS).W φ := by
  have hbij : ∀ (T : SmallEtale B S hS) (i : (affineSubordinateCover B S hS T).I₀),
      Function.Bijective (φ.app (op ((affineSubordinateCover B S hS T).X i))) :=
    fun T i => hφ _ i.down.1.2
  have hinj : Presheaf.IsLocallyInjective (topology B S hS) φ := by
    refine ⟨fun {T} x y hxy => ?_⟩
    refine (topology B S hS).superset_covering ?_
      (mem_topology_sieve₀_affineSubordinateCover B S hS T.unop)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    refine (hbij T.unop i).1 ?_
    have hn := fun z => ConcreteCategory.congr_hom
      (φ.naturality ((affineSubordinateCover B S hS T.unop).f i).op) z
    exact (hn x).trans ((congrArg _ hxy).trans (hn y).symm)
  have hsurj : Presheaf.IsLocallySurjective (topology B S hS) φ := by
    refine ⟨fun {T} s => ?_⟩
    refine (topology B S hS).superset_covering ?_
      (mem_topology_sieve₀_affineSubordinateCover B S hS T)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact (hbij T i).2 _
  exact (topology B S hS).W_of_isLocallyBijective φ

/-- The extension to all objects of a morphism of presheaves given on the affine objects of the
small étale site, with target a sheaf, becomes an isomorphism after sheafification as soon as
the given morphism is an isomorphism. -/
theorem W_sheafHom_of_isIso
    [HasWeakSheafify (topology B S hS) AddCommGrpCat.{w}]
    [(topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(SmallAffineEtale.inclusion B S hS).IsCoverDense (topology B S hS)]
    [(SmallAffineEtale.inclusion B S hS).IsLocallyFull (topology B S hS)]
    {P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{w}}
    {H : Sheaf (topology B S hS) AddCommGrpCat.{w}}
    (α : (SmallAffineEtale.inclusion B S hS).op ⋙ P ⟶
      (SmallAffineEtale.inclusion B S hS).op ⋙ H.obj) [IsIso α] :
    (topology B S hS).W (Functor.IsCoverDense.sheafHom α) := by
  refine W_of_bijective_app_of_isAffine B S hS _ fun T hT => ?_
  have h := congrArg (fun t => NatTrans.app t (op (⟨T, hT⟩ : SmallAffineEtale B S hS)))
    (Functor.IsCoverDense.sheafHom_restrict_eq α)
  have hb : Function.Bijective (α.app (op (⟨T, hT⟩ : SmallAffineEtale B S hS))) :=
    ConcreteCategory.bijective_of_isIso _
  rw [← h] at hb
  exact hb

/-- **A presheaf on the small étale site agreeing on affine objects with a sheaf sheafifies to
that sheaf.**  Given an isomorphism, natural on the affine objects, between a presheaf `P` and a
sheaf `H`, the affine objects being a dense subsite (Stacks 04HR) extend it to a morphism of
presheaves `P ⟶ H` which is bijective on affine objects, hence becomes an isomorphism after
sheafification. -/
def presheafToSheafObjIsoOfAffine
    [HasWeakSheafify (topology B S hS) AddCommGrpCat.{w}]
    [(topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{w})
    (H : Sheaf (topology B S hS) AddCommGrpCat.{w})
    (α : (SmallAffineEtale.inclusion B S hS).op ⋙ P ≅
      (SmallAffineEtale.inclusion B S hS).op ⋙ H.obj) :
    (presheafToSheaf (topology B S hS) AddCommGrpCat.{w}).obj P ≅ H :=
  letI := Functor.IsDenseSubsite.isCoverDense (SmallAffineEtale.topology B S hS)
    (topology B S hS) (SmallAffineEtale.inclusion B S hS)
  letI := Functor.IsDenseSubsite.isLocallyFull (SmallAffineEtale.topology B S hS)
    (topology B S hS) (SmallAffineEtale.inclusion B S hS)
  haveI := ((topology B S hS).W_iff _).1 (W_sheafHom_of_isIso B S hS α.hom)
  asIso ((presheafToSheaf (topology B S hS) AddCommGrpCat.{w}).map
      (Functor.IsCoverDense.sheafHom α.hom)) ≪≫
    (asIso ((sheafificationAdjunction (topology B S hS) AddCommGrpCat.{w}).counit)).app H

end AffineLocal

section Cohomology

/-- **The étale cohomology presheaf** `W ↦ H^p(W, E)` of an abelian sheaf on the small étale site,
with the restriction maps `NatTrans.rightDerived` of the restriction of sections. -/
def cohomologyPresheaf (E : Sheaf (topology B S hS) AddCommGrpCat.{u}) (p : ℕ) :
    (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := (((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj W).rightDerived p).obj E
  map h := (NatTrans.rightDerived ((sheafSections (topology B S hS) AddCommGrpCat.{u}).map h)
    p).app E
  map_id W := by
    rw [CategoryTheory.Functor.map_id, NatTrans.rightDerived_id]
    rfl
  map_comp h h' := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.rightDerived_comp]
    rfl

end Cohomology

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.SmallEtale

section HigherDirectImage

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The presheaf `V ↦ H^p(X ×_Y V, E)` of Stacks 03Q8 is the étale cohomology presheaf of `E`
read along small étale base change: its values are identified by
`Stacks.HigherDirectImage.preimageCohomologyPresheafEvaluationIso`, and its restriction maps by
the restriction clause of `Stacks.HigherDirectImage.higherDirectImageComparison`. -/
def preimageCohomologyPresheafIso (E : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u})
    (p : ℕ) :
    Stacks.HigherDirectImage.preimageCohomologyPresheaf.{u, u} B a E p ≅
      (smallEtaleBaseChange B a).op ⋙ cohomologyPresheaf B X.obj X.property E p :=
  NatIso.ofComponents
    (fun V => Stacks.HigherDirectImage.preimageCohomologyPresheafEvaluationIso B a E V.unop p)
    (fun g => (Stacks.HigherDirectImage.higherDirectImageComparison.{u, u} B a p).restriction
      E g.unop)

/-- **`R^p f_* E` from the cohomology over the affine base changes.**  For a morphism `a` of the
big étale site and an abelian sheaf `E` on `X_étale`, an isomorphism, natural in the affine
objects `V` of `Y_étale`, between `H^p(X ×_Y V, E)` and the sections over `V` of a sheaf `H` on
`Y_étale` determines an isomorphism `R^p a_* E ≅ H`: by Stacks 03Q8 the higher direct image is the
sheafification of `V ↦ H^p(X ×_Y V, E)`
(`Stacks.HigherDirectImage.higherDirectImageSheafificationIso`), and a presheaf agreeing with a
sheaf on the affine objects sheafifies to it
(`AlgebraicGeometry.SmallEtale.presheafToSheafObjIsoOfAffine`). -/
def higherDirectImageIsoOfAffine (E : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u})
    (p : ℕ) (H : Sheaf (topology B Y.obj Y.property) AddCommGrpCat.{u})
    (α : (SmallAffineEtale.inclusion B Y.obj Y.property).op ⋙
        (smallEtaleBaseChange B a).op ⋙ cohomologyPresheaf B X.obj X.property E p ≅
      (SmallAffineEtale.inclusion B Y.obj Y.property).op ⋙ H.obj) :
    ((Stacks.HigherDirectImage.pushforward.{u, u} B a).rightDerived p).obj E ≅ H :=
  Stacks.HigherDirectImage.higherDirectImageSheafificationIso B a E p ≪≫
    (presheafToSheaf (topology B Y.obj Y.property) AddCommGrpCat.{u}).mapIso
      (preimageCohomologyPresheafIso B a E p) ≪≫
    presheafToSheafObjIsoOfAffine B Y.obj Y.property _ H α

/-- The abelian sheaf underlying `𝓖^a` is the pullback-sections presheaf
`V ↦ Γ(V, V.hom^* 𝓖)` of Stacks 03DS, by Stacks 070S (2)
(`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf`). -/
def associatedSheafObjIsoSections (S : B.Scheme) (G : S.obj.Modules) [G.IsQuasicoherent] :
    ((associatedSheaf B S).obj G).obj ≅
      (toOver B S.obj S.property).op ⋙ quasiCoherentPresheafFunctor S.obj G :=
  (PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _).mapIso (associatedModuleIsoSectionsSheaf B S.obj S.property G))

/-- **Descent, Lemma 071N, from the comparison over the affine base changes.**  For a morphism
`a` of the big étale site, a quasi-coherent `𝒪_X`-module `𝓕` and a quasi-coherent `𝒪_Y`-module
`𝓖`, an isomorphism, natural in the affine objects `V ⟶ Y` of `Y_étale`, between
`H^p(X ×_Y V, 𝓕^a)` and `Γ(V, V^* 𝓖)` determines `R^p a_*(𝓕^a) ≅ 𝓖^a`. -/
def higherDirectImageAssociatedSheafIsoOfAffine (𝓕 : X.obj.Modules) (p : ℕ)
    (G : Y.obj.Modules) [G.IsQuasicoherent]
    (β : (SmallAffineEtale.inclusion B Y.obj Y.property).op ⋙
        (smallEtaleBaseChange B a).op ⋙
          cohomologyPresheaf B X.obj X.property ((associatedSheaf B X).obj 𝓕) p ≅
      (SmallAffineEtale.inclusion B Y.obj Y.property).op ⋙
        (toOver B Y.obj Y.property).op ⋙ quasiCoherentPresheafFunctor Y.obj G) :
    ((Stacks.HigherDirectImage.pushforward.{u, u} B a).rightDerived p).obj
        ((associatedSheaf B X).obj 𝓕) ≅ (associatedSheaf B Y).obj G :=
  higherDirectImageIsoOfAffine B a _ p _
    (β ≪≫ Functor.isoWhiskerLeft _ (associatedSheafObjIsoSections B Y G).symm)

/-- **Descent, Lemma 071N, from the Zariski comparison over the affine base changes.**  For a
morphism `a` of the big étale site, a quasi-coherent `𝒪_X`-module `𝓕` and a quasi-coherent
`𝒪_Y`-module `𝓖`, isomorphisms `Θ_V : H^p(X ×_Y V, 𝓕|) ≅ Γ(V, V^* 𝓖)` for the affine objects `V`
of `Y_étale`, the left side being Zariski cohomology of the pullback of `𝓕` to the scheme
`X ×_Y V`, which carry the pullback maps of Zariski cohomology of Stacks 01FA
(`AlgebraicGeometry.SmallEtale.objPullbackCohomologyMap`) to the pullback of sections, determine
`R^p a_*(𝓕^a) ≅ 𝓖^a`.  The étale cohomology over `X ×_Y V` is identified with the Zariski
cohomology by Stacks 03P2 at an object of the small étale site
(`AlgebraicGeometry.SmallEtale.objCohomologyAssociatedModuleIso`), naturally in the object. -/
def higherDirectImageAssociatedSheafIsoOfZariski (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] (p : ℕ)
    (G : Y.obj.Modules) [G.IsQuasicoherent]
    (Θ : ∀ V : SmallAffineEtale B Y.obj Y.property,
      (((sheafSections (Opens.grothendieckTopology
          ↥(objScheme B X.obj X.property ((smallEtaleBaseChange B a).obj V.obj)))
          AddCommGrpCat.{u}).obj (op ⊤)).rightDerived p).obj
        ((SheafOfModules.toSheaf _).obj ((Scheme.Modules.pullback
          (objHom B X.obj X.property ((smallEtaleBaseChange B a).obj V.obj))).obj 𝓕)) ≅
        AddCommGrpCat.of Γ((Scheme.Modules.pullback ((toOver B Y.obj Y.property).obj V.obj).hom).obj
          G, ⊤))
    (hΘ : ∀ {V₁ V₂ : SmallAffineEtale B Y.obj Y.property} (g : V₁ ⟶ V₂),
      objPullbackCohomologyMap ((smallEtaleBaseChange B a).map
          ((SmallAffineEtale.inclusion B Y.obj Y.property).map g)) 𝓕 p ≫ (Θ V₁).hom =
        (Θ V₂).hom ≫ pullbackSectionsMap G ((toOver B Y.obj Y.property).map
          ((SmallAffineEtale.inclusion B Y.obj Y.property).map g))) :
    ((Stacks.HigherDirectImage.pushforward.{u, u} B a).rightDerived p).obj
        ((associatedSheaf B X).obj 𝓕) ≅ (associatedSheaf B Y).obj G :=
  higherDirectImageAssociatedSheafIsoOfAffine B a 𝓕 p G
    (NatIso.ofComponents
      (fun V => (objCohomologyAssociatedModuleIso B X.obj X.property
          ((smallEtaleBaseChange B a).obj V.unop.obj) 𝓕 p).symm ≪≫ Θ V.unop)
      (fun {V₁ V₂} g => by
        have h2 := objCohomologyAssociatedModuleIso_hom_naturality ((smallEtaleBaseChange B a).map
          ((SmallAffineEtale.inclusion B Y.obj Y.property).map g.unop)) 𝓕 p
        have key : (NatTrans.rightDerived ((sheafSections (topology B X.obj X.property)
              AddCommGrpCat.{u}).map ((smallEtaleBaseChange B a).map
                ((SmallAffineEtale.inclusion B Y.obj Y.property).map g.unop)).op) p).app
              ((SheafOfModules.toSheaf _).obj ((associatedModule B X.obj X.property).obj 𝓕)) ≫
            (objCohomologyAssociatedModuleIso B X.obj X.property
              ((smallEtaleBaseChange B a).obj V₂.unop.obj) 𝓕 p).inv =
          (objCohomologyAssociatedModuleIso B X.obj X.property
              ((smallEtaleBaseChange B a).obj V₁.unop.obj) 𝓕 p).inv ≫
            objPullbackCohomologyMap ((smallEtaleBaseChange B a).map
              ((SmallAffineEtale.inclusion B Y.obj Y.property).map g.unop)) 𝓕 p := by
          rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
          exact h2
        exact (Category.assoc _ _ _).symm.trans ((key =≫ _).trans ((Category.assoc _ _ _).trans
          ((_ ≫= hΘ g.unop).trans (Category.assoc _ _ _).symm)))))

end HigherDirectImage
end AlgebraicGeometry.SmallEtale
