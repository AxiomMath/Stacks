module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsFactorFourReduction

/-!
# The identification of sections of Stacks 076T, from the sheafified comparison

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean` and the
files built on it identify, for a locally quasi-coherent `F`, the sections `F(z)` at an arrow
`φ : z ⟶ x` lying over `g : W ⟶ U` with the sections of `g^*𝓕` (where `𝓕^a ≅ F|_{U_ét}`), and
prove that this identification is compatible with composition. They ask that the comparison map
`c_φ` of Stacks 06WC be an isomorphism of *presheaves*, which is more than Stacks 0762 asks.

This file runs the same construction from the hypothesis the source makes: that the morphism of
sheaves `f_{small}^*(F|_{U_ét}) ⟶ F|_{W_ét}` induced by `c_φ`,
`AlgebraicGeometry.Stack.sheafifiedRestrictComparison`, is an isomorphism. The identification
`F|_{W_ét} ≅ (g^*𝓕)^a` is then the inverse of the morphism of sheaves
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`, and the composition law of the library, which
is proved at the level of sheaves (`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp`),
applies unchanged. Every declaration here is the library's of the same name without the suffix
`OfSheafified`, with the hypothesis `IsIso (restrictModulePullbackComparison ..)` replaced by
`IsIso (sheafifiedRestrictComparison ..)`, which it implies.

## Main definitions

* `AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfSheafified`, `liftedSectionsIsoOfSheafified`,
  `overPostSectionsIsoOfSheafified`, `overPostSectionsMapOfSheafified`.

## Main results

* `AlgebraicGeometry.Stack.liftedSectionsCocycleOfSheafified_of_factorFourSquare` and
  `AlgebraicGeometry.Stack.liftedSectionsFactorFourSquareOfSheafified_of_compat`: the cocycle
  condition, from the compatibility the library proves
  (`AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat`).

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Sections

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

/-- **The restriction `F|_{W_ét}` is the associated module of `g^*𝓕`.** For an arrow
`φ : z ⟶ x` of `𝒳` lying over a morphism of schemes `g : W ⟶ U` along which the comparison map
`c_φ` of **Stacks 06WC** induces an isomorphism of sheaves, and for a quasi-coherent `𝒪_U`-module
`𝓕` with
`𝓕^a ≅ F|_{U_ét}`, the restriction of `F` to the small étale site of `W` is `(g^*𝓕)^a`.

It is the inverse of the morphism of sheaves `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`,
which is the identification of Stacks 03LC (1) read backwards, the sheafified Stacks 06WC pullback
of `𝓕^a ≅ F|_{U_ét}`, and the sheafified comparison, all three invertible. -/
noncomputable def liftedSmallEtaleIsoOfSheafified {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose)) :
    (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf ≅
      ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val.presheaf :=
  haveI : IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx (hlqc.2 z).choose eU.hom) :=
    IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' (Functor.map_isIso _ eU.hom) hiso)
  ((PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).mapIso
      (asIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx (hlqc.2 z).choose
        eU.hom)))).symm

/-- **`AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfSheafified` is inverse to
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`**, by construction. -/
theorem liftedSmallEtaleIsoOfSheafified_hom_comp_sheafInv {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose)) :
    (liftedSmallEtaleIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (PresheafOfModules.toPresheaf _).map
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
            (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)) =
      𝟙 _ :=
  Eq.trans (by rfl) (liftedSmallEtaleIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU
    hiso).hom_inv_id

/-- **The identification of the sections of `F` at `z` with the sections of the presheaf of
Stacks 03DS of `𝓕` over `g`.** For an arrow `φ : z ⟶ x` lying over `g : W ⟶ U` along which the
comparison map of **Stacks 06WC** induces an isomorphism of sheaves, `F(z) = Γ(W, g^*𝓕)`.

`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso` reads `F(z)` as the sections of
`F|_{W_ét}` over the final object of the small étale site of `W`,
`AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfSheafified` identifies that restriction with
`(g^*𝓕)^a`,
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` reads the latter's sections as the
sections of the presheaf of Stacks 03DS of `g^*𝓕`, and
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` reads those as the sections of the presheaf of
Stacks 03DS of `𝓕` over `g`. -/
noncomputable def liftedSectionsIsoOfSheafified {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose)) :
    F.presheaf.obj (op z) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj
        (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) := by
  letI := h𝓕
  refine (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).symm ≪≫
    (liftedSmallEtaleIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).app
      (op (smallEtaleFinal B E h S hS p z)) ≪≫
    (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).app
      (op (smallEtaleFinal B E h S hS p z)) ≪≫
    ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕
        (Over.mk (B.inclusion.map (p.map φ).left))).app
      (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z)))).symm ≪≫
    (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).mapIso
      (Iso.op (Over.isoMk (Iso.refl _) ?_))
  simp [smallEtaleFinal, SmallEtale.final, Over.post]

/-- **The identification of the sections, at an object of the big fppf site of `U`.**
`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified` at the arrow of `𝒳` which the localization
equivalence of **Stacks 06W0** produces over the object, followed by the restriction map along
the counit of that equivalence. -/
noncomputable def overPostSectionsIsoOfSheafified (x : 𝒳)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (overPostLiftHom B S hS p hp x V)
        (hlqc.2 _).choose)) :
    F.presheaf.obj (op (overPostLiftObj B S hS p hp x V)) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj (op V) :=
  liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V) 𝓕 h𝓕 hMx
      eU hiso ≪≫
    (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).mapIso
      (Iso.op (overPostLiftIso B S hS p hp x V).symm)

/-! ### The compatibility with composition which is carried -/

/-- **The one hypothesis carried: `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified` is
compatible with
composition of arrows of `𝒳`.**

This is a *stand-in*, not a result. It is the cocycle condition for the composite identification
of `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`, stated in the only form the assembly of
this
file consumes: at a composable pair of arrows both of which lie over a morphism of schemes along
which the comparison map of **Stacks 06WC** induces an isomorphism of sheaves. Four of its five
factors are
available — see the discussion at the head of this file — and the fifth, the compatibility of
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` with composition of arrows,
is what nothing in this development states. No Stacks tag may be registered on anything which
carries it. -/
def LiftedSectionsCocycleOfSheafified : Prop :=
  ∀ (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) {x : 𝒳}
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    {z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x) (hφ' : φ' = ψ ≫ φ)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose))
    (hiso' : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ' (hlqc.2 _).choose)),
    F.presheaf.map ψ.op ≫
        (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx eU hiso').hom =
      (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map ψ)
            (by simp [hφ']) :
            Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ') ⟶
              Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ)).op

/-- **Over the carried cocycle, the identification commutes with the restriction maps of the big
fppf site of `U`.** For an arrow `r : V' ⟶ V` of the big fppf site of the scheme below `x`,
restricting along `r` after identifying is identifying after restricting along the arrow of `𝒳`
which the localization equivalence of **Stacks 06W0** produces over `r`.

The cocycle supplies the square for `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`; what
is added
here is the bookkeeping of the counit of the localization equivalence, which is its naturality
pushed forward along the inclusion of the big fppf site into the schemes over `U`. -/
theorem overPostSectionsIsoOfSheafified_naturality (hcoc : LiftedSectionsCocycleOfSheafified B E h
    S hS p hp) (x : 𝒳)
    {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (overPostLiftHom B S hS p hp x V)
        (hlqc.2 _).choose))
    (hiso' : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (overPostLiftHom B S hS p hp x
        V') (hlqc.2 _).choose)) :
    F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op ≫
        (overPostSectionsIsoOfSheafified B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso').hom =
      (overPostSectionsIsoOfSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op := by
  have hφ' : overPostLiftHom B S hS p hp x V' =
      ((overPostEquivalence B S hS p hp x).inverse.map r).left ≫
        overPostLiftHom B S hS p hp x V :=
    (Over.w ((overPostEquivalence B S hS p hp x).inverse.map r)).symm
  have hcell := hcoc F hlqc 𝓕 h𝓕 hMx eU
    (((overPostEquivalence B S hS p hp x).inverse.map r).left)
    (overPostLiftHom B S hS p hp x V) (overPostLiftHom B S hS p hp x V') hφ' hiso hiso'
  have htail : ∀ (m : Over.mk ((p ⋙ Over.forget (B.obj hS)).map
        (overPostLiftHom B S hS p hp x V')) ⟶
      Over.mk ((p ⋙ Over.forget (B.obj hS)).map (overPostLiftHom B S hS p hp x V))),
      m.left = (p ⋙ Over.forget (B.obj hS)).map
          (((overPostEquivalence B S hS p hp x).inverse.map r).left) →
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map m.op ≫
          (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
            (Iso.op (overPostLiftIso B S hS p hp x V').symm).hom =
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
            (Iso.op (overPostLiftIso B S hS p hp x V).symm).hom ≫
          (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op := by
    intro m hm
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map (Quiver.Hom.unop_inj ?_)
    simp only [unop_comp, Iso.op, Iso.symm_hom, Quiver.Hom.unop_op]
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact overPostLiftIso_naturality B S hS p hp x r m hm
  simp only [overPostSectionsIsoOfSheafified, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hcell, Category.assoc, htail _ rfl, Category.assoc]


/-- The identification of `AlgebraicGeometry.Stack.overPostSectionsIsoOfSheafified` read as a map
between
the sections of the two presheaves the reduced sheaf condition is about. -/
noncomputable def overPostSectionsMapOfSheafified
    (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (overPostLiftHom B S hS p hp x V)
        (hlqc.2 _).choose))
    (M : AddCommGrpCat.{u}) :
    (overPostTransportSections B S hS p hp F x M).obj (op V) →
      (overPostSectionsTypes B S hS p x 𝓕 h𝓕 M).obj (op V) :=
  fun s => ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIsoOfSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso)).hom s

/-- **`AlgebraicGeometry.Stack.overPostSectionsMapOfSheafified` is a bijection**, the
identification it comes
from being an isomorphism. -/
theorem overPostSectionsMapOfSheafified_bijective
    (x : 𝒳) (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (overPostLiftHom B S hS p hp x V)
        (hlqc.2 _).choose))
    (M : AddCommGrpCat.{u}) :
    Function.Bijective (overPostSectionsMapOfSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso
        M) :=
  ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIsoOfSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso)).toEquiv.bijective

include hlqc in
/-- **Over the carried cocycle, `AlgebraicGeometry.Stack.overPostSectionsMapOfSheafified` commutes
with the
restriction maps of the big fppf site of `U`.**
`AlgebraicGeometry.Stack.overPostSectionsIsoOfSheafified_naturality` on a section. -/
theorem overPostSectionsMapOfSheafified_naturality (hcoc : LiftedSectionsCocycleOfSheafified B E h
    S hS p hp)
    (x : 𝒳) {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (overPostLiftHom B S hS p hp x V)
        (hlqc.2 _).choose))
    (hiso' : IsIso (sheafifiedRestrictComparison B E h S hS p hp F (overPostLiftHom B S hS p hp x
        V') (hlqc.2 _).choose))
    (M : AddCommGrpCat.{u})
    (s : (overPostTransportSections B S hS p hp F x M).obj (op V)) :
    overPostSectionsMapOfSheafified B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso' M
        ((overPostTransportSections B S hS p hp F x M).map r.op s) =
      (overPostSectionsTypes B S hS p x 𝓕 h𝓕 M).map r.op
        (overPostSectionsMapOfSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso M s) := by
  have key := overPostSectionsIsoOfSheafified_naturality B E h S hS p hp F hlqc hcoc x r 𝓕 h𝓕 hMx
      eU hiso hiso'
  show (s ≫ F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op) ≫
      (overPostSectionsIsoOfSheafified B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso').hom =
    (s ≫ (overPostSectionsIsoOfSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso).hom) ≫
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => s ≫ t) key).trans (Category.assoc _ _ _).symm)


end Sections

section Cocycle

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

/-- The composite of the first four factors of
`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`:
the sections of `F` at `z` read as the sections of the presheaf of **Stacks 03DS** of `g^*𝓕`
over the final object of the small étale site of `W`. -/
noncomputable def liftedSectionsUpperOfSheafified {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) [h𝓕 : 𝓕.IsQuasicoherent]
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose)) :
    F.presheaf.obj (op z) ⟶
      (quasiCoherentPresheafFunctor (p.obj z).left.1
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).obj
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) :=
  (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).inv ≫
    (liftedSmallEtaleIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom.app
      (op (smallEtaleFinal B E h S hS p z)) ≫
    (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
      (op (smallEtaleFinal B E h S hS p z))

/-- `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified` is
`AlgebraicGeometry.Stack.liftedSectionsUpperOfSheafified` followed by the base-change
identification of
**Stacks 03DS**, read backwards, and the restriction map along the arrow of `Sch/U` which
identifies `W / U` with the final object of the small étale site of `W` seen over `U`. -/
theorem liftedSectionsIsoOfSheafified_hom_eq {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose)) :
    letI := h𝓕
    ∃ e : (Over.mk (B.inclusion.map (p.map φ).left) : Over (p.obj x).left.1) ⟶
        (Over.map (B.inclusion.map (p.map φ).left)).obj
          ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
            (smallEtaleFinal B E h S hS p z)),
      e.left = 𝟙 _ ∧
      (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom =
        liftedSectionsUpperOfSheafified B E h S hS p hp F hlqc φ 𝓕 hMx eU hiso ≫
          ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕
              (Over.mk (B.inclusion.map (p.map φ).left))).inv.app
            (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
              (smallEtaleFinal B E h S hS p z))) ≫
            (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map e.op) := by
  let := h𝓕
  refine ⟨(Over.isoMk (Iso.refl _)
    (by simp)).hom, rfl, ?_⟩
  unfold liftedSectionsIsoOfSheafified liftedSectionsUpperOfSheafified
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rfl

/-- **Stand-in, not a result: the composition law for factor 4 of
`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`**, in the only form the assembly of the
cocycle
condition consumes.

Factors 1, 2, 3, 4 and 5a of the identification compose into
`AlgebraicGeometry.Stack.liftedSectionsUpperOfSheafified`; of their composition laws every one but
factor
4's is available. This is the square those laws paste into: at a composable pair of arrows both
lying over a morphism along which the comparison map of **Stacks 06WC** induces an isomorphism
of sheaves,
restriction of `F` along `ψ` followed by the identification at `φ'` is the identification at
`φ` followed by the right-hand vertical of factor 5's square — restriction along the arrow `n`
of `Sch/W`, base change along the morphism `k` below `ψ`, and the composition isomorphism of the
pullback pseudofunctor.

No Stacks tag may be registered on anything which carries this. -/
def LiftedSectionsFactorFourSquareOfSheafified : Prop :=
  ∀ (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) {x : 𝒳}
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    {z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x) (hφ' : φ' = ψ ≫ φ)
    (hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose))
    (hiso' : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ' (hlqc.2 _).choose))
    (n : (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
          (smallEtaleFinal B E h S hS p z')) ⟶
      (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z))
    (hn : n.left = B.inclusion.map (p.map ψ).left),
    letI := h𝓕
    F.presheaf.map ψ.op ≫ liftedSectionsUpperOfSheafified B E h S hS p hp F hlqc φ' 𝓕 hMx eU hiso' =
      liftedSectionsUpperOfSheafified B E h S hS p hp F hlqc φ 𝓕 hMx eU hiso ≫
        (quasiCoherentPresheafFunctor (p.obj z).left.1
              ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).map n.op ≫
          (Stacks.Sites.quasiCoherentPresheafBaseChangeIso
              ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)
              (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
            (op ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
              (smallEtaleFinal B E h S hS p z'))) ≫
          (Stacks.Sites.pullbackCompSectionsIsoOfEq 𝓕 (B.inclusion.map (p.map φ).left)
              (B.inclusion.map (p.map ψ).left) (B.inclusion.map (p.map φ').left) hkg
              ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
                (smallEtaleFinal B E h S hS p z'))).hom

/-- **The cocycle condition for `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`, over the
factor-4
stand-in.** Pasting the stand-in square of
`AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareOfSheafified` onto the composition square of
`Stacks.Sites.baseChangeCompIso_inv_restriction` gives the hypothesis
`AlgebraicGeometry.Stack.LiftedSectionsCocycleOfSheafified` which
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean`
carries, with no further compatibility. -/
theorem liftedSectionsCocycleOfSheafified_at_belowArrowSite
    (hf4 : LiftedSectionsFactorFourSquareOfSheafified B E h S hS p hp) {x : 𝒳}
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    {z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x) (hφ' : φ' = ψ ≫ φ)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose))
    (hiso' : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ' (hlqc.2 _).choose)) :
    F.presheaf.map ψ.op ≫
        (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx eU hiso').hom =
      (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (belowArrowSite B S hS p ψ φ φ' hφ').op := by
  have paste_squares {C : Type _} [Category C] {P P' Q Q' R T T' : C}
      (fψ : P ⟶ P') (u : P ⟶ Q) (u' : P' ⟶ Q') (v : Q ⟶ Q')
      (dinv : Q ⟶ R) (dhom : R ⟶ Q) (ee : R ⟶ T) (tail' : Q' ⟶ T') (mapme : R ⟶ T')
      (mm : T ⟶ T')
      (hA : fψ ≫ u' = u ≫ v)
      (hB : dhom ≫ v ≫ tail' = mapme)
      (hC : mapme = ee ≫ mm)
      (hD : dinv ≫ dhom = 𝟙 Q) :
      fψ ≫ u' ≫ tail' = (u ≫ dinv ≫ ee) ≫ mm := by
    rw [← Category.assoc, hA, Category.assoc, Category.assoc, Category.assoc, ← hC, ← hB,
      ← Category.assoc dinv dhom, hD, Category.id_comp]
  let := h𝓕
  have hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left := by
    rw [hφ', p.map_comp]
    exact B.inclusion.map_comp _ _
  obtain ⟨e, he, hfac⟩ := liftedSectionsIsoOfSheafified_hom_eq B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU
      hiso
  obtain ⟨e', he', hfac'⟩ := liftedSectionsIsoOfSheafified_hom_eq B E h S hS p hp F hlqc φ' 𝓕 h𝓕
      hMx eU hiso'
  have hmm : (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
        (belowArrowSite B S hS p ψ φ φ' hφ').op =
      (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
        (belowArrow B S hS p ψ φ φ' hkg).op := rfl
  rw [hfac, hfac', hmm]
  have hA := hf4 F hlqc 𝓕 h𝓕 hMx eU ψ φ φ' hφ' hkg hiso hiso'
    (finalBaseChangeArrow B E h S hS p ψ) rfl
  have hB := Stacks.Sites.baseChangeCompIso_inv_restriction_of_eq 𝓕
    (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map ψ).left)
    (B.inclusion.map (p.map φ').left) hkg
    (A := (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      (smallEtaleFinal B E h S hS p z))
    (A' := (SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
      (smallEtaleFinal B E h S hS p z'))
    (finalBaseChangeArrow B E h S hS p ψ) e e'
    (belowArrow B S hS p ψ φ φ' hkg)
    (by rw [he, he']; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hC : (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
        (belowArrow B S hS p ψ φ φ' hkg ≫ e).op =
      (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map e.op ≫
        (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
          (belowArrow B S hS p ψ φ φ' hkg).op := by
    rw [op_comp, Functor.map_comp]
  exact paste_squares _ _ _ _ _ _ _ _ _ _ hA hB hC (Iso.inv_hom_id_app _ _)

/-- **The cocycle condition for `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`, over the
factor-4
stand-in.** -/
theorem liftedSectionsCocycleOfSheafified_of_factorFourSquare
    (hf4 : LiftedSectionsFactorFourSquareOfSheafified B E h S hS p hp) :
    LiftedSectionsCocycleOfSheafified B E h S hS p hp := by
  intro F hlqc x 𝓕 h𝓕 hMx eU z' z ψ φ φ' hφ' hiso hiso'
  exact liftedSectionsCocycleOfSheafified_at_belowArrowSite B E h S hS p hp F hlqc hf4 𝓕 h𝓕 hMx eU
      ψ φ φ'
    hφ' hiso hiso'


end Cocycle

/-- **The factor-four square of Stacks 076T, over the compatibility of the two base changes on
sections.**  `AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareOfSheafified` — and hence, by
`AlgebraicGeometry.Stack.liftedSectionsCocycleOfSheafified_of_factorFourSquare`, the cocycle
condition
`AlgebraicGeometry.Stack.LiftedSectionsCocycleOfSheafified` — follows from
`AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat` alone.

The proof strips the invertible head of the identification, replaces its inverse by
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` using
`AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfSheafified_hom_comp_sheafInv`, reads factors 3 and 4
on
sections at the final object with
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp_sheafifiedFactor`, rewrites the
composition law of factors 2, 3 and 4 at sheaf level by
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp`, and crosses the associated-module
vertical by `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module`.
What is left over is exactly the carried compatibility. -/
theorem liftedSectionsFactorFourSquareOfSheafified_of_compat
    (hc : AssociatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp) :
    LiftedSectionsFactorFourSquareOfSheafified B E h S hS p hp := by
  have factor_four_algebra {C : Type _} [Category C]
      {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ O₁₃ : C}
      (sinv : O₁ ⟶ O₂) (fzh : O₂ ⟶ O₃) (fψ : O₃ ⟶ O₄) (fzi' : O₄ ⟶ O₅)
      (lam' : O₅ ⟶ O₆) (ap' : O₆ ⟶ O₇)
      (uu : O₁ ⟶ O₈) (eta : O₈ ⟶ O₉) (bc : O₉ ⟶ O₁₀) (pf : O₁₀ ⟶ O₆) (si' : O₆ ⟶ O₅)
      (apQ : O₁₀ ⟶ O₁₁) (pfs : O₁₁ ⟶ O₇) (apB : O₁ ⟶ O₁₂) (nmap : O₁₂ ⟶ O₁₃) (qcbc : O₁₃ ⟶ O₁₁)
      (hfinal : uu ≫ eta ≫ bc ≫ pf ≫ si' = sinv ≫ fzh ≫ fψ ≫ fzi')
      (hsi : si' ≫ lam' = 𝟙 O₆)
      (hnat : pf ≫ ap' = apQ ≫ pfs)
      (hcompat : uu ≫ eta ≫ bc ≫ apQ = apB ≫ nmap ≫ qcbc) :
      sinv ≫ fzh ≫ fψ ≫ fzi' ≫ lam' ≫ ap' = apB ≫ nmap ≫ qcbc ≫ pfs := by
    have e1 : uu ≫ eta ≫ bc ≫ pf ≫ si' ≫ lam' ≫ ap' =
        sinv ≫ fzh ≫ fψ ≫ fzi' ≫ lam' ≫ ap' := by
      have hf := congrArg (fun t => t ≫ lam' ≫ ap') hfinal
      simpa only [Category.assoc] using hf
    rw [← e1, ← Category.assoc si' lam' ap', hsi, Category.id_comp, hnat]
    have hcc := congrArg (fun t => t ≫ pfs) hcompat
    simpa only [Category.assoc] using hcc
  have split_prefix {C : Type _} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
      (fzh : O₂ ⟶ O₁) (fzi : O₁ ⟶ O₂) (lh : O₂ ⟶ O₃) (li : O₃ ⟶ O₂)
      (t : O₁ ⟶ O₄) (ap : O₃ ⟶ O₅) (rest : O₅ ⟶ O₄)
      (hfz : fzi ≫ fzh = 𝟙 O₁) (hl : lh ≫ li = 𝟙 O₂)
      (key : li ≫ fzh ≫ t = ap ≫ rest) :
      t = (fzi ≫ lh ≫ ap) ≫ rest := by
    rw [Category.assoc, Category.assoc, ← key, ← Category.assoc lh li, hl, Category.id_comp,
      ← Category.assoc, hfz, Category.id_comp]
  intro F hlqcF x 𝓕 h𝓕 hMx eU z' z ψ φ φ' hφ' hkg hiso hiso' n hn
  let := h𝓕
  subst hφ'
  have hMz := (hlqcF.2 z).choose
  have hMz' := (hlqcF.2 z').choose
  rw [Stacks.Sites.pullbackCompSectionsIsoOfEq_hom]
  unfold liftedSectionsUpperOfSheafified
  -- `h3`: the composition law for factors 2, 3, 4 at sheaf level, with factor 4 peeled off
  have h3 : (PresheafOfModules.sheafification
            (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
              (contains_base B E h S hS p z')).obj)).map
            ((PresheafOfModules.pullback.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                (etaleTopology_le_topology B))).map
              ((SheafOfModules.forget _).map
                (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom))) ≫
          sheafifiedRestrictComparison B E h S hS p hp F ψ hMz' =
        (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ
            ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom ≫
          (SmallEtale.associatedModule E (p.obj z').left.1
              (contains_base B E h S hS p z')).map
            ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
              (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left)
              (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕) ≫
          liftedSmallEtaleSheafInv B E h S hS p hp F (ψ ≫ φ) 𝓕 hMx hMz' eU.hom := by
    rw [← liftedSmallEtaleSheafInv_comp B E h S hS p hp F ψ φ 𝓕 hMx hMz hMz' eU.hom,
      liftedSmallEtaleSheafInv_eq B E h S hS p hp F ψ
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) hMz hMz'
        (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom),
      Iso.hom_inv_id_assoc]
    rfl
  -- `e1`: factors 3 and 4 read on sections at the final object
  have e1 := smallEtaleFinalPullbackUnit_comp_sheafifiedFactor B E h S hS p hp ψ F hMz'
    ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val
    ((SheafOfModules.forget _).map
      (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom))
  -- `uu ≫ _`, the common prefix of the two spellings of factors 3 and 4 on sections
  have h4 := congrArg (fun t =>
      smallEtaleFinalPullbackUnit B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ
          ((SmallEtale.associatedModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj
            ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val ≫
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                  (contains_base B E h S hS p z')).obj)).unit.app
              ((PresheafOfModules.pullback.{u}
                (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                  (etaleTopology_le_topology B))).obj
                ((SmallEtale.associatedModule E (p.obj z).left.1
                  (contains_base B E h S hS p z)).obj
                  ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val) ≫
            (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map t)).app
          (op (smallEtaleFinal B E h S hS p z'))) h3
  have h5 :
      smallEtaleFinalPullbackUnit B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ
            ((SmallEtale.associatedModule E (p.obj z).left.1
              (contains_base B E h S hS p z)).obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val ≫
          ((PresheafOfModules.toPresheaf _).map
            ((PresheafOfModules.sheafificationAdjunction
                  (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                    (contains_base B E h S hS p z')).obj)).unit.app
                ((PresheafOfModules.pullback.{u}
                  (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                    (etaleTopology_le_topology B))).obj
                  ((SmallEtale.associatedModule E (p.obj z).left.1
                    (contains_base B E h S hS p z)).obj
                    ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val) ≫
              (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
                ((associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
                    (etaleTopology_le_topology B) ψ
                    ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom ≫
                  (SmallEtale.associatedModule E (p.obj z').left.1
                      (contains_base B E h S hS p z')).map
                    ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
                      (B.inclusion.map (p.map φ).left)
                      (B.inclusion.map (p.map (ψ ≫ φ)).left)
                      (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕) ≫
                  liftedSmallEtaleSheafInv B E h S hS p hp F (ψ ≫ φ) 𝓕 hMx hMz'
                    eU.hom))).app
            (op (smallEtaleFinal B E h S hS p z')) =
        smallEtaleFinalPullbackUnit B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ
            ((SmallEtale.associatedModule E (p.obj z).left.1
              (contains_base B E h S hS p z)).obj
              ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val ≫
          ((PresheafOfModules.toPresheaf _).map
              ((PresheafOfModules.sheafificationAdjunction
                    (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                      (contains_base B E h S hS p z')).obj)).unit.app
                  ((PresheafOfModules.pullback.{u}
                    (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                      (etaleTopology_le_topology B))).obj
                    ((SmallEtale.associatedModule E (p.obj z).left.1
                      (contains_base B E h S hS p z)).obj
                      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj
                        𝓕)).val))).app
              (op (smallEtaleFinal B E h S hS p z')) ≫
            ((PresheafOfModules.toPresheaf _).map
                ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
                  (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
                    (etaleTopology_le_topology B) ψ
                    ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj
                      𝓕)).hom)).app
              (op (smallEtaleFinal B E h S hS p z')) ≫
            ((PresheafOfModules.toPresheaf _).map
                ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
                  ((SmallEtale.associatedModule E (p.obj z').left.1
                      (contains_base B E h S hS p z')).map
                    ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
                      (B.inclusion.map (p.map φ).left)
                      (B.inclusion.map (p.map (ψ ≫ φ)).left)
                      (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕)))).app
              (op (smallEtaleFinal B E h S hS p z')) ≫
            ((PresheafOfModules.toPresheaf _).map
                ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
                  (liftedSmallEtaleSheafInv B E h S hS p hp F (ψ ≫ φ) 𝓕 hMx hMz'
                    eU.hom))).app
              (op (smallEtaleFinal B E h S hS p z')) := by
    simp only [Functor.map_comp, NatTrans.comp_app]
    rfl
  have hfinal := h5.symm.trans (h4.symm.trans e1)
  -- `hA`: factors 2, 3, 4 are inverse to the identification, at `ψ ≫ φ`
  have hA := NatTrans.congr_app (liftedSmallEtaleIsoOfSheafified_hom_comp_sheafInv B E h S hS p hp
      F hlqcF
    (ψ ≫ φ) 𝓕 h𝓕 hMx hMz' eU hiso') (op (smallEtaleFinal B E h S hS p z'))
  simp only [NatTrans.id_app] at hA
  have hsi := (Iso.comp_hom_eq_id _).2 ((Iso.hom_comp_eq_id
    ((liftedSmallEtaleIsoOfSheafified B E h S hS p hp F hlqcF (ψ ≫ φ) 𝓕 h𝓕 hMx eU hiso').app
      (op (smallEtaleFinal B E h S hS p z')))).1 hA)
  -- `hnat`: naturality of the Stacks 070S identification in the module
  have : SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left) ⋙
        Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓕) :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)))
  have hnat := SmallEtale.associatedModulePresheafIso_hom_naturality_module E
    (p.obj z').left.1 (contains_base B E h S hS p z')
    ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
      (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left)
      (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕)
    (op (smallEtaleFinal B E h S hS p z'))
  have hl := NatTrans.congr_app (liftedSmallEtaleIsoOfSheafified_hom_comp_sheafInv B E h S hS p hp
      F hlqcF
    φ 𝓕 h𝓕 hMx hMz eU hiso) (op (smallEtaleFinal B E h S hS p z))
  simp only [NatTrans.id_app] at hl
  refine split_prefix
    (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).hom _ _
    (((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map
        (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom))).app
      (op (smallEtaleFinal B E h S hS p z)))
    _ _ _ (Iso.inv_hom_id _) hl ?_
  exact factor_four_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfinal hsi hnat
    (hc ψ ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) inferInstance n hn)


end AlgebraicGeometry.Stack

end
