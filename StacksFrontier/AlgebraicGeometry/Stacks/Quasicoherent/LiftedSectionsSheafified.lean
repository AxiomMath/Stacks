module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleIsoComposition

/-!
# The identification of sections of Stacks 076T, under the sheaf-level comparison

The proof of **Stacks 076T** identifies, for an arrow `φ : z ⟶ x` of `𝒳` lying over a flat
morphism locally of finite presentation `g : W ⟶ U`, the restriction `F|_{W_ét}` with `(g^*𝓕)^a`,
where `𝓕` is the quasi-coherent `𝒪_U`-module with `𝓕^a ≅ F|_{U_ét}`. That identification needs
the comparison map `c_φ : g_{small}^*(F|_{U_ét}) ⟶ F|_{W_ét}` of **Stacks 06WC** to be an
isomorphism *of sheaves*, the inverse image `g_{small}^*` being that of sheaves of modules.

`AlgebraicGeometry.Stack.liftedSmallEtaleIso` asks instead that the comparison map be an
isomorphism of *presheaves* of modules, which is a strictly stronger condition, false for
quasi-coherent modules in general (see the module docstring of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafFlatBaseChangeProperty.lean`). This file
redoes the identification and its consequences under the source's condition:
`AlgebraicGeometry.Stack.IsIsoSheafifiedComparison` asks that the adjunct
`AlgebraicGeometry.Stack.sheafifiedRestrictComparison` of `c_φ` under the sheafification
adjunction — the comparison map of sheaves of modules — be an isomorphism.

The identification is defined directly as the inverse of the morphism of sheaves of modules
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`, which is an isomorphism under that hypothesis,
so the inverse identity of `AlgebraicGeometry.Stack.liftedSmallEtaleIso_hom_comp_sheafInv` holds
by construction; everything downstream is the same assembly as in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.IsIsoSheafifiedComparison`: the comparison map of sheaves of modules
  below an arrow is an isomorphism.
* `AlgebraicGeometry.Stack.liftedSmallEtaleIsoSheafified`: `F|_{W_ét} ≅ (g^*𝓕)^a`.
* `AlgebraicGeometry.Stack.liftedSectionsIsoSheafified` and
  `AlgebraicGeometry.Stack.overPostSectionsIsoSheafified`: the identification of sections.
* `AlgebraicGeometry.Stack.LiftedSectionsCocycleSheafified`: its compatibility with composition,
  proved in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsCocycleSheafified.lean`.

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
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

/-- **The comparison map of Stacks 06WC is an isomorphism of sheaves** below an arrow
`φ : z ⟶ x`: the adjunct `AlgebraicGeometry.Stack.sheafifiedRestrictComparison` of `c_φ` under
the sheafification adjunction, a morphism from the sheafified inverse image of `F|_{U_ét}` to the
sheaf `F|_{W_ét}`, is invertible. This is the condition **Stacks 0762** asks of `φ`. -/
abbrev IsIsoSheafifiedComparison {x z : 𝒳} (φ : z ⟶ x) : Prop :=
  IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 z).choose)

/-- Under `AlgebraicGeometry.Stack.IsIsoSheafifiedComparison`, the morphism of sheaves of modules
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` attached to an isomorphism `𝓕^a ≅ F|_{U_ét}`
is an isomorphism: it is a composite of an identification, the image of an isomorphism under a
functor, and the comparison map of sheaves. -/
theorem isIso_liftedSmallEtaleSheafInv {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules)
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
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ) :
    IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom) := by
  have : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ hMz) := hiso
  rw [liftedSmallEtaleSheafInv_eq]
  have h1 : IsIso ((SheafOfModules.forget _).map eU.hom) := Functor.map_isIso _ _
  have h2 : IsIso ((PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).map ((SheafOfModules.forget _).map eU.hom)) :=
    Functor.map_isIso _ _
  have h3 : IsIso ((PresheafOfModules.sheafification (𝟙 _)).map
      ((PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).map ((SheafOfModules.forget _).map eU.hom))) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h3 this)

/-- **The restriction `F|_{W_ét}` is the associated module of `g^*𝓕`**, under the sheaf-level
comparison: for an arrow `φ : z ⟶ x` of `𝒳` lying over `g : W ⟶ U` along which the comparison
map of sheaves of **Stacks 06WC** is an isomorphism, and for a quasi-coherent `𝒪_U`-module `𝓕`
with `𝓕^a ≅ F|_{U_ét}`, the restriction of `F` to the small étale site of `W` is `(g^*𝓕)^a`.

It is the inverse of `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`, read on presheaves. -/
noncomputable def liftedSmallEtaleIsoSheafified {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (_h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ) :
    (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf ≅
      ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val.presheaf :=
  have := isIso_liftedSmallEtaleSheafInv B E h S hS p hp F hlqc φ 𝓕 hMx (hlqc.2 z).choose eU hiso
  ((PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).mapIso
      (asIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx (hlqc.2 z).choose
        eU.hom)))).symm

/-- `AlgebraicGeometry.Stack.liftedSmallEtaleIsoSheafified` is inverse to
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`, by construction. -/
theorem liftedSmallEtaleIsoSheafified_hom_comp_sheafInv {x z : 𝒳} (φ : z ⟶ x)
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
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ) :
    (liftedSmallEtaleIsoSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (PresheafOfModules.toPresheaf _).map
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
            (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)) =
      𝟙 _ :=
  have := isIso_liftedSmallEtaleSheafInv B E h S hS p hp F hlqc φ 𝓕 hMx (hlqc.2 z).choose eU hiso
  Iso.inv_hom_id _


/-- **The identification of the sections of `F` at `z` with the sections of the presheaf of
Stacks 03DS of `𝓕` over `g`**, under the sheaf-level comparison: `F(z) = Γ(W, g^*𝓕)`. The same
five factors as `AlgebraicGeometry.Stack.liftedSectionsIso`, with
`AlgebraicGeometry.Stack.liftedSmallEtaleIsoSheafified` as the middle one. -/
noncomputable def liftedSectionsIsoSheafified {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ) :
    F.presheaf.obj (op z) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj
        (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) := by
  letI := h𝓕
  refine (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).symm ≪≫
    (liftedSmallEtaleIsoSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).app
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

/-- **The identification of the sections, at an object of the big fppf site of `U`**, under
the sheaf-level comparison: `AlgebraicGeometry.Stack.liftedSectionsIsoSheafified` at the arrow of
`𝒳` which the localization equivalence of **Stacks 06W0** produces over the object, followed by
the restriction map along the counit of that equivalence. -/
noncomputable def overPostSectionsIsoSheafified (x : 𝒳)
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
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V)) :
    F.presheaf.obj (op (overPostLiftObj B S hS p hp x V)) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj (op V) :=
  liftedSectionsIsoSheafified B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V) 𝓕 h𝓕 hMx eU
      hiso ≪≫
    (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).mapIso
      (Iso.op (overPostLiftIso B S hS p hp x V).symm)

/-- **The compatibility of `AlgebraicGeometry.Stack.liftedSectionsIsoSheafified` with composition
of arrows of `𝒳`**, at a composable pair of arrows along which the comparison maps of sheaves of
**Stacks 06WC** are isomorphisms. It is proved, as
`AlgebraicGeometry.Stack.liftedSectionsCocycleSheafified`, in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsCocycleSheafified.lean`. -/
def LiftedSectionsCocycleSheafified : Prop :=
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
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ)
    (hiso' : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ'),
    F.presheaf.map ψ.op ≫
        (liftedSectionsIsoSheafified B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx eU hiso').hom =
      (liftedSectionsIsoSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map ψ)
            (by simp [hφ']) :
            Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ') ⟶
              Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ)).op

/-- **Over the cocycle condition, the identification commutes with the restriction maps of the big
fppf site of `U`**: `AlgebraicGeometry.Stack.overPostSectionsIso_naturality` under the
sheaf-level comparison. -/
theorem overPostSectionsIsoSheafified_naturality (hcoc : LiftedSectionsCocycleSheafified B E h S hS
    p hp) (x : 𝒳)
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
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V))
    (hiso' : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V')) :
    F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op ≫
        (overPostSectionsIsoSheafified B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso').hom =
      (overPostSectionsIsoSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso).hom ≫
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
  simp only [overPostSectionsIsoSheafified, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hcell, Category.assoc, htail _ rfl, Category.assoc]

/-- The identification of `AlgebraicGeometry.Stack.overPostSectionsIsoSheafified` read as a map
between the sections of the two presheaves the reduced sheaf condition is about. -/
noncomputable def overPostSectionsMapSheafified
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
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V))
    (M : AddCommGrpCat.{u}) :
    (overPostTransportSections B S hS p hp F x M).obj (op V) →
      (overPostSectionsTypes B S hS p x 𝓕 h𝓕 M).obj (op V) :=
  fun s => ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIsoSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso)).hom s

/-- **`AlgebraicGeometry.Stack.overPostSectionsMapSheafified` is a bijection**, the identification
it comes from being an isomorphism. -/
theorem overPostSectionsMapSheafified_bijective
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
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V))
    (M : AddCommGrpCat.{u}) :
    Function.Bijective (overPostSectionsMapSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso M)
        :=
  ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIsoSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso)).toEquiv.bijective

include hlqc in
/-- **Over the cocycle condition, `AlgebraicGeometry.Stack.overPostSectionsMapSheafified`
commutes with the restriction maps of the big fppf site of `U`.** -/
theorem overPostSectionsMapSheafified_naturality (hcoc : LiftedSectionsCocycleSheafified B E h S hS
    p hp)
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
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V))
    (hiso' : IsIsoSheafifiedComparison B E h S hS p hp F hlqc (overPostLiftHom B S hS p hp x V'))
    (M : AddCommGrpCat.{u})
    (s : (overPostTransportSections B S hS p hp F x M).obj (op V)) :
    overPostSectionsMapSheafified B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso' M
        ((overPostTransportSections B S hS p hp F x M).map r.op s) =
      (overPostSectionsTypes B S hS p x 𝓕 h𝓕 M).map r.op
        (overPostSectionsMapSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso M s) := by
  have key := overPostSectionsIsoSheafified_naturality B E h S hS p hp F hlqc hcoc x r 𝓕 h𝓕 hMx eU
      hiso hiso'
  change (s ≫ F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op) ≫
      (overPostSectionsIsoSheafified B E h S hS p hp F hlqc x V' 𝓕 h𝓕 hMx eU hiso').hom =
    (s ≫ (overPostSectionsIsoSheafified B E h S hS p hp F hlqc x V 𝓕 h𝓕 hMx eU hiso).hom) ≫
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => s ≫ t) key).trans (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Stack

end
