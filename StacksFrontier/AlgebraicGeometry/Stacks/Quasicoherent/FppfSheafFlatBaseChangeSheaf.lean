module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsFactorFourReduction

/-!
# Stacks 076T with the flat base change property read on sheaves of modules

**Stacks 076T** says that a presheaf of modules `ℱ` on a category fibred in groupoids `𝒳` over
`(Sch/S)_{fppf}` which is locally quasi-coherent (**Stacks 06WJ**) and whose comparison maps
`c_φ : a_{small}^*(ℱ|_{V_ét}) ⟶ ℱ|_{U_ét}` of **Stacks 06WC** are isomorphisms along every arrow
`φ` lying over a flat morphism locally of finite presentation is a sheaf for the fppf topology.
In the source `a_{small}^*` is the pullback of *sheaves* of modules along the morphism of ringed
sites `ε_a` of **Stacks 070R (2)**, so `c_φ` is the comparison map read on sheaves of modules,
`AlgebraicGeometry.Stack.sheafifiedRestrictComparisonNatTrans`.

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFlatBaseChangeProved.lean` proves
the
statement with `c_φ` computed in *presheaves* of modules, which is a strictly stronger hypothesis
(see `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_hasFlatBaseChangeProperty`, and the
counterexample recorded in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/CoheratorSheaf.lean`).  This file proves it
at the source's reading.

## The proof

The proof of the presheaf version identifies, for an arrow `φ : z ⟶ x` lying over `g : W ⟶ U`,
the sections `ℱ(z)` with `Γ(W, g^*𝓕)`, where `𝓕` is the quasi-coherent `𝒪_U`-module with
`𝓕^a ≅ ℱ|_{U_ét}`, and transports the fppf sheaf condition of `𝒢^a` on `(Sch/U)_{fppf}`
(Descent, **Stacks 03DT**) across that identification.  The only place where the comparison map
enters is the identification `ℱ|_{W_ét} ≅ (g^*𝓕)^a` of factors 2, 3 and 4; its inverse is the
morphism of *sheaves* of modules `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`, which is the
base change identification of **Stacks 03LC (1)**, the sheafified pullback of `𝓕^a ≅ ℱ|_{U_ét}`
and the sheaf-level comparison map.  So it is invertible exactly when the sheaf-level comparison
map is, and every later step of the presheaf proof — the cocycle condition, which is proved at
sheaf level through `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp`, and the transport —
only ever uses the identification through that inverse.  The declarations below are the steps of
the presheaf proof restated over the hypothesis that `liftedSmallEtaleSheafInv` is invertible.

## Main results

* `AlgebraicGeometry.Stack.isIso_liftedSmallEtaleSheafInv_of_isIso_sheafifiedRestrictComparison`:
  the inverse identification is invertible as soon as the sheaf-level comparison map is.
* `AlgebraicGeometry.Stack.liftedSectionsIsoOfInv_cocycle`: the cocycle condition for the
  identification of sections, unconditionally.
* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_flatLfpBaseChangeSheaf`:
  **Stacks 076T** at the source's reading of the comparison map.
* `AlgebraicGeometry.Stack.isSheaf_fppf_of_locallyQuasicoherentFlatBaseChangeSheaf`: the case
  used by **Stacks 0771 (1)**, a member of `LQCoh^fbc(𝒪_𝒳)` is an fppf sheaf.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe t u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-! ### The identification of the sections over an invertible sheaf-level inverse -/

/-- **Factors 2, 3 and 4 of the identification of Stacks 076T, from their sheaf-level inverse.**
For an arrow `φ : z ⟶ x` of `𝒳` lying over `g : W ⟶ U`, a quasi-coherent `𝒪_U`-module `𝓕` and a
morphism `e : 𝓕^a ⟶ F|_{U_ét}` such that `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` is an
isomorphism, the restriction `F|_{W_ét}` is identified with `(g^*𝓕)^a` by the inverse of that
morphism of sheaves of modules. -/
noncomputable def liftedSmallEtaleIsoOfInv {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (e : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e)] :
    (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf ≅
      ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val.presheaf :=
  ((PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).mapIso
      (asIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e)))).symm

/-- The identification of `AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfInv` followed by the
morphism of sheaves of modules it inverts is the identity. -/
theorem liftedSmallEtaleIsoOfInv_hom_comp_sheafInv {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (e : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e)] :
    (liftedSmallEtaleIsoOfInv B E h S hS p hp F φ 𝓕 hMx hMz e).hom ≫
        (PresheafOfModules.toPresheaf _).map
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
            (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e)) =
      𝟙 _ :=
  ((PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).mapIso
      (asIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e)))).inv_hom_id

/-- **The identification of the sections of `F` at `z` with the sections of the presheaf of
Stacks 03DS of `𝓕` over `g`**, over an invertible sheaf-level inverse.  This is
`AlgebraicGeometry.Stack.liftedSectionsIso` with factors 2, 3 and 4 replaced by
`AlgebraicGeometry.Stack.liftedSmallEtaleIsoOfInv`. -/
noncomputable def liftedSectionsIsoOfInv {x z : 𝒳} (φ : z ⟶ x)
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
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)] :
    F.presheaf.obj (op z) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj
        (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) := by
  letI := h𝓕
  refine (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).symm ≪≫
    (liftedSmallEtaleIsoOfInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom).app
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

/-- The first four factors of `AlgebraicGeometry.Stack.liftedSectionsIsoOfInv`. -/
noncomputable def liftedSectionsUpperOfInv {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) [𝓕.IsQuasicoherent]
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
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)] :
    F.presheaf.obj (op z) ⟶
      (quasiCoherentPresheafFunctor (p.obj z).left.1
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).obj
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) :=
  (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).inv ≫
    (liftedSmallEtaleIsoOfInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom).hom.app
      (op (smallEtaleFinal B E h S hS p z)) ≫
    (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
      (op (smallEtaleFinal B E h S hS p z))

/-- `AlgebraicGeometry.Stack.liftedSectionsIsoOfInv` split as
`AlgebraicGeometry.Stack.liftedSectionsUpperOfInv` followed by the base change identification of
**Stacks 03DS**, read backwards, and a restriction map along an arrow with identity left
component. -/
theorem liftedSectionsIsoOfInv_hom_eq {x z : 𝒳} (φ : z ⟶ x)
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
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)] :
    letI := h𝓕
    ∃ e : (Over.mk (B.inclusion.map (p.map φ).left) : Over (p.obj x).left.1) ⟶
        (Over.map (B.inclusion.map (p.map φ).left)).obj
          ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
            (smallEtaleFinal B E h S hS p z)),
      e.left = 𝟙 _ ∧
      (liftedSectionsIsoOfInv B E h S hS p hp F φ 𝓕 h𝓕 hMx hMz eU).hom =
        liftedSectionsUpperOfInv B E h S hS p hp F φ 𝓕 hMx hMz eU ≫
          ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕
              (Over.mk (B.inclusion.map (p.map φ).left))).inv.app
            (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
              (smallEtaleFinal B E h S hS p z))) ≫
            (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map e.op) := by
  let := h𝓕
  refine ⟨(Over.isoMk (Iso.refl _)
    (by simp)).hom, rfl, ?_⟩
  unfold liftedSectionsIsoOfInv liftedSectionsUpperOfInv
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rfl

/-- **The factor-four square of Stacks 076T over an invertible sheaf-level inverse**, with no
further hypothesis: the compatibility of the two base changes on sections is
`AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat`.  The proof is that of
`AlgebraicGeometry.Stack.liftedSectionsFactorFourSquare_of_compat`, which only ever uses the
identification of factors 2, 3 and 4 through its sheaf-level inverse. -/
theorem liftedSectionsFactorFourSquareOfInv {x : 𝒳}
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
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)]
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ' 𝓕 hMx hMz' eU.hom)]
    (n : (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
          (smallEtaleFinal B E h S hS p z')) ⟶
      (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z))
    (hn : n.left = B.inclusion.map (p.map ψ).left) :
    letI := h𝓕
    F.presheaf.map ψ.op ≫ liftedSectionsUpperOfInv B E h S hS p hp F φ' 𝓕 hMx hMz' eU =
      liftedSectionsUpperOfInv B E h S hS p hp F φ 𝓕 hMx hMz eU ≫
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
                (smallEtaleFinal B E h S hS p z'))).hom := by
  let := h𝓕
  subst hφ'
  have right_inv : ∀ {X Y : AddCommGrpCat.{u}} (e : X ≅ Y) (s : Y ⟶ X),
      e.hom ≫ s = 𝟙 X → s ≫ e.hom = 𝟙 Y := by
    intro X Y e s hs
    have hse : s = e.inv := by
      rw [← Category.id_comp s, ← e.inv_hom_id, Category.assoc, hs, Category.comp_id]
    rw [hse, e.inv_hom_id]
  have algebra : ∀ {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ O₁₃ : AddCommGrpCat.{u}}
      (sinv : O₁ ⟶ O₂) (fzh : O₂ ⟶ O₃) (fψ : O₃ ⟶ O₄) (fzi' : O₄ ⟶ O₅)
      (lam' : O₅ ⟶ O₆) (ap' : O₆ ⟶ O₇)
      (uu : O₁ ⟶ O₈) (eta : O₈ ⟶ O₉) (bc : O₉ ⟶ O₁₀) (pf : O₁₀ ⟶ O₆) (si' : O₆ ⟶ O₅)
      (apQ : O₁₀ ⟶ O₁₁) (pfs : O₁₁ ⟶ O₇) (apB : O₁ ⟶ O₁₂) (nmap : O₁₂ ⟶ O₁₃)
      (qcbc : O₁₃ ⟶ O₁₁),
      uu ≫ eta ≫ bc ≫ pf ≫ si' = sinv ≫ fzh ≫ fψ ≫ fzi' → si' ≫ lam' = 𝟙 O₆ →
      pf ≫ ap' = apQ ≫ pfs → uu ≫ eta ≫ bc ≫ apQ = apB ≫ nmap ≫ qcbc →
      sinv ≫ fzh ≫ fψ ≫ fzi' ≫ lam' ≫ ap' = apB ≫ nmap ≫ qcbc ≫ pfs := by
    intro O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ O₁₃ sinv fzh fψ fzi' lam' ap' uu eta bc pf si'
      apQ pfs apB nmap qcbc hfinal hsi hnat hcompat
    have e1 : uu ≫ eta ≫ bc ≫ pf ≫ si' ≫ lam' ≫ ap' =
        sinv ≫ fzh ≫ fψ ≫ fzi' ≫ lam' ≫ ap' := by
      have hf := congrArg (fun t => t ≫ lam' ≫ ap') hfinal
      simpa only [Category.assoc] using hf
    rw [← e1, ← Category.assoc si' lam' ap', hsi, Category.id_comp, hnat]
    have hcc := congrArg (fun t => t ≫ pfs) hcompat
    simpa only [Category.assoc] using hcc
  have split : ∀ {O₁ O₂ O₃ O₄ O₅ : AddCommGrpCat.{u}}
      (fzh : O₂ ⟶ O₁) (fzi : O₁ ⟶ O₂) (lh : O₂ ⟶ O₃) (li : O₃ ⟶ O₂)
      (t : O₁ ⟶ O₄) (ap : O₃ ⟶ O₅) (rest : O₅ ⟶ O₄),
      fzi ≫ fzh = 𝟙 O₁ → lh ≫ li = 𝟙 O₂ → li ≫ fzh ≫ t = ap ≫ rest →
      t = (fzi ≫ lh ≫ ap) ≫ rest := by
    intro O₁ O₂ O₃ O₄ O₅ fzh fzi lh li t ap rest hfz hl key
    rw [Category.assoc, Category.assoc, ← key, ← Category.assoc lh li, hl, Category.id_comp,
      ← Category.assoc, hfz, Category.id_comp]
  rw [Stacks.Sites.pullbackCompSectionsIsoOfEq_hom]
  unfold liftedSectionsUpperOfInv
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
  have hA := NatTrans.congr_app (liftedSmallEtaleIsoOfInv_hom_comp_sheafInv B E h S hS p hp F
    (ψ ≫ φ) 𝓕 hMx hMz' eU.hom) (op (smallEtaleFinal B E h S hS p z'))
  simp only [NatTrans.id_app] at hA
  have hsi := right_inv
    ((liftedSmallEtaleIsoOfInv B E h S hS p hp F (ψ ≫ φ) 𝓕 hMx hMz' eU.hom).app
      (op (smallEtaleFinal B E h S hS p z'))) _ hA
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
  have hl := NatTrans.congr_app (liftedSmallEtaleIsoOfInv_hom_comp_sheafInv B E h S hS p hp F
    φ 𝓕 hMx hMz eU.hom) (op (smallEtaleFinal B E h S hS p z))
  simp only [NatTrans.id_app] at hl
  refine split
    (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).hom _ _
    (((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map
        (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom))).app
      (op (smallEtaleFinal B E h S hS p z)))
    _ _ _ (Iso.inv_hom_id _) hl ?_
  exact algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfinal hsi hnat
    ((associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp) ψ
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) inferInstance n hn)


/-- **The cocycle condition for the identification of sections of Stacks 076T**, over invertible
sheaf-level inverses at the two arrows it mentions, with no further hypothesis.  This is
`AlgebraicGeometry.Stack.liftedSectionsCocycle_at_belowArrowSite` with its factor-four square
supplied by `AlgebraicGeometry.Stack.liftedSectionsFactorFourSquareOfInv`. -/
theorem liftedSectionsIsoOfInv_cocycle {x : 𝒳}
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
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
        (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)]
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ' 𝓕 hMx hMz' eU.hom)] :
    F.presheaf.map ψ.op ≫
        (liftedSectionsIsoOfInv B E h S hS p hp F φ' 𝓕 h𝓕 hMx hMz' eU).hom =
      (liftedSectionsIsoOfInv B E h S hS p hp F φ 𝓕 h𝓕 hMx hMz eU).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (belowArrowSite B S hS p ψ φ φ' hφ').op := by
  let := h𝓕
  have paste : ∀ {P P' Q Q' R T T' : AddCommGrpCat.{u}}
      (fψ : P ⟶ P') (u : P ⟶ Q) (u' : P' ⟶ Q') (v : Q ⟶ Q')
      (dinv : Q ⟶ R) (dhom : R ⟶ Q) (ee : R ⟶ T) (tail' : Q' ⟶ T') (mapme : R ⟶ T')
      (mm : T ⟶ T'),
      fψ ≫ u' = u ≫ v → dhom ≫ v ≫ tail' = mapme → mapme = ee ≫ mm → dinv ≫ dhom = 𝟙 Q →
      fψ ≫ u' ≫ tail' = (u ≫ dinv ≫ ee) ≫ mm := by
    intro P P' Q Q' R T T' fψ u u' v dinv dhom ee tail' mapme mm hA hB hC hD
    rw [← Category.assoc, hA, Category.assoc, Category.assoc, Category.assoc, ← hC, ← hB,
      ← Category.assoc dinv dhom, hD, Category.id_comp]
  have hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left := by
    rw [hφ', p.map_comp]
    exact B.inclusion.map_comp _ _
  obtain ⟨e, he, hfac⟩ := liftedSectionsIsoOfInv_hom_eq B E h S hS p hp F φ 𝓕 h𝓕 hMx hMz eU
  obtain ⟨e', he', hfac'⟩ :=
    liftedSectionsIsoOfInv_hom_eq B E h S hS p hp F φ' 𝓕 h𝓕 hMx hMz' eU
  have hmm : (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
        (belowArrowSite B S hS p ψ φ φ' hφ').op =
      (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
        (belowArrow B S hS p ψ φ φ' hkg).op := rfl
  rw [hfac, hfac', hmm]
  have hA := liftedSectionsFactorFourSquareOfInv B E h S hS p hp F 𝓕 h𝓕 hMx eU ψ φ φ' hφ' hkg
    hMz hMz' (finalBaseChangeArrow B E h S hS p ψ) rfl
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
  exact paste _ _ _ _ _ _ _ _ _ _ hA hB hC (Iso.inv_hom_id_app _ _)

/-! ### The identification at an object of the big fppf site of `U` -/

/-- **The identification of the sections, at an object of the big fppf site of `U`**, over an
invertible sheaf-level inverse: `AlgebraicGeometry.Stack.liftedSectionsIsoOfInv` at the arrow of
`𝒳` which the localization equivalence of **Stacks 06W0** produces over the object, followed by
the restriction map along the counit of that equivalence. -/
noncomputable def overPostSectionsIsoOfInv (x : 𝒳)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMV : Presheaf.IsSheaf (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V)).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V)))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V)
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V) 𝓕
      hMx hMV eU.hom)] :
    F.presheaf.obj (op (overPostLiftObj B S hS p hp x V)) ≅
      (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).obj (op V) :=
  liftedSectionsIsoOfInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V) 𝓕 h𝓕 hMx hMV eU ≪≫
    (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).mapIso
      (Iso.op (overPostLiftIso B S hS p hp x V).symm)

/-- **The identification commutes with the restriction maps of the big fppf site of `U`**, with
no hypothesis beyond the invertibility of the sheaf-level inverses at the two objects.  This is
`AlgebraicGeometry.Stack.overPostSectionsIso_naturality` with the cocycle supplied by
`AlgebraicGeometry.Stack.liftedSectionsIsoOfInv_cocycle`. -/
theorem overPostSectionsIsoOfInv_naturality (x : 𝒳)
    {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)} (r : V' ⟶ V)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMV : Presheaf.IsSheaf (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V)).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V)))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V)
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    (hMV' : Presheaf.IsSheaf
        (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V')).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V')))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V')
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V) 𝓕
      hMx hMV eU.hom)]
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V') 𝓕
      hMx hMV' eU.hom)] :
    F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op ≫
        (overPostSectionsIsoOfInv B E h S hS p hp F x V' 𝓕 h𝓕 hMx hMV' eU).hom =
      (overPostSectionsIsoOfInv B E h S hS p hp F x V 𝓕 h𝓕 hMx hMV eU).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map r.op := by
  have hφ' : overPostLiftHom B S hS p hp x V' =
      ((overPostEquivalence B S hS p hp x).inverse.map r).left ≫
        overPostLiftHom B S hS p hp x V :=
    (Over.w ((overPostEquivalence B S hS p hp x).inverse.map r)).symm
  have hcell := liftedSectionsIsoOfInv_cocycle B E h S hS p hp F 𝓕 h𝓕 hMx eU
    (((overPostEquivalence B S hS p hp x).inverse.map r).left)
    (overPostLiftHom B S hS p hp x V) (overPostLiftHom B S hS p hp x V') hφ' hMV hMV'
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
  simp only [overPostSectionsIsoOfInv, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hcell, Category.assoc, htail _ rfl, Category.assoc]

/-- **The sheaf-level inverse is invertible when the sheaf-level comparison map is.**
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` is the base change identification of
**Stacks 03LC (1)** read backwards, followed by the sheafified pullback of the isomorphism
`e : 𝓕^a ≅ F|_{U_ét}` and by the comparison map of **Stacks 06WC** read on sheaves of modules. -/
theorem isIso_liftedSmallEtaleSheafInv_of_isIso_sheafifiedRestrictComparison {x z : 𝒳}
    (φ : z ⟶ x) (𝓕 : (p.obj x).left.1.Modules)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (e : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx) (he : IsIso e)
    (hc : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ hMz)) :
    IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e) := by
  unfold liftedSmallEtaleSheafInv
  have : IsIso ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).map e) := @Functor.map_isIso _ _ _ _ _ _ _ e he
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this hc)

/-! ### The transport of the sheaf condition -/

namespace QuasicoherentBelow

variable {B E h S hS p hp F} {x : 𝒳} (d : QuasicoherentBelow B E h S hS p hp F x)

/-- The identification of `AlgebraicGeometry.Stack.overPostSectionsIsoOfInv` at the
quasi-coherent module below `x`, read as a map between the sections of the two presheaves the
reduced sheaf condition is about. -/
noncomputable def sectionsMapOfInv (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hMV : Presheaf.IsSheaf (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V)).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V)))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V)
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V) d.val
      d.isSheaf hMV d.iso.hom)]
    (M : AddCommGrpCat.{u}) :
    (overPostTransportSections B S hS p hp F x M).obj (op V) →
      (overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M).obj (op V) :=
  fun s => ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIsoOfInv B E h S hS p hp F x V d.val d.isQuasicoherent d.isSheaf hMV
      d.iso)).hom s

/-- `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMapOfInv` is a bijection. -/
theorem sectionsMapOfInv_bijective (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hMV : Presheaf.IsSheaf (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V)).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V)))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V)
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V) d.val
      d.isSheaf hMV d.iso.hom)]
    (M : AddCommGrpCat.{u}) :
    Function.Bijective (d.sectionsMapOfInv V hMV M) :=
  ((coyoneda.obj (op M)).mapIso
    (overPostSectionsIsoOfInv B E h S hS p hp F x V d.val d.isQuasicoherent d.isSheaf hMV
      d.iso)).toEquiv.bijective

/-- `AlgebraicGeometry.Stack.QuasicoherentBelow.sectionsMapOfInv` commutes with the restriction
maps of the big fppf site of `U`. -/
theorem sectionsMapOfInv_naturality {V V' : Over ((p ⋙ Over.forget (B.obj hS)).obj x)}
    (r : V' ⟶ V)
    (hMV : Presheaf.IsSheaf (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V)).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V)))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V)
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    (hMV' : Presheaf.IsSheaf
        (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V')).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V')))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V')
        (etaleTopology B) (etaleTopology_le_topology B) F).presheaf)
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V) d.val
      d.isSheaf hMV d.iso.hom)]
    [IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F (overPostLiftHom B S hS p hp x V') d.val
      d.isSheaf hMV' d.iso.hom)]
    (M : AddCommGrpCat.{u})
    (s : (overPostTransportSections B S hS p hp F x M).obj (op V)) :
    d.sectionsMapOfInv V' hMV' M ((overPostTransportSections B S hS p hp F x M).map r.op s) =
      (overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M).map r.op
        (d.sectionsMapOfInv V hMV M s) := by
  have key := overPostSectionsIsoOfInv_naturality B E h S hS p hp F x r d.val d.isQuasicoherent
    d.isSheaf hMV hMV' d.iso
  change (s ≫ F.presheaf.map (((overPostEquivalence B S hS p hp x).inverse.map r).left).op) ≫
      (overPostSectionsIsoOfInv B E h S hS p hp F x V' d.val d.isQuasicoherent d.isSheaf hMV'
        d.iso).hom =
    (s ≫ (overPostSectionsIsoOfInv B E h S hS p hp F x V d.val d.isQuasicoherent d.isSheaf hMV
        d.iso).hom) ≫
      (overPostSectionsPresheaf B S hS p x d.val d.isQuasicoherent).map r.op
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => s ≫ t) key).trans (Category.assoc _ _ _).symm)

end QuasicoherentBelow

section Transport

attribute [local irreducible] overPostTransportSections overPostSectionsTypes
  QuasicoherentBelow.sectionsMapOfInv

variable (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

include hlqc in
/-- **The transport of the sheaf condition downstairs, over invertible sheaf-level inverses.**
For a family `{π i : U_i / U → U / U}` of the big fppf site of the scheme `U` below `x` which
generates a covering sieve, if the sheaf-level inverse of
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` is invertible along the arrows of `𝒳` which
the localization equivalence of **Stacks 06W0** produces over `U / U`, over each `U_i / U` and over
each fibre product, then the transported presheaf satisfies the sheaf condition for the family.
This is `AlgebraicGeometry.Stack.isSheafFor_overPostTransportSections_of_isIso` at the sheaf
reading. -/
theorem isSheafFor_overPostTransportSections_of_isIso_sheafInv {x : 𝒳}
    (d : QuasicoherentBelow B E h S hS p hp F x)
    {I : Type t} (X : I → Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (π : ∀ i, X i ⟶ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
    {W : I → I → Over ((p ⋙ Over.forget (B.obj hS)).obj x)}
    (pr₁ : ∀ i j, W i j ⟶ X i) (pr₂ : ∀ i j, W i j ⟶ X j)
    (hW : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (π i) (π j))
    (hisoY : IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F
      (overPostLiftHom B S hS p hp x (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
      d.val d.isSheaf (hlqc.2 _).choose d.iso.hom))
    (hisoX : ∀ i, IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F
      (overPostLiftHom B S hS p hp x (X i)) d.val d.isSheaf (hlqc.2 _).choose d.iso.hom))
    (hisoW : ∀ i j, IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F
      (overPostLiftHom B S hS p hp x (W i j)) d.val d.isSheaf (hlqc.2 _).choose d.iso.hom))
    (hcov : Sieve.generate (Presieve.ofArrows X π) ∈
      BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf
        (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
    (M : AddCommGrpCat.{u}) :
    Presieve.IsSheafFor (overPostTransportSections B S hS p hp F x M)
      (Presieve.ofArrows X π) :=
  Presieve.Arrows.isSheafFor_ofArrows_of_maps
    (Q := overPostTransportSections B S hS p hp F x M)
    (Q' := overPostSectionsTypes B S hS p x d.val d.isQuasicoherent M)
    (Y := Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) (X := X) (W := W)
    π pr₁ pr₂ hW
    (d.sectionsMapOfInv (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) _ M)
    (d.sectionsMapOfInv_bijective (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) _ M)
    (fun i ↦ have := hisoX i; d.sectionsMapOfInv (X i) _ M)
    (fun i ↦ have := hisoX i; (d.sectionsMapOfInv_bijective (X i) _ M).injective)
    (fun i j ↦ have := hisoW i j; d.sectionsMapOfInv (W i j) _ M)
    (fun i s ↦ have := hisoX i; d.sectionsMapOfInv_naturality (π i) _ _ M s)
    (fun i j s ↦ have := hisoX i; have := hisoW i j;
      d.sectionsMapOfInv_naturality (pr₁ i j) _ _ M s)
    (fun i j s ↦ have := hisoX j; have := hisoW i j;
      d.sectionsMapOfInv_naturality (pr₂ i j) _ _ M s)
    (d.isSheafFor_sectionsTypes X π hcov M)

end Transport

/-! ### Stacks 076T at the sheaf reading -/

section SheafReading

variable (ℱ : SheafOfModules.{u}
  (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))

/-- **Hypothesis (b) of Stacks 076T, read on sheaves of modules.**  The comparison map `c_φ` of
**Stacks 06WC**, with `a_{small}^*` the pullback of sheaves of modules along `ε_a` of
**Stacks 070R (2)**, is an isomorphism for every arrow `φ` of `𝒳` lying over a morphism of
schemes which is flat and locally of finite presentation. -/
abbrev HasFlatLfpBaseChangePropertySheaf : Prop :=
  ∀ {x z : 𝒳} (φ : z ⟶ x), Flat (B.inclusion.map (p.map φ).left) →
    LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left) →
      IsIso ((sheafifiedRestrictComparisonNatTrans B E h S hS p hp φ).app ℱ)

/-- The flat base change property of **Stacks 0762**, read on sheaves of modules, implies
hypothesis (b) of **Stacks 076T** read the same way. -/
theorem hasFlatLfpBaseChangePropertySheaf_of_hasFlatBaseChangePropertySheaf
    (hℱ : HasFlatBaseChangePropertySheaf B E h S hS p hp ℱ) :
    HasFlatLfpBaseChangePropertySheaf B E h S hS p hp ℱ :=
  fun φ hflat _ => hℱ φ hflat

variable (hlqc : IsLocallyQuasicoherent B E h S hS p hp ℱ.val)
  (hbc : HasFlatLfpBaseChangePropertySheaf B E h S hS p hp ℱ)

include hbc in
/-- Hypothesis (b) of Stacks 076T read on sheaves of modules, consumed at one object of the big
fppf site of the scheme below `x`: the sheaf-level inverse of the identification of factors 2, 3
and 4 is invertible along the arrow of `𝒳` the localization equivalence produces over an object
lying over a flat morphism locally of finite presentation. -/
theorem isIso_liftedSmallEtaleSheafInv_overPostLift {x : 𝒳}
    (d : QuasicoherentBelow B E h S hS p hp ℱ.val x)
    (V : Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (hflat : Flat (B.inclusion.map V.hom))
    (hlfp : LocallyOfFinitePresentation (B.inclusion.map V.hom))
    (hMV : Presheaf.IsSheaf (SmallEtale.topology E (p.obj (overPostLiftObj B S hS p hp x V)).left.1
        (contains_base B E h S hS p (overPostLiftObj B S hS p hp x V)))
      (restrictModuleToSmallEtale B E h S hS p hp (overPostLiftObj B S hS p hp x V)
        (etaleTopology B) (etaleTopology_le_topology B) ℱ.val).presheaf) :
    IsIso (liftedSmallEtaleSheafInv B E h S hS p hp ℱ.val (overPostLiftHom B S hS p hp x V)
      d.val d.isSheaf hMV d.iso.hom) :=
  isIso_liftedSmallEtaleSheafInv_of_isIso_sheafifiedRestrictComparison B E h S hS p hp ℱ.val
    _ d.val d.isSheaf hMV d.iso.hom (Iso.isIso_hom d.iso)
    (hbc _ (flat_overPostLift B S hS p hp x V hflat)
      (locallyOfFinitePresentation_overPostLift B S hS p hp x V hlfp))

include hlqc hbc in
/-- **The sheaf condition along a family lying over an fppf covering of schemes, transported
downstairs from Descent, Stacks 03DT**, at the sheaf reading of hypothesis (b). -/
theorem isSheafFor_overPostTransportSections_sheaf {x : 𝒳}
    (d : QuasicoherentBelow B E h S hS p hp ℱ.val x)
    {I : Type t} (X : I → Over ((p ⋙ Over.forget (B.obj hS)).obj x))
    (π : ∀ i, X i ⟶ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
    (hflat : ∀ i, Flat (B.inclusion.map (X i).hom))
    (hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (X i).hom))
    (hcov : Sieve.generate (Presieve.ofArrows X π) ∈
      BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf
        (Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))
    (M : AddCommGrpCat.{u}) :
    Presieve.IsSheafFor (overPostTransportSections B S hS p hp ℱ.val x M)
      (Presieve.ofArrows X π) := by
  have hleft : ∀ i, (π i).left = (X i).hom := fun i ↦ by simpa using Over.w (π i)
  exact isSheafFor_overPostTransportSections_of_isIso_sheafInv B E h S hS p hp ℱ.val hlqc d X π
    (fun i j ↦ pullback.fst (π i) (π j)) (fun i j ↦ pullback.snd (π i) (π j))
    (fun i j ↦ IsPullback.of_hasPullback (π i) (π j))
    (isIso_liftedSmallEtaleSheafInv_overPostLift B E h S hS p hp ℱ hbc d _
      (by simpa using inferInstanceAs
        (Flat (𝟙 (B.inclusion.obj ((p ⋙ Over.forget (B.obj hS)).obj x)))))
      (by simpa using inferInstanceAs
        (LocallyOfFinitePresentation
          (𝟙 (B.inclusion.obj ((p ⋙ Over.forget (B.obj hS)).obj x))))) _)
    (fun i ↦ isIso_liftedSmallEtaleSheafInv_overPostLift B E h S hS p hp ℱ hbc d (X i)
      (hflat i) (hlfp i) _)
    (fun i j ↦ isIso_liftedSmallEtaleSheafInv_overPostLift B E h S hS p hp ℱ hbc d _
      (prop_hom_pullback B _ (π i) (π j) (hflat i) ((hleft j).symm ▸ hflat j))
      (prop_hom_pullback B _ (π i) (π j) (hlfp i) ((hleft j).symm ▸ hlfp j)) _)
    hcov M

include hlqc hbc in
/-- A locally quasi-coherent module with flat base change is an fppf sheaf, read on sheaves of
modules.  Let `ℱ` be a sheaf of `𝒪_𝒳`-modules on
`𝒳_étale` for a category `𝒳` fibred in groupoids over `(Sch/S)_{fppf}`.  If `ℱ` is locally
quasi-coherent (**Stacks 06WJ**) and the comparison map `c_φ` of **Stacks 06WC**, with
`a_{small}^*` the pullback of sheaves of modules, is an isomorphism for every arrow lying over a
flat morphism locally of finite presentation, then `ℱ` is a sheaf for the fppf topology.

The sheaf condition is tested on the families of arrows lying over an fppf covering of schemes
(`AlgebraicGeometry.Stack.isSheaf_of_isSheafFor_flatLfp`); along such a family it moves
downstairs to the big fppf site of the scheme below the target, where it is Descent,
**Stacks 03DT**, transported across the identification of sections of
`AlgebraicGeometry.Stack.liftedSectionsIsoOfInv`. -/
theorem isSheaf_fppf_of_isLocallyQuasicoherent_of_flatLfpBaseChangeSheaf :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) ℱ.val.presheaf := by
  refine isSheaf_of_isSheafFor_flatLfp B S hS p hp ℱ.val.presheaf ?_
  intro x R hR hfl M
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp ℱ.val hlqc x
  obtain ⟨I, z, φ, hRe⟩ :
      ∃ (I : Type (max v w)) (z : I → 𝒳) (φ : ∀ i, z i ⟶ x), Presieve.ofArrows z φ = R := by
    refine ⟨(y : 𝒳) × {f : y ⟶ x // R f}, fun i ↦ i.1, fun i ↦ i.2.1, ?_⟩
    funext Z g
    refine propext ⟨?_, fun hg ↦ ?_⟩
    · rintro ⟨i⟩
      exact i.2.2
    · exact Presieve.ofArrows.mk (⟨Z, g, hg⟩ : (y : 𝒳) × {f : y ⟶ x // R f})
  have hmem : ∀ i, R (φ i) := fun i ↦ hRe ▸ Presieve.ofArrows.mk i
  have hflat : ∀ i, Flat (B.inclusion.map (p.map (φ i)).left) := fun i ↦ (hfl (φ i) (hmem i)).1
  have hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (p.map (φ i)).left) := fun i ↦
    (hfl (φ i) (hmem i)).2
  have : p.IsFibered := hp.isFibered
  rw [← hRe] at hR ⊢
  have hbase : Sieve.ofArrows (fun i ↦ p.obj (z i)) (fun i ↦ p.map (φ i)) ∈
      (B.topology.over (B.obj hS)) (p.obj x) :=
    (Functor.isInheritedTopology_inheritedTopology.{max v w} p (B.topology.over (B.obj hS))
      z φ fun i ↦ hp.isStronglyCartesian (φ i)).1 hR
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hbase
  rw [isSheafFor_ofArrows_iff_overPost B S hS p hp x (ℱ.val.presheaf ⋙ coyoneda.obj (op M))
    (overPostTransportSections B S hS p hp ℱ.val x M) φ
    (overPostTransportIso B S hS p hp x (ℱ.val.presheaf ⋙ coyoneda.obj (op M)))]
  refine isSheafFor_overPostTransportSections_sheaf B E h S hS p hp ℱ hlqc hbc d _ _ hflat hlfp
    ?_ M
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hbase

end SheafReading

/-- **A member of `LQCoh^fbc(𝒪_𝒳)` is a sheaf for the fppf topology** (the first half of
**Stacks 0771 (1)**): a sheaf of `𝒪_𝒳`-modules on `𝒳_étale` which is locally quasi-coherent and
has the flat base change property of **Stacks 0762** read on sheaves of modules satisfies the
fppf sheaf condition. -/
theorem isSheaf_fppf_of_locallyQuasicoherentFlatBaseChangeSheaf
    {ℱ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))}
    (hℱ : locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp ℱ) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) ℱ.val.presheaf :=
  isSheaf_fppf_of_isLocallyQuasicoherent_of_flatLfpBaseChangeSheaf B E h S hS p hp ℱ hℱ.1
    (hasFlatLfpBaseChangePropertySheaf_of_hasFlatBaseChangePropertySheaf B E h S hS p hp ℱ hℱ.2)

end AlgebraicGeometry.Stack

end
