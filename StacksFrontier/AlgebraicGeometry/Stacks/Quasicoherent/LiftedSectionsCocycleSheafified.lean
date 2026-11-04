module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AssociatedModuleBaseChangeFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsSheafified

/-!
# The cocycle condition for the sections identification of Stacks 076T, sheaf-level

`AlgebraicGeometry.Stack.LiftedSectionsCocycleSheafified` is the compatibility with composition of
arrows of the identification of sections `AlgebraicGeometry.Stack.liftedSectionsIsoSheafified`,
which is built under the source's form of the hypothesis of **Stacks 076T**: the comparison map
of *sheaves* of **Stacks 06WC** is an isomorphism. This file proves it, by the same assembly as
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsCocycleAssembly.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsFactorFourReduction.lean` give
for the presheaf-level hypothesis: the cocycle condition reduces to a factor-four square, and the
square reduces to `AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat`, which
`AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat` proves and which does not
involve the comparison map at all.

## Main results

* `AlgebraicGeometry.Stack.liftedSectionsCocycleSheafified`: **the cocycle condition, with
  nothing carried.**

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
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


/-- The composite of the first four factors of
`AlgebraicGeometry.Stack.liftedSectionsIsoSheafified`: the sections of `F` at `z` read as the
sections of the presheaf of **Stacks 03DS** of `g^*𝓕` over the final object of the small étale
site of `W`. -/
noncomputable def liftedSectionsUpperSheafified {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) [h𝓕 : 𝓕.IsQuasicoherent]
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ) :
    F.presheaf.obj (op z) ⟶
      (quasiCoherentPresheafFunctor (p.obj z).left.1
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).obj
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) :=
  (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).inv ≫
    (liftedSmallEtaleIsoSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom.app
      (op (smallEtaleFinal B E h S hS p z)) ≫
    (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
      (op (smallEtaleFinal B E h S hS p z))

/-- `AlgebraicGeometry.Stack.liftedSectionsIsoSheafified` is
`AlgebraicGeometry.Stack.liftedSectionsUpperSheafified` followed by the base-change identification
of **Stacks 03DS**, read backwards, and a restriction map. -/
theorem liftedSectionsIsoSheafified_hom_eq {x z : 𝒳} (φ : z ⟶ x)
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
    letI := h𝓕
    ∃ e : (Over.mk (B.inclusion.map (p.map φ).left) : Over (p.obj x).left.1) ⟶
        (Over.map (B.inclusion.map (p.map φ).left)).obj
          ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
            (smallEtaleFinal B E h S hS p z)),
      e.left = 𝟙 _ ∧
      (liftedSectionsIsoSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom =
        liftedSectionsUpperSheafified B E h S hS p hp F hlqc φ 𝓕 hMx eU hiso ≫
          ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕
              (Over.mk (B.inclusion.map (p.map φ).left))).inv.app
            (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
              (smallEtaleFinal B E h S hS p z))) ≫
            (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map e.op) := by
  let := h𝓕
  refine ⟨(Over.isoMk (Iso.refl _) (by simp)).hom, rfl, ?_⟩
  unfold liftedSectionsIsoSheafified liftedSectionsUpperSheafified
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rfl

/-- **The factor-four square** for
`AlgebraicGeometry.Stack.liftedSectionsUpperSheafified`: at a composable pair of arrows along
which the comparison maps of sheaves of **Stacks 06WC** are isomorphisms, restriction of `F` along
`ψ` followed by the identification at `φ'` is the identification at `φ` followed by restriction,
base change and the composition isomorphism of the pullback pseudofunctor. It is proved as
`AlgebraicGeometry.Stack.liftedSectionsFactorFourSquareSheafified_of_compat`. -/
def LiftedSectionsFactorFourSquareSheafified : Prop :=
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
    {z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x) (_hφ' : φ' = ψ ≫ φ)
    (hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left)
    (hiso : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ)
    (hiso' : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ')
    (n : (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
          (smallEtaleFinal B E h S hS p z')) ⟶
      (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z))
    (_hn : n.left = B.inclusion.map (p.map ψ).left),
    letI := h𝓕
    F.presheaf.map ψ.op ≫ liftedSectionsUpperSheafified B E h S hS p hp F hlqc φ' 𝓕 hMx eU hiso' =
      liftedSectionsUpperSheafified B E h S hS p hp F hlqc φ 𝓕 hMx eU hiso ≫
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

/-- The pasting of the two squares, with every object and arrow abstract. -/
private theorem paste_squares {P P' Q Q' R T T' : AddCommGrpCat.{u}}
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

/-- **The cocycle condition for
`AlgebraicGeometry.Stack.liftedSectionsIsoSheafified`, over the factor-four square**, at one
composable pair. -/
theorem liftedSectionsCocycleSheafified_at_belowArrowSite
    (hf4 : LiftedSectionsFactorFourSquareSheafified B E h S hS p hp) {x : 𝒳}
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
    (hiso' : IsIsoSheafifiedComparison B E h S hS p hp F hlqc φ') :
    F.presheaf.map ψ.op ≫
        (liftedSectionsIsoSheafified B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx eU hiso').hom =
      (liftedSectionsIsoSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (belowArrowSite B S hS p ψ φ φ' hφ').op := by
  let := h𝓕
  have hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left := by
    rw [hφ', p.map_comp]
    exact B.inclusion.map_comp _ _
  obtain ⟨e, he, hfac⟩ := liftedSectionsIsoSheafified_hom_eq B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU
      hiso
  obtain ⟨e', he', hfac'⟩ := liftedSectionsIsoSheafified_hom_eq B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx
      eU hiso'
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

/-- **The cocycle condition for
`AlgebraicGeometry.Stack.liftedSectionsIsoSheafified`, over the factor-four square.** -/
theorem liftedSectionsCocycleSheafified_of_factorFourSquare
    (hf4 : LiftedSectionsFactorFourSquareSheafified B E h S hS p hp) :
    LiftedSectionsCocycleSheafified B E h S hS p hp := by
  intro F hlqc x 𝓕 h𝓕 hMx eU z' z ψ φ φ' hφ' hiso hiso'
  exact liftedSectionsCocycleSheafified_at_belowArrowSite B E h S hS p hp F hlqc hf4 𝓕 h𝓕 hMx eU ψ φ
      φ'
    hφ' hiso hiso'

/-- A left inverse of the forward map of an isomorphism is a right inverse. -/
private theorem right_inv_of_left_inv {X Y : AddCommGrpCat.{u}} (e : X ≅ Y) (s : Y ⟶ X)
    (hs : e.hom ≫ s = 𝟙 X) : s ≫ e.hom = 𝟙 Y := by
  have hse : s = e.inv := by
    rw [← Category.id_comp s, ← e.inv_hom_id, Category.assoc, hs, Category.comp_id]
  rw [hse, e.inv_hom_id]

/-- The category algebra of the factor-four square, with every object and arrow abstract. -/
private theorem factor_four_algebra
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ O₁₃ : AddCommGrpCat.{u}}
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

/-- The prefix split: stripping the invertible head of the identification. -/
private theorem split_prefix {O₁ O₂ O₃ O₄ O₅ : AddCommGrpCat.{u}}
    (fzh : O₂ ⟶ O₁) (fzi : O₁ ⟶ O₂) (lh : O₂ ⟶ O₃) (li : O₃ ⟶ O₂)
    (t : O₁ ⟶ O₄) (ap : O₃ ⟶ O₅) (rest : O₅ ⟶ O₄)
    (hfz : fzi ≫ fzh = 𝟙 O₁) (hl : lh ≫ li = 𝟙 O₂)
    (key : li ≫ fzh ≫ t = ap ≫ rest) :
    t = (fzi ≫ lh ≫ ap) ≫ rest := by
  rw [Category.assoc, Category.assoc, ← key, ← Category.assoc lh li, hl, Category.id_comp,
    ← Category.assoc, hfz, Category.id_comp]

/-- **The factor-four square, over the compatibility of the two base changes on sections**: the
proof of `AlgebraicGeometry.Stack.liftedSectionsFactorFourSquare_of_compat`, under the sheaf-level
comparison. -/
theorem liftedSectionsFactorFourSquareSheafified_of_compat
    (hc : AssociatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp) :
    LiftedSectionsFactorFourSquareSheafified B E h S hS p hp := by
  intro F hlqcF x 𝓕 h𝓕 hMx eU z' z ψ φ φ' hφ' hkg hiso hiso' n hn
  let := h𝓕
  subst hφ'
  have hM : ∀ w : 𝒳, Presheaf.IsSheaf (SmallEtale.topology E (p.obj w).left.1
      (contains_base B E h S hS p w))
      (restrictModuleToSmallEtale B E h S hS p hp w (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf := fun w => (hlqcF.2 w).choose
  rw [Stacks.Sites.pullbackCompSectionsIsoOfEq_hom]
  unfold liftedSectionsUpperSheafified
  -- `h3`: the composition law for factors 2, 3, 4 at sheaf level, with factor 4 peeled off
  have h3 : (PresheafOfModules.sheafification
            (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
              (contains_base B E h S hS p z')).obj)).map
            ((PresheafOfModules.pullback.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                (etaleTopology_le_topology B))).map
              ((SheafOfModules.forget _).map
                (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx (hM z) eU.hom))) ≫
          sheafifiedRestrictComparison B E h S hS p hp F ψ (hM z') =
        (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ
            ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom ≫
          (SmallEtale.associatedModule E (p.obj z').left.1
              (contains_base B E h S hS p z')).map
            ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
              (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left)
              (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕) ≫
          liftedSmallEtaleSheafInv B E h S hS p hp F (ψ ≫ φ) 𝓕 hMx (hM z') eU.hom := by
    rw [← liftedSmallEtaleSheafInv_comp B E h S hS p hp F ψ φ 𝓕 hMx (hM z) (hM z') eU.hom,
      liftedSmallEtaleSheafInv_eq B E h S hS p hp F ψ
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) (hM z) (hM z')
        (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx (hM z) eU.hom),
      Iso.hom_inv_id_assoc]
    rfl
  -- `e1`: factors 3 and 4 read on sections at the final object
  have e1 := smallEtaleFinalPullbackUnit_comp_sheafifiedFactor B E h S hS p hp ψ F (hM z')
    ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val
    ((SheafOfModules.forget _).map
      (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx (hM z) eU.hom))
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
  have hfinal := h4.symm.trans e1
  simp only [Functor.map_comp, NatTrans.comp_app] at hfinal
  -- `hA`: factors 2, 3, 4 are inverse to the identification, at `ψ ≫ φ`
  have hA := NatTrans.congr_app (liftedSmallEtaleIsoSheafified_hom_comp_sheafInv B E h S hS p hp F
      hlqcF
    (ψ ≫ φ) 𝓕 h𝓕 hMx (hM z') eU hiso') (op (smallEtaleFinal B E h S hS p z'))
  simp only [NatTrans.id_app] at hA
  have hsi := right_inv_of_left_inv
    ((liftedSmallEtaleIsoSheafified B E h S hS p hp F hlqcF (ψ ≫ φ) 𝓕 h𝓕 hMx eU hiso').app
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
  have hl := NatTrans.congr_app (liftedSmallEtaleIsoSheafified_hom_comp_sheafInv B E h S hS p hp F
      hlqcF
    φ 𝓕 h𝓕 hMx (hM z) eU hiso) (op (smallEtaleFinal B E h S hS p z))
  simp only [NatTrans.id_app] at hl
  refine split_prefix
    (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).hom _ _
    (((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map
        (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx (hM z) eU.hom))).app
      (op (smallEtaleFinal B E h S hS p z)))
    _ _ _ (Iso.inv_hom_id _) hl ?_
  exact factor_four_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfinal hsi hnat
    (hc ψ ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) inferInstance n hn)

/-- **The cocycle condition for the sections identification of Stacks 076T, under the
sheaf-level comparison, with nothing carried.** -/
theorem liftedSectionsCocycleSheafified : LiftedSectionsCocycleSheafified B E h S hS p hp :=
  liftedSectionsCocycleSheafified_of_factorFourSquare B E h S hS p hp
    (liftedSectionsFactorFourSquareSheafified_of_compat B E h S hS p hp
      (associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp))

end AlgebraicGeometry.Stack

end
