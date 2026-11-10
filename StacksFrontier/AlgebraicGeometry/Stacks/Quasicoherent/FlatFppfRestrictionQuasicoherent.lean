module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AssociatedModuleBaseChangeFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilyFromDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsOfSheafifiedComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence

/-!
# The restriction of `LQCoh^fbc` to the flat-fppf site is quasi-coherent (Stacks 07B1 (2)(b))

Let `𝒳` be an algebraic stack and `F` a module on its fppf site lying in `LQCoh^fbc(𝒪_𝒳)`, with
the flat base change property of **Stacks 0762** read with the pullback of sheaves (the class
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`).  This file proves
**Stacks 07B1** (2)(b): the restriction `g^{-1}F` of `F` to the flat-fppf site of **Stacks 0787**
is a quasi-coherent module on that ringed site (**Stacks 03DL**).

## The argument

Fix a flat object `y` over the scheme `V`, and a quasi-coherent `𝒪_V`-module `𝓕` with
`𝓕^a ≅ F|_{V_ét}` (local quasi-coherence).  For a flat `z ⟶ y` over `g : W ⟶ V`, the comparison
map of **Stacks 06WC** induces an isomorphism of sheaves along `z ⟶ y`, both ends being flat
objects (`AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_flatObject`), so the
identification of **Stacks 076T**, `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`,
gives `F(z) ≅ Γ(W, g^*𝓕)`, naturally in `z` by its cocycle condition.  This file proves that the
identification is *linear* (`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified_hom_smul`), so
the localization of `g^{-1}F` at `y` is, as a sheaf of modules, the restriction of the associated
module `𝓕^a` of the big fppf site of `V` along the functor `(z ⟶ y) ↦ (W ⟶ V)`, which is
continuous and cocontinuous.  `𝓕^a` is quasi-coherent (**Stacks 03DV**), restriction along such a
functor preserves quasi-coherence, and quasi-coherence is local (**Stacks 03DN**).

## Main results

* `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified_hom_smul`: the identification of
  sections of Stacks 076T is linear.
* `AlgebraicGeometry.Stack.subcategorySliceModuleIso`: the localization at a flat object `y` of
  the restriction of `F` is the restriction of the associated module of the quasi-coherent module
  below `y`.
* `AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_moduleRestriction`: **Stacks 07B1**
  (2)(b).

## References

* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

/-- Restricting a sheaf of modules along two continuous functors in turn is restricting its
underlying presheaf of modules along their composite. -/
def CategoryTheory.SheafOfModules.pushforwardPushforwardValIso {C₁ C₂ C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃] {J₁ : GrothendieckTopology C₁}
    {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃} (G₂ : C₁ ⥤ C₂) (G₁ : C₂ ⥤ C₃)
    [G₂.IsContinuous J₁ J₂]
    [G₁.IsContinuous J₂ J₃] {R : Sheaf J₃ RingCat.{u}} (M : SheafOfModules.{u} R) :
    ((SheafOfModules.pushforward.{u} (F := G₂) (𝟙 ((G₂.sheafPushforwardContinuous RingCat.{u}
      J₁ J₂).obj ((G₁.sheafPushforwardContinuous RingCat.{u} J₂ J₃).obj R)))).obj
        ((SheafOfModules.pushforward.{u} (F := G₁)
          (𝟙 ((G₁.sheafPushforwardContinuous RingCat.{u} J₂ J₃).obj R))).obj M)).val ≅
      (PresheafOfModules.pushforward₀ (G₂ ⋙ G₁) R.obj).obj M.val :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Steps

/-- The morphism of abelian presheaves underlying a morphism of presheaves of modules is linear
on sections. -/
theorem _root_.CategoryTheory.PresheafOfModules.toPresheaf_map_app_smul {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}}
    {P Q : PresheafOfModules.{u} R} (g : P ⟶ Q) (X : Cᵒᵖ) (r : R.obj X) (t : P.obj X) :
    (show Q.obj X from ((PresheafOfModules.toPresheaf R).map g).app X (r • t : P.obj X)) =
      r • (show Q.obj X from ((PresheafOfModules.toPresheaf R).map g).app X t) :=
  (g.app X).hom.map_smul r t

/-- **The identification of the global sections of a small étale restriction is semilinear.** -/
theorem restrictModuleToSmallEtaleFinalIso_inv_smul (z : 𝒳) (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (r : (ringStructureSheafCore B S hS p hp τ hτ).obj.obj (op z)) (s : F.obj (op z)) :
    (show (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).obj
        (op (smallEtaleFinal B E h S hS p z)) from
      (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z τ hτ F).inv (r • s : F.obj (op z))) =
      (show (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj.obj (op (smallEtaleFinal B E h S hS p z)) from
        (localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app
          (op (smallEtaleFinal B E h S hS p z))
          ((ringStructureSheafCore B S hS p hp τ hτ).obj.map
            (smallEtaleFinalObjectIso B E h S hS p hp z).hom.op r)) •
        (show (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).obj
          (op (smallEtaleFinal B E h S hS p z)) from
          (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z τ hτ F).inv s) := by
  change F.map (smallEtaleFinalObjectIso B E h S hS p hp z).hom.op (r • s) =
    (localStructurePresheafIso B E h S hS p hp z τ hτ).hom.app
      (op (smallEtaleFinal B E h S hS p z))
      ((localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app
        (op (smallEtaleFinal B E h S hS p z))
        ((ringStructureSheafCore B S hS p hp τ hτ).obj.map
          (smallEtaleFinalObjectIso B E h S hS p hp z).hom.op r)) •
      F.map (smallEtaleFinalObjectIso B E h S hS p hp z).hom.op s
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
  exact PresheafOfModules.map_smul F _ r s

/-- **The base change identification of the presheaf of Stacks 03DS is linear**, for the
module structures transported from the global sections of the pullbacks. -/
theorem _root_.Stacks.Sites.quasiCoherentPresheafBaseChangeIso_inv_app_smul {T : Scheme.{u}}
    (G : T.Modules)
    [G.IsQuasicoherent] (X : Over T) (A : Over X.left) (r : Γ(A.left, ⊤))
    (m : (quasiCoherentSectionsPresheaf X.left ((Scheme.Modules.pullback X.hom).obj G) (𝟭 _)).obj
      (op A)) :
    letI := quasiCoherentSectionsModule X.left ((Scheme.Modules.pullback X.hom).obj G) (𝟭 _)
      (op A)
    letI := quasiCoherentSectionsModule T G (𝟭 _) (op ((Over.map X.hom).obj A))
    (show (quasiCoherentSectionsPresheaf T G (𝟭 _)).obj (op ((Over.map X.hom).obj A)) from
      (Stacks.Sites.quasiCoherentPresheafBaseChangeIso G X).inv.app (op A)
        ((show (Stacks.Sites.structurePresheaf X.left (𝟭 _)).obj (op A) from r) • m)) =
      (show (Stacks.Sites.structurePresheaf T (𝟭 _)).obj (op ((Over.map X.hom).obj A)) from r) •
        (show (quasiCoherentSectionsPresheaf T G (𝟭 _)).obj (op ((Over.map X.hom).obj A)) from
          (Stacks.Sites.quasiCoherentPresheafBaseChangeIso G X).inv.app (op A) m) := by
  let := quasiCoherentSectionsModule X.left ((Scheme.Modules.pullback X.hom).obj G) (𝟭 _)
      (op A)
  let := quasiCoherentSectionsModule T G (𝟭 _) (op ((Over.map X.hom).obj A))
  let P := quasiCoherentPresheaf T G
  let Q := quasiCoherentPresheaf X.left ((Scheme.Modules.pullback X.hom).obj G)
  have hinv : ∀ n, (Stacks.Sites.quasiCoherentPresheafBaseChangeIso G X).inv.app (op A) n =
      (P.objIso (op ((Over.map X.hom).obj A))).inv
        (((Scheme.Modules.pullbackComp A.hom X.hom).hom.app G).app ⊤
          ((Q.objIso (op A)).hom n)) := fun n => rfl
  change (Stacks.Sites.quasiCoherentPresheafBaseChangeIso G X).inv.app (op A)
      ((Q.objIso (op A)).inv (r • (Q.objIso (op A)).hom m)) =
    (P.objIso (op ((Over.map X.hom).obj A))).inv
      (r • (P.objIso (op ((Over.map X.hom).obj A))).hom
        ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso G X).inv.app (op A) m))
  rw [hinv, hinv, ← ConcreteCategory.comp_apply (Q.objIso (op A)).inv, Iso.inv_hom_id,
    ← ConcreteCategory.comp_apply _ (P.objIso _).hom, Iso.inv_hom_id]
  simp only [ConcreteCategory.id_apply]
  rw [Scheme.Modules.Hom.app_smul]

/-- Restricting a function along the identification of `z` with the object carrying the global
sections of the small étale restriction, and reading it in the small étale structure sheaf,
returns the function itself. -/
theorem localStructurePresheafIso_inv_app_final (z : 𝒳) (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology) (r : (ringStructureSheafCore B S hS p hp τ hτ).obj.obj (op z)) :
    (localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app
        (op (smallEtaleFinal B E h S hS p z))
        ((ringStructureSheafCore B S hS p hp τ hτ).obj.map
          (smallEtaleFinalObjectIso B E h S hS p hp z).hom.op r) =
      (show (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj.obj (op (smallEtaleFinal B E h S hS p z)) from
        r) := by
  have := isEquivalence_overPost B S hS p hp z
  let b := Over.post (X := z) (p ⋙ Over.forget (B.obj hS))
  let V0 := (smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z)).obj
    (smallEtaleFinal B E h S hS p z)
  let e := (IsTerminal.isTerminalObj b.inv V0
    (isTerminal_smallEtaleInclusion_obj_final B E h S hS p z)).uniqueUpToIso Over.mkIdTerminal
  let R := (baseRingStructureSheaf B (p.obj z).left.1 (p.obj z).left.2 τ hτ).obj
  have key : (localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app
        (op (smallEtaleFinal B E h S hS p z))
        ((ringStructureSheafCore B S hS p hp τ hτ).obj.map
          (smallEtaleFinalObjectIso B E h S hS p hp z).hom.op r) =
      R.map (b.asEquivalence.counitInv.app V0).op (R.map (b.map e.hom).op r) := rfl
  let m : V0 ⟶ b.obj (Over.mk (𝟙 z)) := b.asEquivalence.counitInv.app V0 ≫ b.map e.hom
  have hc : R.map (b.asEquivalence.counitInv.app V0).op (R.map (b.map e.hom).op r) =
      R.map m.op r :=
    (congrArg (fun φ : R.obj (op (b.obj (Over.mk (𝟙 z)))) ⟶ R.obj (op V0) =>
        ConcreteCategory.hom φ r)
      (R.map_comp (b.map e.hom).op (b.asEquivalence.counitInv.app V0).op)).symm
  have hm : m.left = 𝟙 _ :=
    (Category.comp_id m.left).symm.trans
      ((congrArg (fun t => m.left ≫ t) ((p ⋙ Over.forget (B.obj hS)).map_id z).symm).trans
        (Over.w m))
  have hR : R.map m.op r = (forget₂ CommRingCat RingCat).map
      (Scheme.Γ.map (B.inclusion.map m.left).op) r := rfl
  refine key.trans (hc.trans (hR.trans ?_))
  rw [hm]
  rfl

/-- **The restriction maps of the presheaf of Stacks 03DS are semilinear**, read at an object
of the big fppf site of a scheme `V` and an arrow of schemes over `V` out of it. -/
theorem _root_.AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules_map_smul
    (V : Scheme.{u}) (hV : B.Contains V) (𝓕 : V.Modules) [𝓕.IsQuasicoherent]
    (Y : BigFppfOver B V hV) (A : Over V) (f : (Over.post B.inclusion).obj Y ⟶ A)
    (c : (Stacks.Sites.structurePresheaf V (𝟭 _)).obj (op A))
    (t : (quasiCoherentSectionsPresheaf V 𝓕 (𝟭 _)).obj (op A)) :
    letI := quasiCoherentSectionsModule V 𝓕 (𝟭 _) (op A)
    (show (BigFppfOver.sectionsPresheafOfModules B V hV 𝓕).obj (op Y) from
      (quasiCoherentPresheafFunctor V 𝓕).map f.op (c • t)) =
      (show (BigFppfOver.structureSheaf B V hV).obj.obj (op Y) from
        (Stacks.Sites.structurePresheaf V (𝟭 _)).map f.op c) •
        (show (BigFppfOver.sectionsPresheafOfModules B V hV 𝓕).obj (op Y) from
          (quasiCoherentPresheafFunctor V 𝓕).map f.op t) :=
  quasiCoherentSectionsPresheaf_map_smul V 𝓕 (𝟭 _) f.op c t

/-- **The base change identification of Stacks 03DS followed by a restriction map is
semilinear**, read at an object of the big fppf site of a scheme `V`. -/
theorem _root_.AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules_map_baseChange_smul
    (V : Scheme.{u}) (hV : B.Contains V) (𝓕 : V.Modules) [𝓕.IsQuasicoherent]
    (X : Over V) (A : Over X.left) (Y : BigFppfOver B V hV)
    (f : (Over.post B.inclusion).obj Y ⟶ (Over.map X.hom).obj A) (c : Γ(A.left, ⊤))
    (t : (quasiCoherentSectionsPresheaf X.left ((Scheme.Modules.pullback X.hom).obj 𝓕)
      (𝟭 _)).obj (op A)) :
    letI := quasiCoherentSectionsModule X.left ((Scheme.Modules.pullback X.hom).obj 𝓕) (𝟭 _)
      (op A)
    (show (BigFppfOver.sectionsPresheafOfModules B V hV 𝓕).obj (op Y) from
      (quasiCoherentPresheafFunctor V 𝓕).map f.op
        ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕 X).inv.app (op A)
          ((show (Stacks.Sites.structurePresheaf X.left (𝟭 _)).obj (op A) from c) • t))) =
      (show (BigFppfOver.structureSheaf B V hV).obj.obj (op Y) from
        (Stacks.Sites.structurePresheaf V (𝟭 _)).map f.op c) •
        (show (BigFppfOver.sectionsPresheafOfModules B V hV 𝓕).obj (op Y) from
          (quasiCoherentPresheafFunctor V 𝓕).map f.op
            ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕 X).inv.app (op A) t)) := by
  let := quasiCoherentSectionsModule X.left ((Scheme.Modules.pullback X.hom).obj 𝓕) (𝟭 _)
    (op A)
  let := quasiCoherentSectionsModule V 𝓕 (𝟭 _) (op ((Over.map X.hom).obj A))
  exact (congrArg (fun m => (show (BigFppfOver.sectionsPresheafOfModules B V hV 𝓕).obj (op Y)
      from (quasiCoherentPresheafFunctor V 𝓕).map f.op m))
      (Stacks.Sites.quasiCoherentPresheafBaseChangeIso_inv_app_smul 𝓕 X A c t)).trans
    (BigFppfOver.sectionsPresheafOfModules_map_smul B V hV 𝓕 Y _ f c _)

end Steps

section Linear

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

/-- **The identification of sections of Stacks 076T is linear.**  For an arrow `φ : z ⟶ x`
along which the comparison map of Stacks 06WC induces an isomorphism of sheaves, the
identification `F(z) ≅ Γ(W, g^*𝓕)` of `AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`
commutes with multiplication by the functions on `W`. -/
theorem liftedSectionsIsoOfSheafified_hom_smul {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ (hlqc.2 _).choose))
    (r : (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj.obj (op z)) (s : F.obj (op z)) :
    letI := h𝓕
    (show (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕).obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from
      (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom
        (r • s : F.obj (op z))) =
      (show (BigFppfOver.structureSheaf B (p.obj x).left.1 (p.obj x).left.2).obj.obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from r) •
        (show (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2 𝓕).obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from
          (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom s) := by
  let := h𝓕
  -- the names of the five factors of the identification
  let fin := smallEtaleFinal B E h S hS p z
  let Wz := (p.obj z).left.1
  let hWz := contains_base B E h S hS p z
  let G := (Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕
  let T := (SmallEtale.toOver E Wz hWz).obj fin
  let X : Over (p.obj x).left.1 := Over.mk (B.inclusion.map (p.map φ).left)
  let e1 := restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
    (etaleTopology_le_topology B) F
  let e2 := (liftedSmallEtaleIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 hMx eU hiso).app
    (op fin)
  let e3 := (SmallEtale.associatedModulePresheafIso E Wz hWz G).app (op fin)
  let e4 := (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕 X).inv.app (op T)
  let i5 : (Over.post B.inclusion).obj (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ)) ≅
      (Over.map X.hom).obj T := Over.isoMk (Iso.refl _) (by
        simp [T, fin, X, smallEtaleFinal, SmallEtale.final, Over.post])
  let e5 := (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map i5.hom.op
  have hdef : ∀ t : F.obj (op z),
      (liftedSectionsIsoOfSheafified B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom t =
        e5 (e4 (e3.hom (e2.hom (e1.inv t)))) := fun t => rfl
  -- the ring element at the final object of the small étale site
  let ρ : (SmallEtale.structureSheaf E Wz hWz).obj.obj (op fin) :=
    (localStructurePresheafIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B)).inv.app (op fin)
      ((ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj.map
        (smallEtaleFinalObjectIso B E h S hS p hp z).hom.op r)
  have hρ : ρ = (show (SmallEtale.structureSheaf E Wz hWz).obj.obj (op fin) from r) :=
    localStructurePresheafIso_inv_app_final B E h S hS p hp z _ _ r
  have s1 : (show (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).obj (op fin) from e1.inv (r • s : F.obj (op z))) =
      ρ • (show (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).obj (op fin) from e1.inv s) :=
    restrictModuleToSmallEtaleFinalIso_inv_smul B E h S hS p hp z _ _ F r s
  have s2 : ∀ (c : (SmallEtale.structureSheaf E Wz hWz).obj.obj (op fin))
      (t : (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).obj (op fin)),
      (show ((SmallEtale.associatedModule E Wz hWz).obj G).val.obj (op fin) from
        e2.hom (c • t)) =
        c • (show ((SmallEtale.associatedModule E Wz hWz).obj G).val.obj (op fin) from
          e2.hom t) := by
    intro c t
    exact PresheafOfModules.toPresheaf_map_app_smul _ _ c t
  have s3 : ∀ (c : (SmallEtale.structureSheaf E Wz hWz).obj.obj (op fin))
      (t : ((SmallEtale.associatedModule E Wz hWz).obj G).val.obj (op fin)),
      (show (SmallEtale.sectionsPresheafOfModules E Wz hWz G).obj (op fin) from
        e3.hom (c • t)) =
        c • (show (SmallEtale.sectionsPresheafOfModules E Wz hWz G).obj (op fin) from
          e3.hom t) := by
    intro c t
    exact PresheafOfModules.toPresheaf_map_app_smul _ _ c t
  let := quasiCoherentSectionsModule X.left ((Scheme.Modules.pullback X.hom).obj 𝓕) (𝟭 _)
    (op T)
  let := quasiCoherentSectionsModule (p.obj x).left.1 𝓕 (𝟭 _) (op ((Over.map X.hom).obj T))
  let := quasiCoherentSectionsModule (p.obj x).left.1 𝓕 (𝟭 _)
    (op ((Over.post B.inclusion).obj (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))))
  have s4 : ∀ (c : Γ(T.left, ⊤)) (t : (quasiCoherentSectionsPresheaf X.left
      ((Scheme.Modules.pullback X.hom).obj 𝓕) (𝟭 _)).obj (op T)),
      (show (quasiCoherentSectionsPresheaf (p.obj x).left.1 𝓕 (𝟭 _)).obj
          (op ((Over.map X.hom).obj T)) from
        e4 ((show (Stacks.Sites.structurePresheaf X.left (𝟭 _)).obj (op T) from c) • t)) =
        (show (Stacks.Sites.structurePresheaf (p.obj x).left.1 (𝟭 _)).obj
          (op ((Over.map X.hom).obj T)) from c) •
          (show (quasiCoherentSectionsPresheaf (p.obj x).left.1 𝓕 (𝟭 _)).obj
            (op ((Over.map X.hom).obj T)) from e4 t) :=
    fun c t => Stacks.Sites.quasiCoherentPresheafBaseChangeIso_inv_app_smul 𝓕 X T c t
  have hring : (show (BigFppfOver.structureSheaf B (p.obj x).left.1 (p.obj x).left.2).obj.obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from
        (Stacks.Sites.structurePresheaf (p.obj x).left.1 (𝟭 _)).map i5.hom.op
          (show (Stacks.Sites.structurePresheaf (p.obj x).left.1 (𝟭 _)).obj
            (op ((Over.map X.hom).obj T)) from ρ)) =
      (show (BigFppfOver.structureSheaf B (p.obj x).left.1 (p.obj x).left.2).obj.obj
          (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from r) := by
    change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (𝟙 _).op) ρ = r
    rw [hρ]
    simp only [op_id, CategoryTheory.Functor.map_id]
    rfl
  have c1 := congrArg (fun t => (show (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1
      (p.obj x).left.2 𝓕).obj (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from
        e5 (e4 (e3.hom (e2.hom t))))) s1
  let t1 : (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
    (etaleTopology_le_topology B) F).obj (op fin) := e1.inv s
  let t2 : ((SmallEtale.associatedModule E Wz hWz).obj G).val.obj (op fin) := e2.hom t1
  let t3 : (SmallEtale.sectionsPresheafOfModules E Wz hWz G).obj (op fin) := e3.hom t2
  have c2 := congrArg (fun t => (show (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1
      (p.obj x).left.2 𝓕).obj (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from
        e5 (e4 (e3.hom t)))) (s2 ρ t1)
  have c3 := congrArg (fun t => (show (BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1
      (p.obj x).left.2 𝓕).obj (op (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ))) from
        e5 (e4 t))) (s3 ρ t2)
  have c45 := BigFppfOver.sectionsPresheafOfModules_map_baseChange_smul B (p.obj x).left.1
    (p.obj x).left.2 𝓕 X T (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ)) i5.hom ρ t3
  refine c1.trans ?_
  refine c2.trans ?_
  refine c3.trans ?_
  refine c45.trans ?_
  rw [hdef s]
  congr 1

end Linear

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

section SubcategorySlice

variable {B : BigFppfSite.{u}} {E : BigEtaleSite.{u}} {h : E.cutoff = B.cutoff}
  {S : Scheme.{u}} {hS : B.Contains S} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (P : ObjectProperty 𝒳.val.val.obj) (hP : ∀ x, P x → flatObject B S hS 𝒳.val x)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
  (hF : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F)
  (y : P.FullSubcategory)
  (d : QuasicoherentBelow B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F y.obj)

/-- For a full subcategory of flat objects of an algebraic stack, the functor localized at an
object `y`: an arrow `z ⟶ y` goes to the morphism of schemes below it, an object of the big site
of the scheme below `y`. -/
abbrev subcategorySliceFunctor : Over y ⥤ BigFppfOver B (𝒳.val.val.p.obj y.obj).left.1
    (𝒳.val.val.p.obj y.obj).left.2 :=
  Over.post (X := y) (P.ι ⋙ 𝒳.val.val.p ⋙ Over.forget (B.obj hS))

include hP hF in
/-- Along the structure arrow of an object of a full subcategory of flat objects localized at
`y`, the comparison map of Stacks 06WC induces an isomorphism of sheaves: both ends are flat. -/
theorem isIso_sheafifiedRestrictComparison_subcategoryOverHom (X : Over y) :
    IsIso (sheafifiedRestrictComparison B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F
      X.hom.hom (hF.1.2 X.left.obj).choose) :=
  isIso_sheafifiedRestrictComparison_of_flatObject B E h S hS 𝒳 F hF (hP _ X.left.property)
    (hP _ y.property) X.hom.hom _

/-- The restriction of `F` along the composite of the localization at `y` and the inclusion of
the subcategory, as a presheaf of modules. -/
abbrev subcategorySliceSource :
    PresheafOfModules.{u} ((Over.forget y ⋙ P.ι).op ⋙ (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj) :=
  (PresheafOfModules.pushforward₀ (Over.forget y ⋙ P.ι) (ringStructureSheafCore B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B)).obj).obj F

/-- The ring of `AlgebraicGeometry.Stack.subcategorySliceSource` is the restriction of the
structure sheaf of the big site of the scheme below `y` along the slice functor. -/
theorem subcategorySliceRing_eq :
    (Over.forget y ⋙ P.ι).op ⋙ (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj =
      (subcategorySliceFunctor P y).op ⋙ (BigFppfOver.structureSheaf B
        (𝒳.val.val.p.obj y.obj).left.1 (𝒳.val.val.p.obj y.obj).left.2).obj :=
  rfl

/-- The restriction along the slice functor of the pullback-sections presheaf of the
quasi-coherent module below `y`, as a presheaf of modules over the same ring as
`AlgebraicGeometry.Stack.subcategorySliceSource`. -/
abbrev subcategorySliceTarget :
    PresheafOfModules.{u} ((Over.forget y ⋙ P.ι).op ⋙ (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj) :=
  (PresheafOfModules.pushforward₀ (subcategorySliceFunctor P y)
      (BigFppfOver.structureSheaf B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2).obj ⋙
    PresheafOfModules.restrictScalars (eqToHom (subcategorySliceRing_eq P y))).obj
    (@BigFppfOver.sectionsPresheafOfModules B (𝒳.val.val.p.obj y.obj).left.1
      (𝒳.val.val.p.obj y.obj).left.2 d.val d.isQuasicoherent)

/-- **The sections of `F` over the objects of the subcategory over `y` are the sections of the
associated module of the quasi-coherent module below `y`**, as presheaves of abelian groups:
the identification of Stacks 076T (`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`),
natural by its cocycle condition. -/
def subcategorySliceSectionsIso :
    (subcategorySliceSource P F y).presheaf ≅ (subcategorySliceTarget P F y d).presheaf :=
  NatIso.ofComponents (fun X => liftedSectionsIsoOfSheafified B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F hF.1 X.unop.hom.hom d.val d.isQuasicoherent d.isSheaf
      d.iso (isIso_sheafifiedRestrictComparison_subcategoryOverHom P hP F hF y X.unop))
    (fun {X Y} f => by
      have hφ' : Y.unop.hom.hom = f.unop.left.hom ≫ X.unop.hom.hom :=
        (congrArg (fun g => g.hom) (Over.w f.unop)).symm
      exact liftedSectionsCocycleOfSheafified_of_factorFourSquare B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (liftedSectionsFactorFourSquareOfSheafified_of_compat B E h S
          hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (associatedModuleBaseChangeFinalSectionsCompat B E h S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids)) F hF.1 d.val d.isQuasicoherent d.isSheaf d.iso
        f.unop.left.hom X.unop.hom.hom Y.unop.hom.hom hφ'
        (isIso_sheafifiedRestrictComparison_subcategoryOverHom P hP F hF y X.unop)
        (isIso_sheafifiedRestrictComparison_subcategoryOverHom P hP F hF y Y.unop))

/-- The isomorphism `AlgebraicGeometry.Stack.subcategorySliceSectionsIso` is linear
(`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified_hom_smul`): it is an isomorphism of
presheaves of modules. -/
def subcategorySliceModuleIso : subcategorySliceSource P F y ≅ subcategorySliceTarget P F y d :=
  haveI : IsIso (PresheafOfModules.homMk (M₁ := subcategorySliceSource P F y)
      (M₂ := subcategorySliceTarget P F y d)
      (subcategorySliceSectionsIso P hP F hF y d).hom (fun X r m =>
      liftedSectionsIsoOfSheafified_hom_smul B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F hF.1 X.unop.hom.hom d.val d.isQuasicoherent d.isSheaf
        d.iso (isIso_sheafifiedRestrictComparison_subcategoryOverHom P hP F hF y X.unop) r m)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    exact (inferInstance : IsIso (subcategorySliceSectionsIso P hP F hF y d).hom)
  asIso (PresheafOfModules.homMk (M₁ := subcategorySliceSource P F y)
      (M₂ := subcategorySliceTarget P F y d)
      (subcategorySliceSectionsIso P hP F hF y d).hom (fun X r m =>
      liftedSectionsIsoOfSheafified_hom_smul B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F hF.1 X.unop.hom.hom d.val d.isQuasicoherent d.isSheaf
        d.iso (isIso_sheafifiedRestrictComparison_subcategoryOverHom P hP F hF y X.unop) r m))

end SubcategorySlice

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.FlatFppf

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The functor from the flat-fppf site of an algebraic stack to the big fppf site of schemes
sending a flat object to the scheme below it. -/
abbrev baseFunctor : FlatFppf B S hS 𝒳 ⥤ B.Schemes :=
  inclusion B S hS 𝒳 ⋙ 𝒳.val.val.p ⋙ Over.forget (B.obj hS)

/-- The functor to schemes is continuous for the flat-fppf topology and the fppf topology. -/
instance isContinuous_baseFunctor :
    (baseFunctor B S hS 𝒳).IsContinuous (topology B S hS 𝒳) B.topology := by
  have := isContinuous_inclusion_topology B S hS 𝒳
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have := Stacks.Sites.FibredCategory.isContinuous_inheritedTopology_of_isFibered
    𝒳.val.val.p (B.topology.over (B.obj hS))
  have : (𝒳.val.val.p ⋙ Over.forget (B.obj hS)).IsContinuous
      (associatedTopology B S hS 𝒳.val.val.p B.topology) B.topology :=
    Functor.isContinuous_comp _ _ _ (B.topology.over (B.obj hS)) _
  exact Functor.isContinuous_comp _ _ _ (associatedTopology B S hS 𝒳.val.val.p B.topology) _

/-- The functor to schemes is cocontinuous for the flat-fppf topology and the fppf topology. -/
instance isCocontinuous_baseFunctor :
    (baseFunctor B S hS 𝒳).IsCocontinuous (topology B S hS 𝒳) B.topology := by
  have := isCocontinuous_inclusion_topology B S hS 𝒳
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have := Stacks.Sites.FibredCategory.isCocontinuous_inheritedTopology_of_isFibered
    𝒳.val.val.p (B.topology.over (B.obj hS))
  have : (𝒳.val.val.p ⋙ Over.forget (B.obj hS)).IsCocontinuous
      (associatedTopology B S hS 𝒳.val.val.p B.topology) B.topology :=
    isCocontinuous_comp _ _ _ (B.topology.over (B.obj hS))
  exact isCocontinuous_comp _ _ _ (associatedTopology B S hS 𝒳.val.val.p B.topology)

section Slice

variable (y : FlatFppf B S hS 𝒳)

/-- The slice functor is continuous. -/
instance isContinuous_sliceFunctor :
    (subcategorySliceFunctor (objectProperty B S hS 𝒳) y).IsContinuous ((topology B S hS 𝒳).over y)
      (BigFppfOver.baseOverTopology B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .fppf) :=
  Functor.isContinuous_overPost (topology B S hS 𝒳) B.topology (baseFunctor B S hS 𝒳) y

/-- The slice functor is cocontinuous. -/
instance isCocontinuous_sliceFunctor :
    (subcategorySliceFunctor (objectProperty B S hS 𝒳) y).IsCocontinuous
      ((topology B S hS 𝒳).over y)
      (BigFppfOver.baseOverTopology B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .fppf) :=
  inferInstanceAs ((Over.post (X := y) (baseFunctor B S hS 𝒳)).IsCocontinuous
    ((topology B S hS 𝒳).over y) (B.topology.over ((baseFunctor B S hS 𝒳).obj y)))

/-- The localizations of the slice functor are continuous. -/
instance isContinuous_overPost_sliceFunctor (X : Over y) :
    (Over.post (X := X) (subcategorySliceFunctor (objectProperty B S hS 𝒳) y)).IsContinuous
      (((topology B S hS 𝒳).over y).over X)
      ((BigFppfOver.baseOverTopology B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .fppf).over
          ((subcategorySliceFunctor (objectProperty B S hS 𝒳) y).obj X)) :=
  Functor.isContinuous_overPost _ _ (subcategorySliceFunctor (objectProperty B S hS 𝒳) y) X

/-- The structure sheaf of the flat-fppf site, localized at `y`, is the restriction of the
structure sheaf of the big fppf site of the scheme below `y` along the slice functor. -/
theorem ringSheaf_over_obj_eq :
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (structureSheaf B S hS 𝒳)).over y).obj =
      (subcategorySliceFunctor (objectProperty B S hS 𝒳) y).op ⋙
        (FibredSite.baseRingStructureSheaf B (𝒳.val.val.p.obj y.obj).left.1
          (𝒳.val.val.p.obj y.obj).left.2 .fppf).obj :=
  rfl

/-- **The restriction along the slice functor of the associated module of a quasi-coherent
module on the scheme below `y` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_sliceRestriction (𝓕 : (𝒳.val.val.p.obj y.obj).left.1.Modules)
    [𝓕.IsQuasicoherent] :
    ((SheafOfModules.restrictAlongContinuous (J := (topology B S hS 𝒳).over y)
      (subcategorySliceFunctor (objectProperty B S hS 𝒳) y) (FibredSite.baseRingStructureSheaf B
        (𝒳.val.val.p.obj y.obj).left.1 (𝒳.val.val.p.obj y.obj).left.2 .fppf)).obj
      (BigFppfOver.sectionsSheafOfModules B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .fppf 𝓕)).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (subcategorySliceFunctor (objectProperty B S hS 𝒳) y) _ _
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B _ _ .fppf 𝓕)
      (BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B _ _ .fppf 𝓕
        inferInstance))

end Slice

section SliceIso

variable {B E h S hS 𝒳} (F : fppfModules B S hS 𝒳)
  (hF : lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F)
  (y : FlatFppf B S hS 𝒳)
  (d : QuasicoherentBelow B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val y.obj)

include hF in
/-- **Stacks 07B1 (2)(b), localized at a flat object.**  The restriction to the flat-fppf site,
localized at a flat object `y`, of a module in `LQCoh^fbc(𝒪_𝒳)` (with the flat base change
property of Stacks 0762 read with the pullback of sheaves) is quasi-coherent. -/
theorem isQuasicoherentOnSite_over_moduleRestriction :
    (((moduleRestriction B S hS 𝒳).obj F).over y).IsQuasicoherentOnSite := by
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    F.val hF.1 y.obj
  have := d.isQuasicoherent
  have := isQuasicoherentOnSite_sliceRestriction B S hS 𝒳 y d.val
  exact SheafOfModules.isQuasicoherentOnSite_of_restrictionIso
    (subcategorySliceFunctor (objectProperty B S hS 𝒳) y)
    (FibredSite.baseRingStructureSheaf B (𝒳.val.val.p.obj y.obj).left.1
      (𝒳.val.val.p.obj y.obj).left.2 .fppf) _ (ringSheaf_over_obj_eq B S hS 𝒳 y)
    (BigFppfOver.sectionsSheafOfModules B (𝒳.val.val.p.obj y.obj).left.1
      (𝒳.val.val.p.obj y.obj).left.2 .fppf d.val) _
    ((@SheafOfModules.pushforwardPushforwardValIso _ _ _ _ _ _ _ _ _ (Over.forget y)
      (inclusion B S hS 𝒳) _ (isContinuous_inclusion_topology B S hS 𝒳) _ F) ≪≫
      subcategorySliceModuleIso (objectProperty B S hS 𝒳) (fun _ hx => hx) F.val hF y d)

end SliceIso

section Restriction

variable {B E h S hS 𝒳} (F : fppfModules B S hS 𝒳)
  (hF : lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F)

include hF in
/-- **Stacks 07B1 (2)(b).**  Let `𝒳` be an algebraic stack and `F` a module in
`LQCoh^fbc(𝒪_𝒳)` — locally quasi-coherent with the flat base change property of Stacks 0762,
read with the pullback of sheaves of `f_{small}^*`.  Then the restriction `g^{-1}F` of `F` to the
flat-fppf site of Stacks 0787 is a quasi-coherent module on that ringed site.

By Stacks 03DN it is enough to check it on the localizations at the flat objects `y`.  There the
sections of `F` over a flat `z ⟶ y`, lying over `W ⟶ V`, are `Γ(W, (W → V)^*𝓕)`, where
`𝓕^a ≅ F|_{V_ét}`: the comparison map of Stacks 06WC is invertible along every arrow between flat
objects (`AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_flatObject`), and the
identification of Stacks 076T (`AlgebraicGeometry.Stack.liftedSectionsIsoOfSheafified`) is
natural and linear.  So the localization is the restriction of `𝓕^a` on the big fppf site of
`V`, which is quasi-coherent (Stacks 03DV), along a continuous and cocontinuous functor. -/
theorem isQuasicoherentOnSite_moduleRestriction :
    ((moduleRestriction B S hS 𝒳).obj F).IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite _).2
    ⟨FlatFppf B S hS 𝒳, fun y => y, fun Y => (topology B S hS 𝒳).superset_covering
      (fun Z _ _ => ⟨Z, ⟨𝟙 Z⟩⟩) ((topology B S hS 𝒳).top_mem Y),
      fun y => isQuasicoherentOnSite_over_moduleRestriction F hF y⟩

end Restriction

end AlgebraicGeometry.Stack.FlatFppf
