module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineSiteAssociatedModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AssociatedModuleBaseChangeFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtalePullbackFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictModulePullback
public import StacksFrontier.LinearAlgebra.TensorProduct.SemilinearExtension

/-!
# The comparison map of Stacks 06WC between affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `F` a presheaf of modules over
its structure sheaf, and `φ : z ⟶ x` an arrow of `𝒳` lying over a morphism `g : W ⟶ U` of
*affine* schemes. Assume the restrictions `F|_{U_ét}` and `F|_{W_ét}` are quasi-coherent sheaves
on the small étale sites. This file proves that the comparison map
`c_φ : g_{small}^*(F|_{U_ét}) ⟶ F|_{W_ét}` of Stacks 06WC is an isomorphism exactly when `F` is
cartesian along `φ`, that is when the base-change map `𝒪(z) ⊗_{𝒪(x)} F(x) ⟶ F(z)` of the
restriction map of `F` along `φ` is bijective.

Both sides of `c_φ` are quasi-coherent on the small étale site of the affine scheme `W`, so `c_φ`
is an isomorphism exactly when it is bijective on the sections over the final object. Read on
those sections through the unit of the pullback of Stacks 06WC, `c_φ` is restriction of `F` along
`φ` (`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp_sheafifiedFactor`); and the unit
itself presents the sections of the pullback over `W` as the base change of the sections over `U`,
because for `F|_{U_ét} = 𝓐^a` it is the pullback of global sections of `𝓐` along `g`
(`AlgebraicGeometry.Stack.associatedModuleBaseChangeFinalSectionsCompat`), which presents
`Γ(W, g^*𝓐)` as `𝒪(W) ⊗_{𝒪(U)} Γ(U, 𝓐)` for affine `U` and `W`.

## Main results

* `AlgebraicGeometry.Stack.smallEtaleStructureComparison_app_final_comp`: the map of structure
  sheaves of Stacks 06WC between the two final objects is restriction of functions along `φ`.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

/-- Two additive maps out of a tensor product are equal when they agree on pure tensors. -/
private theorem coe_eq_of_tmul_eq {R M N P : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] (f g : TensorProduct R M N →+ P)
    (h : ∀ m n, f (TensorProduct.tmul R m n) = g (TensorProduct.tmul R m n)) : ⇑f = ⇑g := by
  funext z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero f).trans (map_zero g).symm
  | tmul m n => exact h m n
  | add z w hz hw =>
    exact (map_add f z w).trans ((congrArg₂ (· + ·) hz hw).trans (map_add g z w).symm)

namespace Stacks.PresheafOfModules

/-- **The base-change comparison of a restriction map is the extension of that restriction map**,
in the sense of `Stacks.SemilinearExtension.extend`. -/
theorem restrictionBaseChange_eq_extend {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) {X Y : Cᵒᵖ}
    (g : X ⟶ Y) :
    letI : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
    ⇑(restrictionBaseChange M g).hom =
      ⇑(Stacks.SemilinearExtension.extend (R.map g).hom (fun _ _ => rfl)
        (M.map g).hom.toAddMonoidHom (fun r m => M.map_smul g r m)) := by
  let : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
  exact coe_eq_of_tmul_eq (restrictionBaseChange M g).hom.toAddMonoidHom _
    fun c m => restrictionBaseChange_tmul M g c m

end Stacks.PresheafOfModules


namespace Stacks.Sites

open AlgebraicGeometry

/-- **The pullback of global sections between affine schemes presents a base change.** For an
arrow `g : X ⟶ Y` of schemes over `S0` with affine total spaces and a quasi-coherent module `𝓖`
on `S0`, the extension of the restriction map of the presheaf of Stacks 03DS along `g`, semilinear
along `g^♯`, is bijective. -/
theorem bijective_extend_pullbackSectionsMap {S0 : Scheme.{u}} (𝓖 : S0.Modules)
    [𝓖.IsQuasicoherent] {X Y : Over S0} [IsAffine X.left] [IsAffine Y.left] (g : X ⟶ Y) :
    letI : Module Γ(Y.left, ⊤) Γ(X.left, ⊤) := Module.compHom _ g.left.appTop.hom
    Function.Bijective (Stacks.SemilinearExtension.extend g.left.appTop.hom (fun _ _ => rfl)
      (pullbackSectionsMap 𝓖 g).hom (pullbackSectionsMap_smul 𝓖 g)) := by
  let : Module Γ(Y.left, ⊤) Γ(X.left, ⊤) := Module.compHom _ g.left.appTop.hom
  have hφ : g.left.appTop.hom = (g.left.appLE ⊤ ⊤ (top_le_preimage_top g.left)).hom :=
    gammaMap_eq_appLE_top_top g.left
  let e := affineAssociatedBaseChangeIsoOfEq 𝓖 g g.left.appTop.hom hφ
  have heq : ⇑(Stacks.SemilinearExtension.extend g.left.appTop.hom (fun _ _ => rfl)
      (pullbackSectionsMap 𝓖 g).hom (pullbackSectionsMap_smul 𝓖 g)) = ⇑e.hom.hom := by
    refine coe_eq_of_tmul_eq _ e.hom.hom.toAddMonoidHom
      fun (s : Γ(X.left, ⊤)) m => ?_
    have h2 := ModuleCat.ExtendScalars.smul_tmul g.left.appTop.hom s 1 m
    rw [mul_one] at h2
    refine (Stacks.SemilinearExtension.extend_tmul _ _ _ _ s m).trans ?_
    refine Eq.trans ?_ (congrArg e.hom.hom h2)
    refine Eq.trans ?_ (e.hom.hom.map_smul s _).symm
    exact congrArg (fun y => s • y)
      (affineAssociatedBaseChangeIsoOfEq_one_tmul 𝓖 g g.left.appTop.hom hφ m).symm
  rw [heq]
  exact ConcreteCategory.bijective_of_isIso e.hom

end Stacks.Sites

namespace AlgebraicGeometry.SmallEtale

/-- The module structure of the presheaf of Stacks 03DS on the small étale site, at an object,
is the module structure of the global sections of the pullback. -/
theorem sectionsPresheafOfModules_smul_eq (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : S.Modules) [F.IsQuasicoherent] (T : SmallEtale B S hS)
    (r : (structureSheaf B S hS).obj.obj (op T))
    (m : (sectionsPresheafOfModules B S hS F).obj (op T)) :
    r • m = (show (sectionsPresheafOfModules B S hS F).obj (op T) from
      ((show Γ(((toOver B S hS).obj T).left, ⊤) from r) •
        (show Γ((Scheme.Modules.pullback ((toOver B S hS).obj T).hom).obj F, ⊤) from m))) :=
  rfl

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The category algebra of `AlgebraicGeometry.Stack.smallEtaleStructureComparison_app_final_comp`,
with every object and arrow abstract. -/
private theorem final_square_algebra {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : C}
    (a : O₁ ⟶ O₂) {b : O₂ ⟶ O₃} {c : O₃ ⟶ O₄} {d : O₄ ⟶ O₅} {r : O₃ ⟶ O₆} {c' : O₆ ⟶ O₅}
    {k₁ : O₂ ⟶ O₇} {k₂ : O₇ ⟶ O₈} {k₃ : O₈ ⟶ O₆}
    (hnat : r ≫ c' = c ≫ d) (hfin : b ≫ r = k₁ ≫ k₂ ≫ k₃) :
    a ≫ b ≫ c ≫ d = a ≫ k₁ ≫ k₂ ≫ k₃ ≫ c' := by
  rw [← hnat, ← Category.assoc b, hfin]
  simp only [Category.assoc]

/-- **The map of structure sheaves of Stacks 06WC between the final objects is restriction along
the arrow.** For `φ : z ⟶ x`, the map `a_{small}^♯` at the final object of the small étale site
below `x`, followed by restriction to the final object below `z`, is restriction of functions
of `𝒳` along `φ`, conjugated by the identifications of the sections at the final objects. -/
theorem smallEtaleStructureComparison_app_final_comp {x z : 𝒳} (φ : z ⟶ x) :
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app
          (op (smallEtaleFinal B E h S hS p x)) ≫
        (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj.map
          (finalToBaseChangeFinal B E h S hS p φ).op =
      (localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app
          (op (smallEtaleFinal B E h S hS p x)) ≫
        (restrictToSmallEtaleFinalIso B E h S hS p hp x
          (ringStructureSheafCore B S hS p hp τ hτ).obj).hom ≫
        (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ.op ≫
        (restrictToSmallEtaleFinalIso B E h S hS p hp z
          (ringStructureSheafCore B S hS p hp τ hτ).obj).inv ≫
        (localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app
          (op (smallEtaleFinal B E h S hS p z)) := by
  have hfinal := restrictionPushforwardComparison_app_final B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp τ hτ).obj
  have hnat := (localStructurePresheafIso B E h S hS p hp z τ hτ).inv.naturality
    (finalToBaseChangeFinal B E h S hS p φ).op
  simp only [smallEtaleStructureComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  exact final_square_algebra _ hnat hfinal

/-- The ring map between the final objects along which the unit at the final object is
semilinear: the map `a_{small}^♯` of Stacks 06WC at the final object below `x`, followed by
restriction to the final object below `z`. -/
noncomputable abbrev finalStructureMap {x z : 𝒳} (φ : z ⟶ x) :
    (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.obj
        (op (smallEtaleFinal B E h S hS p x)) ⟶
      (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj.obj
        (op (smallEtaleFinal B E h S hS p z)) :=
  (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app
      (op (smallEtaleFinal B E h S hS p x)) ≫
    (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj.map
      (finalToBaseChangeFinal B E h S hS p φ).op

/-- **The pullback of a section over the final object is semilinear.** The map
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit` is semilinear along
`AlgebraicGeometry.Stack.finalStructureMap`: it is the unit of an adjunction of presheaves of
modules at the final object, followed by a restriction map. -/
theorem smallEtaleFinalPullbackUnit_smul {x z : 𝒳} (φ : z ⟶ x)
    (M : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj)
    (r : (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.obj
        (op (smallEtaleFinal B E h S hS p x)))
    (m : M.obj (op (smallEtaleFinal B E h S hS p x))) :
    smallEtaleFinalPullbackUnit B E h S hS p hp τ hτ φ M (r • m) =
      (finalStructureMap B E h S hS p hp τ hτ φ).hom r •
        (show (PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj M |>.obj
            (op (smallEtaleFinal B E h S hS p z)) from
          smallEtaleFinalPullbackUnit B E h S hS p hp τ hτ φ M m) := by
  let unit := (PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app M
  have h1 : unit.app (op (smallEtaleFinal B E h S hS p x)) (r • m) =
      r • unit.app (op (smallEtaleFinal B E h S hS p x)) m :=
    (unit.app (op (smallEtaleFinal B E h S hS p x))).hom.map_smul r m
  show ((PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj M).map
        (finalToBaseChangeFinal B E h S hS p φ).op
        (unit.app (op (smallEtaleFinal B E h S hS p x)) (r • m)) = _
  rw [h1]
  exact PresheafOfModules.map_smul _ _ _ _

/-- The identification of the functions at the final object of the small étale site below `x`
with the functions at `x`: the identification of structure sheaves of Stacks 06W9 there, followed
by the counit of the localization equivalence of Stacks 06W0 at the final object. -/
noncomputable abbrev finalRingIso (x : 𝒳) :
    (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.obj
        (op (smallEtaleFinal B E h S hS p x)) ≅
      (ringStructureSheafCore B S hS p hp τ hτ).obj.obj (op x) :=
  (localStructurePresheafIso B E h S hS p hp x τ hτ).app (op (smallEtaleFinal B E h S hS p x)) ≪≫
    restrictToSmallEtaleFinalIso B E h S hS p hp x (ringStructureSheafCore B S hS p hp τ hτ).obj

/-- The identification of the sections of `F|_{U_ét}` at the final object with the sections of
`F` at `x` is semilinear along `AlgebraicGeometry.Stack.finalRingIso`. -/
theorem restrictModuleToSmallEtaleFinalIso_hom_smul (x : 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (r : (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.obj
        (op (smallEtaleFinal B E h S hS p x)))
    (m : (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).obj
        (op (smallEtaleFinal B E h S hS p x))) :
    (restrictModuleToSmallEtaleFinalIso B E h S hS p hp x τ hτ F).hom (r • m) =
      (show F.obj (op x) from
        (finalRingIso B E h S hS p hp τ hτ x).hom.hom r •
          (show F.obj (op x) from
            (restrictModuleToSmallEtaleFinalIso B E h S hS p hp x τ hτ F).hom m)) :=
  PresheafOfModules.map_smul F _ _ _

/-- **The ring square at the final objects.** Restriction of functions along `φ`, conjugated by
`AlgebraicGeometry.Stack.finalRingIso` at both ends, is
`AlgebraicGeometry.Stack.finalStructureMap`. -/
theorem finalStructureMap_comp_finalRingIso_hom {x z : 𝒳} (φ : z ⟶ x) :
    finalStructureMap B E h S hS p hp τ hτ φ ≫ (finalRingIso B E h S hS p hp τ hτ z).hom =
      (finalRingIso B E h S hS p hp τ hτ x).hom ≫
        (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ.op := by
  rw [finalStructureMap, smallEtaleStructureComparison_app_final_comp]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id, Category.comp_id]

section Final

variable {x z : 𝒳} (ψ : z ⟶ x)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
      (contains_base B E h S hS p x))
    (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F).presheaf)
  (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
      (contains_base B E h S hS p z))
    (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).presheaf)
  (𝓖 : (p.obj x).left.1.Modules) [𝓖.IsQuasicoherent]
  (e : (SmallEtale.associatedModule E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj 𝓖 ⟶
    restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F x hMx)

/-- The category algebra of
`AlgebraicGeometry.Stack.pullbackSectionsMap_comp_liftedSmallEtaleSheafInv_final`, with every
object and arrow abstract. -/
private theorem final_compat_algebra {C : Type*} [Category C]
    {A B₁ B₂ B₃ Q Q' N Fz' Fx' Fx Fz'' : C}
    {unit : A ⟶ B₁} {eta : B₁ ⟶ B₂} {bc : B₂ ⟶ B₃} {L : B₃ ⟶ Fz'} {nst : Q ⟶ N}
    {u : A ⟶ Fx'} {finx : Fx' ⟶ Fx} {Fψ : Fx ⟶ Fz''} {finzinv : Fz'' ⟶ Fz'}
    {sS : A ⟶ Q} {sS' : B₃ ⟶ Q'} {qcbc : N ⟶ Q'}
    (hc : unit ≫ eta ≫ bc ≫ sS' = sS ≫ nst ≫ qcbc)
    (hsf : unit ≫ eta ≫ bc ≫ L = u ≫ finx ≫ Fψ ≫ finzinv)
    (eS : A ≅ Q) (eS' : B₃ ≅ Q') (eqc : N ≅ Q') (efin : Fz' ≅ Fz'')
    (hS : eS.hom = sS := by rfl) (hS' : eS'.hom = sS' := by rfl) (hqc : eqc.hom = qcbc := by rfl)
    (hfin : efin.inv = finzinv := by rfl) :
    nst ≫ qcbc ≫ eS'.inv ≫ L ≫ efin.hom = eS.inv ≫ u ≫ finx ≫ Fψ := by
  subst hS hS' hqc hfin
  have h1 : nst ≫ eqc.hom = eS.inv ≫ unit ≫ eta ≫ bc ≫ eS'.hom := by
    rw [hc, Iso.inv_hom_id_assoc]
  calc nst ≫ eqc.hom ≫ eS'.inv ≫ L ≫ efin.hom
      = (nst ≫ eqc.hom) ≫ eS'.inv ≫ L ≫ efin.hom := by simp only [Category.assoc]
    _ = (eS.inv ≫ unit ≫ eta ≫ bc ≫ eS'.hom) ≫ eS'.inv ≫ L ≫ efin.hom := by rw [h1]
    _ = eS.inv ≫ (unit ≫ eta ≫ bc ≫ L) ≫ efin.hom := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = eS.inv ≫ u ≫ finx ≫ Fψ := by
        rw [hsf]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The arrow of the schemes over `U` below `ψ`, from the base change along it of the final
object of the small étale site of `W` to the final object of that of `U`. -/
noncomputable abbrev finalArrow :
    (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z)) ⟶
      (SmallEtale.toOver E (p.obj x).left.1 (contains_base B E h S hS p x)).obj
        (smallEtaleFinal B E h S hS p x) :=
  Over.homMk (B.inclusion.map (p.map ψ).left)
    (by simp [smallEtaleFinal, SmallEtale.final, Over.post])

/-- **The comparison map of Stacks 06WC at the final objects, read through the presheaf of
Stacks 03DS.** Pulling a section of `𝓖` back along the morphism below `ψ`, read as a section of
the inverse identification `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` over the final
object below `z`, is restricting along `ψ` the section of `F` it corresponds to below `x`. -/
theorem pullbackSectionsMap_comp_liftedSmallEtaleSheafInv_final :
    (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓖).map (finalArrow B E h S hS p ψ).op ≫
      (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
          (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) ≫
      (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1
          (contains_base B E h S hS p z)
          ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).inv.app
        (op (smallEtaleFinal B E h S hS p z)) ≫
      ((PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
          (liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e))).app
        (op (smallEtaleFinal B E h S hS p z)) ≫
      (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).hom =
    (SmallEtale.associatedModulePresheafIso E (p.obj x).left.1
        (contains_base B E h S hS p x) 𝓖).inv.app (op (smallEtaleFinal B E h S hS p x)) ≫
      ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map e)).app
        (op (smallEtaleFinal B E h S hS p x)) ≫
      (restrictModuleToSmallEtaleFinalIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).hom ≫
      F.presheaf.map ψ.op := by
  have hc := associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp ψ 𝓖 inferInstance
    (finalArrow B E h S hS p ψ) rfl
  let u : ((SmallEtale.associatedModule E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj 𝓖).val ⟶
      restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F := (SheafOfModules.forget _).map e
  have hsf := smallEtaleFinalPullbackUnit_comp_sheafifiedFactor B E h S hS p hp ψ F hMz
    ((SmallEtale.associatedModule E (p.obj x).left.1 (contains_base B E h S hS p x)).obj 𝓖).val
    u
  have hL : (PresheafOfModules.sheafification
          (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj)).map
          ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
              (etaleTopology_le_topology B))).map u) ≫
        sheafifiedRestrictComparison B E h S hS p hp F ψ hMz =
      (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ 𝓖).hom ≫
        liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e := by
    rw [liftedSmallEtaleSheafInv_eq, Iso.hom_inv_id_assoc]
    rfl
  rw [hL] at hsf
  simp only [Functor.map_comp, NatTrans.comp_app] at hsf
  exact final_compat_algebra hc hsf
    ((SmallEtale.associatedModulePresheafIso E (p.obj x).left.1
      (contains_base B E h S hS p x) 𝓖).app (op (smallEtaleFinal B E h S hS p x)))
    ((SmallEtale.associatedModulePresheafIso E (p.obj z).left.1
      (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).app
        (op (smallEtaleFinal B E h S hS p z)))
    ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
      (Over.mk (B.inclusion.map (p.map ψ).left))).app
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))))
    (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F)

/-- The map of global functions below the arrow of `AlgebraicGeometry.Stack.finalArrow` is the
map `AlgebraicGeometry.Stack.finalStructureMap` of structure sheaves at the final objects. -/
theorem finalStructureMap_hom_apply (r : (SmallEtale.structureSheaf E (p.obj x).left.1
    (contains_base B E h S hS p x)).obj.obj (op (smallEtaleFinal B E h S hS p x))) :
    (finalStructureMap B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) ψ).hom r =
      (finalArrow B E h S hS p ψ).left.appTop r := by
  have hw := Over.w (finalToBaseChangeFinal B E h S hS p ψ).hom
  have hcond := Limits.pullback.condition (f := (smallEtaleFinal B E h S hS p x).obj.hom)
    (g := smallEtaleBaseMorphism B E h S hS p ψ)
  have key : (finalToBaseChangeFinal B E h S hS p ψ).hom.left ≫
      Limits.pullback.fst (smallEtaleFinal B E h S hS p x).obj.hom
        (smallEtaleBaseMorphism B E h S hS p ψ) = smallEtaleBaseMorphism B E h S hS p ψ := by
    have hw' : (finalToBaseChangeFinal B E h S hS p ψ).hom.left ≫
        Limits.pullback.snd (smallEtaleFinal B E h S hS p x).obj.hom
          (smallEtaleBaseMorphism B E h S hS p ψ) = 𝟙 _ := hw
    exact (congrArg (fun k => (finalToBaseChangeFinal B E h S hS p ψ).hom.left ≫ k)
        (Category.comp_id _).symm).trans
      ((congrArg (fun k => (finalToBaseChangeFinal B E h S hS p ψ).hom.left ≫ k) hcond).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ smallEtaleBaseMorphism B E h S hS p ψ) hw').trans
            (Category.id_comp _))))
  unfold finalStructureMap
  rw [smallEtaleStructureComparison_eq_smallEtaleStructureMapRing]
  have hO : (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj.map
      (finalToBaseChangeFinal B E h S hS p ψ).op =
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map
        (E.inclusion.map (finalToBaseChangeFinal B E h S hS p ψ).hom.left).op) := rfl
  rw [hO, SmallEtale.smallEtaleStructureMapRing_hom_app]
  show (Scheme.Γ.map (E.inclusion.map (finalToBaseChangeFinal B E h S hS p ψ).hom.left).op).hom
      ((Scheme.Γ.map (E.inclusion.map (Limits.pullback.fst
        (smallEtaleFinal B E h S hS p x).obj.hom (smallEtaleBaseMorphism B E h S hS p ψ))).op).hom
          r) = _
  have hk := congrArg (fun k => (Scheme.Γ.map k.op).hom r)
    ((E.inclusion.map_comp _ _).symm.trans (congrArg E.inclusion.map key))
  simp only [op_comp] at hk
  exact hk

/-- **The comparison map of Stacks 06WC between affine objects, on sections over the final
object.** For `φ : z ⟶ x` lying over a morphism of affine schemes and `F|_{U_ét} ≅ 𝓖^a`, the
inverse identification `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` is bijective on the
sections over the final object exactly when `F` is cartesian along `φ`. -/
theorem bijective_liftedSmallEtaleSheafInv_app_final_iff
    [IsAffine (p.obj x).left.1] [IsAffine (p.obj z).left.1] [IsIso e] :
    Function.Bijective ((liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e).val.app
        (op (smallEtaleFinal B E h S hS p z))) ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F ψ.op) := by
  let Ufin := smallEtaleFinal B E h S hS p x
  let Wfin := smallEtaleFinal B E h S hS p z
  let Y := (SmallEtale.toOver E (p.obj x).left.1 (contains_base B E h S hS p x)).obj Ufin
  let A := (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj Wfin
  let X' := (Over.map (B.inclusion.map (p.map ψ).left)).obj A
  have : IsAffine Y.left := inferInstanceAs (IsAffine (p.obj x).left.1)
  have : IsAffine X'.left := inferInstanceAs (IsAffine (p.obj z).left.1)
  let g := finalArrow B E h S hS p ψ
  let : Module Γ(Y.left, ⊤) Γ(X'.left, ⊤) := Module.compHom _ g.left.appTop.hom
  have hσb := Stacks.Sites.bijective_extend_pullbackSectionsMap 𝓖 g
  let O := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
  let F' : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat) := F
  let instx : Module (O.obj (op x)) (F'.obj (op x)) := inferInstance
  let instz : Module (O.obj (op z)) (F'.obj (op z)) := inferInstance
  let : Module (O.obj (op x)) (O.obj (op z)) := Module.compHom _ (O.map ψ.op).hom
  have hc := pullbackSectionsMap_comp_liftedSmallEtaleSheafInv_final B E h S hS p hp ψ F hMx hMz 𝓖 e
  obtain ⟨T, hT⟩ : ∃ T : (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓖).obj (op Y) ⟶
      F.presheaf.obj (op x), T =
        (SmallEtale.associatedModulePresheafIso E (p.obj x).left.1
          (contains_base B E h S hS p x) 𝓖).inv.app (op (smallEtaleFinal B E h S hS p x)) ≫
        ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map e)).app
          (op (smallEtaleFinal B E h S hS p x)) ≫
        (restrictModuleToSmallEtaleFinalIso B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F).hom := ⟨_, rfl⟩
  obtain ⟨ΛI, hΛI⟩ : ∃ ΛI : (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓖).obj (op X') ⟶
      F.presheaf.obj (op z), ΛI =
        (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
          (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) ≫
      (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1
          (contains_base B E h S hS p z)
          ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).inv.app
        (op (smallEtaleFinal B E h S hS p z)) ≫
      ((PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
          (liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e))).app
        (op (smallEtaleFinal B E h S hS p z)) ≫
      (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).hom := ⟨_, rfl⟩
  rw [← hΛI] at hc
  have hT2 : T ≫ F.presheaf.map ψ.op =
      (SmallEtale.associatedModulePresheafIso E (p.obj x).left.1
          (contains_base B E h S hS p x) 𝓖).inv.app (op (smallEtaleFinal B E h S hS p x)) ≫
        ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map e)).app
          (op (smallEtaleFinal B E h S hS p x)) ≫
        (restrictModuleToSmallEtaleFinalIso B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F).hom ≫ F.presheaf.map ψ.op := by
    rw [hT]
    exact Category.assoc _ _ _
  rw [← hT2] at hc
  have hTb : Function.Bijective T := by
    rw [hT]
    exact ConcreteCategory.bijective_of_isIso
      (((SmallEtale.associatedModulePresheafIso E (p.obj x).left.1
          (contains_base B E h S hS p x) 𝓖).app (op (smallEtaleFinal B E h S hS p x))).symm ≪≫
        ((PresheafOfModules.toPresheaf _).mapIso ((SheafOfModules.forget _).mapIso
          (asIso e))).app (op (smallEtaleFinal B E h S hS p x)) ≪≫
        restrictModuleToSmallEtaleFinalIso B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F).hom
  let τ : Γ((Scheme.Modules.pullback Y.hom).obj 𝓖, ⊤) ≃+ F'.obj (op x) :=
    AddEquiv.ofBijective T.hom hTb
  let eR : Γ(Y.left, ⊤) ≃+* O.obj (op x) :=
    (finalRingIso B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B)
      x).ringCatIsoToRingEquiv
  let eS : Γ(X'.left, ⊤) ≃+* O.obj (op z) :=
    (finalRingIso B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B)
      z).ringCatIsoToRingEquiv
  let Λ : Γ((Scheme.Modules.pullback X'.hom).obj 𝓖, ⊤) →+ F'.obj (op z) := ΛI.hom
  let v : F'.obj (op x) →+ F'.obj (op z) := (F.presheaf.map ψ.op).hom
  have hτ : ∀ (r : Γ(Y.left, ⊤)) (m : Γ((Scheme.Modules.pullback Y.hom).obj 𝓖, ⊤)),
      τ (r • m) = eR r • τ m := fun r m => by
    have h1 := ((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj x).left.1
      (contains_base B E h S hS p x) 𝓖).inv.app (op (smallEtaleFinal B E h S hS p x))).hom.map_smul
        r m
    have h2 := (e.val.app (op (smallEtaleFinal B E h S hS p x))).hom.map_smul r
      (((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj x).left.1
      (contains_base B E h S hS p x) 𝓖).inv.app (op (smallEtaleFinal B E h S hS p x))).hom m)
    have h3 := restrictModuleToSmallEtaleFinalIso_hom_smul B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x F r ((e.val.app (op (smallEtaleFinal B E h S hS p x))).hom
        (((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj x).left.1
          (contains_base B E h S hS p x) 𝓖).inv.app (op (smallEtaleFinal B E h S hS p x))).hom m))
    have hτT : ∀ m', τ m' = T m' := fun _ => rfl
    rw [hτT, hτT, hT]
    exact (congrArg (fun y => (restrictModuleToSmallEtaleFinalIso B E h S hS p hp x
        (etaleTopology B) (etaleTopology_le_topology B) F).hom
          ((e.val.app (op (smallEtaleFinal B E h S hS p x))).hom y)) h1).trans
      ((congrArg (restrictModuleToSmallEtaleFinalIso B E h S hS p hp x
        (etaleTopology B) (etaleTopology_le_topology B) F).hom h2).trans h3)
  have hΛ : ∀ (s : Γ(X'.left, ⊤)) (n : Γ((Scheme.Modules.pullback X'.hom).obj 𝓖, ⊤)),
      Λ (s • n) = eS s • Λ n := fun s n => by
    have h0 : (show Γ((Scheme.Modules.pullback A.hom).obj
          ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖), ⊤) from
        (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
          (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) (s • n)) =
        s • (show Γ((Scheme.Modules.pullback A.hom).obj
          ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖), ⊤) from
          (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
          (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) n) :=
      Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackComp _ _).inv.app 𝓖) s n
    let n1 := (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
          (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) n
    have h1 := ((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).inv.app
        (op (smallEtaleFinal B E h S hS p z))).hom.map_smul s n1
    let n2 := ((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).inv.app
        (op (smallEtaleFinal B E h S hS p z))).hom n1
    have h2 := ((liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e).val.app
        (op (smallEtaleFinal B E h S hS p z))).hom.map_smul s n2
    have h3 := restrictModuleToSmallEtaleFinalIso_hom_smul B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) z F s
        (((liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e).val.app
          (op (smallEtaleFinal B E h S hS p z))).hom n2)
    have hΛΛ : ∀ n', Λ n' = ΛI n' := fun _ => rfl
    rw [hΛΛ, hΛΛ, hΛI]
    have hb := SmallEtale.sectionsPresheafOfModules_smul_eq E (p.obj z).left.1
      (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)
      (smallEtaleFinal B E h S hS p z) s n1
    exact (congrArg (fun y => (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z
        (etaleTopology B) (etaleTopology_le_topology B) F).hom
          (((liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e).val.app
            (op (smallEtaleFinal B E h S hS p z))).hom
            (((SmallEtale.associatedModuleIsoSectionsPresheaf E (p.obj z).left.1
              (contains_base B E h S hS p z)
              ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).inv.app
                (op (smallEtaleFinal B E h S hS p z))).hom y))) (h0.trans hb.symm)).trans
      ((congrArg (fun y => (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z
        (etaleTopology B) (etaleTopology_le_topology B) F).hom
          (((liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e).val.app
            (op (smallEtaleFinal B E h S hS p z))).hom y)) h1).trans
        ((congrArg (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z
          (etaleTopology B) (etaleTopology_le_topology B) F).hom h2).trans h3))
  have hsq : ∀ r, eS (g.left.appTop.hom r) = (O.map ψ.op).hom (eR r) := fun r => by
    have h1 := finalStructureMap_hom_apply B E h S hS p hp ψ r
    have h2 := ConcreteCategory.congr_hom (finalStructureMap_comp_finalRingIso_hom B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) ψ) r
    exact (congrArg eS h1.symm).trans h2
  have hcomm : ∀ m, Λ ((pullbackSectionsMap 𝓖 g).hom m) = v (τ m) := fun m =>
    ConcreteCategory.congr_hom hc m
  have hv : ∀ (r : O.obj (op x)) (m : F'.obj (op x)),
      v (r • m) = (O.map ψ.op).hom r • v m :=
    fun r m => F'.map_smul ψ.op r m
  have key := Stacks.SemilinearExtension.bijective_iff_bijective_extend g.left.appTop.hom
    (O.map ψ.op).hom (fun _ _ => rfl) (fun _ _ => rfl) eR eS hsq (pullbackSectionsMap 𝓖 g).hom
    (pullbackSectionsMap_smul 𝓖 g) v hv τ hτ Λ hΛ hcomm hσb
  have hrbc := Stacks.PresheafOfModules.restrictionBaseChange_eq_extend F' ψ.op
  have hΛb : Function.Bijective Λ ↔ Function.Bijective
      ((liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓖 hMx hMz e).val.app (op Wfin)) := by
    show Function.Bijective ⇑ΛI ↔ _
    subst hΛI
    have b1 := ConcreteCategory.bijective_of_isIso ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso
      𝓖 (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))))
    have b2 := ConcreteCategory.bijective_of_isIso ((SmallEtale.associatedModulePresheafIso E
      (p.obj z).left.1 (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).inv.app
        (op (smallEtaleFinal B E h S hS p z)))
    have b3 := ConcreteCategory.bijective_of_isIso (restrictModuleToSmallEtaleFinalIso B E h S hS
      p hp z (etaleTopology B) (etaleTopology_le_topology B) F).hom
    exact (Function.Bijective.of_comp_iff' b3 _).trans
      (Function.Bijective.of_comp_iff _ (b2.comp b1))
  exact hΛb.symm.trans (key.trans (Iff.of_eq (congrArg Function.Bijective hrbc).symm))

/-- **Stacks 06WK between affine objects.** Let `ψ : z ⟶ x` be an arrow of `𝒳` lying over a
morphism of affine schemes, and let the restrictions of `F` to the small étale sites below `x`
and `z` be quasi-coherent sheaves. Then the comparison map `c_ψ` of Stacks 06WC is an
isomorphism exactly when `F` is cartesian along `ψ`, that is when the base-change map
`𝒪(z) ⊗_{𝒪(x)} F(x) ⟶ F(z)` of its restriction map is bijective. -/
theorem isIso_sheafifiedRestrictComparison_iff_bijective_restrictionBaseChange
    [IsAffine (p.obj x).left.1] [IsAffine (p.obj z).left.1]
    (hqx : (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F x hMx).IsQuasicoherentOnSite)
    (hqz : (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F z hMz).IsQuasicoherentOnSite) :
    IsIso (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz) ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F ψ.op) := by
  obtain ⟨𝓐, ⟨e⟩⟩ := SmallEtale.quasicoherentIsEssImageAssociatedModule E (p.obj x).left.1
    (contains_base B E h S hS p x) _ hqx
  have : 𝓐.obj.IsQuasicoherent := 𝓐.property
  let e' : (SmallEtale.associatedModule E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj 𝓐.obj ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx := e.hom
  have : IsIso e' := inferInstanceAs (IsIso e.hom)
  rw [← bijective_liftedSmallEtaleSheafInv_app_final_iff B E h S hS p hp ψ F hMx hMz 𝓐.obj e']
  have hΛ : liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓐.obj hMx hMz e' =
      (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ 𝓐.obj).inv ≫
        (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ).map e' ≫
        sheafifiedRestrictComparison B E h S hS p hp F ψ hMz := rfl
  have hiff : IsIso (sheafifiedRestrictComparison B E h S hS p hp F ψ hMz) ↔
      IsIso (liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓐.obj hMx hMz e') := by
    rw [hΛ, isIso_comp_left_iff]
    have hm : IsIso ((sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) ψ).map e') := Functor.map_isIso _ _
    exact ⟨fun hc => IsIso.comp_isIso' hm hc,
      fun hI => @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hm hI⟩
  rw [hiff]
  have hqA : ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
        𝓐.obj)).IsQuasicoherentOnSite :=
    SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent E _ _ _
      (Stacks.Modules.isQuasicoherent_pullback _ _ inferInstance)
  exact ⟨fun _ => ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation _
      (op (smallEtaleFinal B E h S hS p z))).mapIso
        (asIso (liftedSmallEtaleSheafInv B E h S hS p hp F ψ 𝓐.obj hMx hMz e'))).hom,
    SmallEtale.isIso_of_bijective_app_final E (p.obj z).left.1
      (contains_base B E h S hS p z) hqA hqz _⟩

end Final

end AlgebraicGeometry.Stack

end
