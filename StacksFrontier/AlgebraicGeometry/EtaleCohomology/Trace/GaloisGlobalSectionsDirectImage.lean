module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat

/-!
# `Γ^Gal(Ȳ, i_* H) ≅ Γ^Gal(Y, H)`

Let `k` be a field, `K/k` a separable algebraic extension and `i : Y ⟶ Ȳ` a morphism of
quasi-compact and quasi-separated `k`-schemes. For a sheaf `H` of `R`-modules on `Y_étale` the
base change map `β : (i_* H)|_{Ȳ_K} ⟶ (i_K)_*(H|_{Y_K})` of the square `i_K ≫ p̄ = p ≫ i`
(`Stacks.EtaleCohomology.etaleModuleBaseChange`) followed by `Γ(Ȳ_K, (i_K)_* -) = Γ(Y_K, -)`
(`Stacks.EtaleCohomology.etaleModuleDirectImageCompGlobalSections`) is a map
`Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ⟶ Γ(Y_K, H|_{Y_K})`
(`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsDirectImageMap`). This file proves that it is
bijective and that it intertwines the actions of `Aut_k(K)`
(`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction`), so that it is an isomorphism
of discrete Galois modules `Γ^Gal(Ȳ, i_* H) ≅ Γ^Gal(Y, H)`, natural in `H`
(`Stacks.EtaleCohomology.galoisGlobalSectionsMapDirectImageIso`). For a compactification
`j : X ⟶ X̄` over `k` this is `Stacks.EtaleCohomology.galoisGlobalSectionsDirectImageIso`.

Both statements are proved on sections coming from the finite stages `Ȳ_E` of `Ȳ_K`
(`Stacks.EtaleCohomology.exists_fieldStageSection_eq`, Stacks 09YQ in degree zero): the map carries
the restriction of the pulled back section `u(a)`, `a ∈ (i_* H)(W) = H(W ×_Ȳ Y)`, along a morphism
`r : Ȳ_K ⟶ W` over `Ȳ` to the restriction of `u(a)` along `(r ∘ i_K, p) : Y_K ⟶ W ×_Ȳ Y`
(`Stacks.EtaleCohomology.ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap`). Since
`Ȳ_E ×_Ȳ Y = Y_E`, both sides are the colimit of the `H(Y_E)`.

## Main definitions

* `Stacks.EtaleCohomology.fieldBaseChangeMorphism` — the base change `i_K : Y_K ⟶ Ȳ_K`.
* `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsDirectImageMap` — the map
  `Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ⟶ Γ(Y_K, H|_{Y_K})`.
* `Stacks.EtaleCohomology.galoisGlobalSectionsMapDirectImageIso` —
  `i_* ⋙ Γ^Gal(Ȳ, -) ≅ Γ^Gal(Y, -)`.
* `Stacks.EtaleCohomology.galoisGlobalSectionsDirectImageIso` — the same for a compactification.
* `Stacks.EtaleCohomology.fieldStageDirectImageHom`,
  `Stacks.EtaleCohomology.fieldStageDirectImageInv` — `Ȳ_E ×_Ȳ Y ⟶ Y_E` and back.

## Main results

* `Stacks.EtaleCohomology.bijective_fieldBaseChangeGlobalSectionsDirectImageMap`.
* `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsDirectImageMap_galoisAction`.
* `Stacks.EtaleCohomology.galoisGlobalSectionsMapDirectImageIso_hom_app`,
  `Stacks.EtaleCohomology.galoisGlobalSectionsDirectImageIso_hom_app` — after forgetting the
  action, the component is `fieldBaseChangeGlobalSectionsDirectImageMap`.
* `Stacks.EtaleCohomology.ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap` — the map on sections
  coming from an étale `Ȳ`-scheme.
* `Stacks.EtaleCohomology.fieldStageSection_map`,
  `Stacks.EtaleCohomology.exists_map_eq_of_fieldStageSection_eq` — sections pulled back from finite
  stages: compatibility with growing the stage, and the injectivity half of Stacks 09YQ in degree
  zero.

## Implementation notes

`AlgebraicGeometry.representationSheafPullbackIso` is not used. The base change map is only shown
to be bijective on global sections, which is all that is needed here.

The computation of the base change map on pulled back sections
(`Stacks.EtaleCohomology.ΓRes_globalSections_map_comp_of_unit`) is done for an arbitrary morphism
satisfying the unit formula of the base change map, which is then applied to the base change map
itself: comparing elementwise statements about the base change map, whose source and target are
spelled differently (`(p̄_* M)(W)` against `M(W ×_Ȳ Ȳ_K)`), makes the kernel unfold it.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-! ### The base change of a morphism over `k` -/

section Morphism

variable {k : Type u} [Field k] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb) (K : Type u) [Field K]
  [Algebra k K]

/-- **The base change `i_K : Y_K ⟶ Ȳ_K`** of a morphism `i : Y ⟶ Ȳ` of schemes over `k`. -/
abbrev fieldBaseChangeMorphism (i : Y ⟶ Yb) (K : Type u) [Field K] [Algebra k K] :
    fieldBaseChange Y K ⟶ fieldBaseChange Yb K :=
  pullback.map Y.hom (specAlgebraMap k K) Yb.hom (specAlgebraMap k K) i.left (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- `i_K` lies over `i`. -/
@[reassoc]
theorem fieldBaseChangeMorphism_comp_fst :
    fieldBaseChangeMorphism i K ≫ fieldBaseChangeProj Yb K = fieldBaseChangeProj Y K ≫ i.left :=
  pullback.lift_fst _ _ _

/-- `i_K` lies over `Spec K`. -/
@[reassoc]
theorem fieldBaseChangeMorphism_comp_snd :
    fieldBaseChangeMorphism i K ≫ pullback.snd Yb.hom (specAlgebraMap k K) =
      pullback.snd Y.hom (specAlgebraMap k K) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `i_K` commutes with `id × Spec σ`. -/
theorem galoisBaseChange_comp_fieldBaseChangeMorphism (σ : K ≃ₐ[k] K) :
    galoisBaseChange Y K σ ≫ fieldBaseChangeMorphism i K =
      fieldBaseChangeMorphism i K ≫ galoisBaseChange Yb K σ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, fieldBaseChangeMorphism_comp_fst,
      galoisBaseChange_comp_fst, galoisBaseChange_comp_fst_assoc, fieldBaseChangeMorphism_comp_fst]
  · rw [Category.assoc, Category.assoc, fieldBaseChangeMorphism_comp_snd,
      galoisBaseChange_comp_snd, galoisBaseChange_comp_snd, fieldBaseChangeMorphism_comp_snd_assoc]

end Morphism

/-! ### The map on global sections -/

section Map

variable (R : Type) [Ring R] {k : Type u} [Field k] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb)
  (K : Type u) [Field K] [Algebra k K]

/-- **`Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ⟶ Γ(Y_K, H|_{Y_K})`**: global sections of the base change map
`(i_* H)|_{Ȳ_K} ⟶ (i_K)_*(H|_{Y_K})`, followed by `Γ(Ȳ_K, (i_K)_* -) = Γ(Y_K, -)`. -/
def fieldBaseChangeGlobalSectionsDirectImageMap (H : EtaleModules.{u, 0} R Y.left) :
    (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)) ⟶
      (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Y K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H) :=
  (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).map
      ((etaleModuleBaseChange R i.left (fieldBaseChangeMorphism i K) (fieldBaseChangeProj Yb K)
        (fieldBaseChangeProj Y K) (fieldBaseChangeMorphism_comp_fst i K)).app H) ≫
    (etaleModuleDirectImageCompGlobalSections.{u, 0} R (fieldBaseChangeMorphism i K)).hom.app
      ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H)

/-- `fieldBaseChangeGlobalSectionsDirectImageMap` is natural in `H`. -/
theorem fieldBaseChangeGlobalSectionsDirectImageMap_naturality {H H' : EtaleModules.{u, 0} R Y.left}
    (v : H ⟶ H') :
    (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).map
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).map
          ((etaleModuleDirectImage.{u, 0} R i.left).map v)) ≫
        fieldBaseChangeGlobalSectionsDirectImageMap R i K H' =
      fieldBaseChangeGlobalSectionsDirectImageMap R i K H ≫
        (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).map v) := by
  have h₁ := (etaleModuleBaseChange R i.left (fieldBaseChangeMorphism i K)
    (fieldBaseChangeProj Yb K) (fieldBaseChangeProj Y K)
    (fieldBaseChangeMorphism_comp_fst i K)).naturality v
  have h₂ := (etaleModuleDirectImageCompGlobalSections.{u, 0} R
    (fieldBaseChangeMorphism i K)).hom.naturality
      ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).map v)
  simp only [Functor.comp_map] at h₁ h₂
  rw [fieldBaseChangeGlobalSectionsDirectImageMap, fieldBaseChangeGlobalSectionsDirectImageMap,
    ← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, h₂, Category.assoc]

end Map

/-! ### The map on sections coming from an étale `Ȳ`-scheme -/

section Core

variable (R : Type) [Ring R] {k : Type u} [Field k] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb)
  (K : Type u) [Field K] [Algebra k K]

/-- `Γ(Z, g_* F) ≅ Γ(X, F)` followed by restriction to the base change of the final object is
restriction to the final object. -/
theorem etaleModuleDirectImageCompGlobalSections_hom_app_comp_ΓRes {X Z : Scheme.{u}}
    (g : X ⟶ Z) (F : EtaleModules.{u, 0} R X) :
    (etaleModuleDirectImageCompGlobalSections.{u, 0} R g).hom.app F ≫
        F.ΓRes (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 Z)))) =
      ((etaleModuleDirectImage.{u, 0} R g).obj F).ΓRes (op (Scheme.Etale.mk (𝟙 Z))) := by
  have : IsIso (Scheme.Etale.mk (𝟙 Z)).hom := inferInstanceAs (IsIso (𝟙 Z))
  have : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  have : HasTerminal Z.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Z))).hasTerminal
  have : HasTerminal X.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X))).hasTerminal
  let ΓZ := Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (ModuleCat.{u + 1} R)
    (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Z)))
  let ΓX := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)
    (isTerminalSmallEtaleBaseChangeObj g (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Z))))
  have cL : (etaleModuleDirectImageCompGlobalSections.{u, 0} R g).hom.app F ≫ ΓX.hom.app F =
      ΓZ.hom.app ((etaleModuleDirectImage.{u, 0} R g).obj F) := by
    show (ΓZ.hom.app ((etaleModuleDirectImage.{u, 0} R g).obj F) ≫ 𝟙 _ ≫ ΓX.inv.app F) ≫
      ΓX.hom.app F = _
    exact (Category.assoc _ _ _).trans ((congrArg _ ((Category.assoc _ _ _).trans
      ((Category.id_comp _).trans (Iso.inv_hom_id_app ΓX F)))).trans (Category.comp_id _))
  rwa [Sheaf.ΓNatIsoSheafSections_hom_app_general, Sheaf.ΓNatIsoSheafSections_hom_app_general] at cL

/-- `(r ∘ i_K, p) : Y_K ⟶ W ×_Ȳ Y` for a morphism `r : Ȳ_K ⟶ W` over `Ȳ`. -/
abbrev fieldBaseChangeDirectImageLift {W : Yb.left.Etale} (r : fieldBaseChange Yb K ⟶ W.left)
    (hr : r ≫ W.hom = fieldBaseChangeProj Yb K) :
    fieldBaseChange Y K ⟶ ((smallEtaleBaseChange i.left).obj W).left :=
  pullback.lift (fieldBaseChangeMorphism i K ≫ r) (fieldBaseChangeProj Y K)
    (by rw [Category.assoc, hr, fieldBaseChangeMorphism_comp_fst])

/-- `(r ∘ i_K, p)` lies over `Y`. -/
theorem fieldBaseChangeDirectImageLift_comp_hom {W : Yb.left.Etale}
    (r : fieldBaseChange Yb K ⟶ W.left) (hr : r ≫ W.hom = fieldBaseChangeProj Yb K) :
    fieldBaseChangeDirectImageLift i K r hr ≫ ((smallEtaleBaseChange i.left).obj W).hom =
      fieldBaseChangeProj Y K :=
  pullback.lift_snd _ _ _

/-- The computation behind `ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap`, for any morphism
`φ : (i_* H)|_{Ȳ_K} ⟶ (i_K)_*(H|_{Y_K})` satisfying the unit formula of the base change map
(`Stacks.EtaleCohomology.unit_comp_map_etaleModuleBaseChange`). Keeping `φ` a variable keeps the
kernel from unfolding the base change map. -/
theorem ΓRes_globalSections_map_comp_of_unit (H : EtaleModules.{u, 0} R Y.left)
    (φ : (etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
        ((etaleModuleDirectImage.{u, 0} R i.left).obj H) ⟶
      (etaleModuleDirectImage.{u, 0} R (fieldBaseChangeMorphism i K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H))
    (hφ : (etaleModuleInverseImageAdj.{u, 0} R (fieldBaseChangeProj Yb K)).unit.app
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H) ≫
        (etaleModuleDirectImage.{u, 0} R (fieldBaseChangeProj Yb K)).map φ =
      (etaleModuleDirectImage.{u, 0} R i.left).map
          ((etaleModuleInverseImageAdj.{u, 0} R (fieldBaseChangeProj Y K)).unit.app H) ≫
        (etaleModuleDirectImageComp.{u, 0} R (fieldBaseChangeProj Y K) i.left
          (fieldBaseChangeMorphism i K ≫ fieldBaseChangeProj Yb K)
          (fieldBaseChangeMorphism_comp_fst i K)).hom.app
          ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H) ≫
        (etaleModuleDirectImageComp.{u, 0} R (fieldBaseChangeMorphism i K)
          (fieldBaseChangeProj Yb K) (fieldBaseChangeMorphism i K ≫ fieldBaseChangeProj Yb K)
          rfl).inv.app ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H))
    {W : Yb.left.Etale} (a : H.obj.obj (op ((smallEtaleBaseChange i.left).obj W)))
    {r : fieldBaseChange Yb K ⟶ W.left} (hr : r ≫ W.hom = fieldBaseChangeProj Yb K)
    (z : (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)))
    (hz : ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Yb K)))) z =
      ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Yb K) W r hr).op
        (moduleUnitSection R (fieldBaseChangeProj Yb K)
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H) (V := W) a)) :
    ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (((etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).map φ ≫
          (etaleModuleDirectImageCompGlobalSections.{u, 0} R (fieldBaseChangeMorphism i K)).hom.app
            ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H)) z) =
      ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) ((smallEtaleBaseChange i.left).obj W)
          (fieldBaseChangeDirectImageLift i K r hr)
          (fieldBaseChangeDirectImageLift_comp_hom i K r hr)).op
        (moduleUnitSection R (fieldBaseChangeProj Y K) H a) := by
  let iK := fieldBaseChangeMorphism i K
  let N := (etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H
  let t0 : Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)) ⟶
      (smallEtaleBaseChange iK).obj (Scheme.Etale.mk (𝟙 (fieldBaseChange Yb K))) :=
    smallEtaleBaseChangeLift iK _ iK (Category.comp_id _)
  have e1 := ConcreteCategory.congr_hom (Sheaf.ΓRes_map N t0.op)
    (((etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).map φ ≫
      (etaleModuleDirectImageCompGlobalSections.{u, 0} R iK).hom.app N) z)
  have e2 := ConcreteCategory.congr_hom
    (etaleModuleDirectImageCompGlobalSections_hom_app_comp_ΓRes R iK N)
    ((etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).map φ z)
  have e3 := ConcreteCategory.congr_hom (Sheaf.ΓRes_naturality φ
    (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Yb K))))) z
  have e4 := ConcreteCategory.congr_hom (φ.hom.naturality
    (smallEtaleBaseChangeLift (fieldBaseChangeProj Yb K) W r hr).op)
    (moduleUnitSection R (fieldBaseChangeProj Yb K)
      ((etaleModuleDirectImage.{u, 0} R i.left).obj H) (V := W) a)
  have e5m := congrArg (fun ψ => ψ.hom.app (op W)) hφ
  simp only [ConcreteCategory.comp_apply, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at e1 e2 e3 e4 e5m
  rw [etaleModuleDirectImageComp_hom_app_hom_app, etaleModuleDirectImageComp_inv_app_hom_app]
    at e5m
  have e5 : φ.hom.app (op ((smallEtaleBaseChange (fieldBaseChangeProj Yb K)).obj W))
      (moduleUnitSection R (fieldBaseChangeProj Yb K)
        ((etaleModuleDirectImage.{u, 0} R i.left).obj H) (V := W) a) =
      N.obj.map (op ((smallEtaleBaseChangeComp' iK (fieldBaseChangeProj Yb K)
          (iK ≫ fieldBaseChangeProj Yb K) rfl).inv.app W))
        (N.obj.map (op ((smallEtaleBaseChangeComp' (fieldBaseChangeProj Y K) i.left
          (iK ≫ fieldBaseChangeProj Yb K) (fieldBaseChangeMorphism_comp_fst i K)).hom.app W))
          (moduleUnitSection R (fieldBaseChangeProj Y K) H a)) :=
    ConcreteCategory.congr_hom e5m a
  have hmap : ∀ {A B C D E : (fieldBaseChange Y K).Etaleᵒᵖ} (f₁ : A ⟶ B) (f₂ : B ⟶ C)
      (f₃ : C ⟶ D) (f₄ : D ⟶ E) (x : N.obj.obj A),
      N.obj.map f₄ (N.obj.map f₃ (N.obj.map f₂ (N.obj.map f₁ x))) =
        N.obj.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄) x := by
    intros
    simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  have hcl : ∀ {Z : Scheme.{u}} {A B C : Z.Etale} (q : A ⟶ B) (q' : B ⟶ C),
      (q ≫ q').left = q.left ≫ q'.left := fun _ _ => rfl
  have key : t0 ≫ (smallEtaleBaseChange iK).map (smallEtaleBaseChangeLift
        (fieldBaseChangeProj Yb K) W r hr) ≫
      (smallEtaleBaseChangeComp' iK (fieldBaseChangeProj Yb K) (iK ≫ fieldBaseChangeProj Yb K)
        rfl).inv.app W ≫
      (smallEtaleBaseChangeComp' (fieldBaseChangeProj Y K) i.left (iK ≫ fieldBaseChangeProj Yb K)
        (fieldBaseChangeMorphism_comp_fst i K)).hom.app W =
      smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) ((smallEtaleBaseChange i.left).obj W)
          (fieldBaseChangeDirectImageLift i K r hr)
          (fieldBaseChangeDirectImageLift_comp_hom i K r hr) := by
    apply smallEtaleBaseChange_hom_ext
    refine Eq.trans ?_ (pullback.lift_fst (fieldBaseChangeDirectImageLift i K r hr)
      (𝟙 (fieldBaseChange Y K)) _).symm
    apply pullback.hom_ext
    · have chain : ∀ {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₁ B₂ : Scheme.{u}} {T : A₀ ⟶ A₁} {B : A₁ ⟶ A₂}
          {V : A₂ ⟶ A₃} {Hh : A₃ ⟶ A₄} {F₁ : A₄ ⟶ A₅} {F₂ : A₅ ⟶ A₆} {G : A₃ ⟶ A₆}
          {P : A₂ ⟶ B₁} {Q : B₁ ⟶ A₆} {P' : A₁ ⟶ B₂} {L : B₂ ⟶ B₁} {ρ : B₂ ⟶ A₆}
          {ι : A₀ ⟶ B₂},
          Hh ≫ F₁ ≫ F₂ = G → V ≫ G = P ≫ Q → B ≫ P = P' ≫ L → L ≫ Q = ρ → T ≫ P' = ι →
          ((T ≫ B ≫ V ≫ Hh) ≫ F₁) ≫ F₂ = ι ≫ ρ := by
        intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅
        simp only [Category.assoc, h₁, h₂, reassoc_of% h₃, h₄, reassoc_of% h₅]
      exact Eq.trans (chain (smallEtaleBaseChangeComp'_fst_fst _ _ _ _ W)
        (smallEtaleBaseChangeComp'_inv_fst iK (fieldBaseChangeProj Yb K) _ rfl W)
        (smallEtaleBaseChange_map_left_fst iK
          (smallEtaleBaseChangeLift (fieldBaseChangeProj Yb K) W r hr))
        (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)) (pullback.lift_fst _ _ _).symm
    · have chain : ∀ {A₀ A₁ A₂ A₃ : Scheme.{u}} {M : A₀ ⟶ A₁} {F₁ : A₁ ⟶ A₂} {G : A₂ ⟶ A₃}
          {S : A₁ ⟶ A₀} {q : A₀ ⟶ A₃}, F₁ ≫ G = S ≫ q → M ≫ S = 𝟙 A₀ → (M ≫ F₁) ≫ G = q := by
        intro _ _ _ _ _ _ _ _ _ h₁ h₂
        rw [Category.assoc, h₁, reassoc_of% h₂]
      exact Eq.trans (chain pullback.condition (smallEtaleBaseChange_w _ _))
        (pullback.lift_snd _ _ _).symm
  simp only [ConcreteCategory.comp_apply]
  refine e1.symm.trans ?_
  rw [e2]
  refine (congrArg (fun x => N.obj.map t0.op x) (e3.trans (congrArg
    (fun x => φ.hom.app (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Yb K)))) x) hz))).trans ?_
  rw [e4, e5, directImage_obj_map]
  refine (hmap _ _ _ _ _).trans (congrArg (fun m => N.obj.map m
    (moduleUnitSection R (fieldBaseChangeProj Y K) H a)) ?_)
  rw [← key]
  simp only [op_comp, Quiver.Hom.unop_op, Category.assoc]
  rfl

/-- **The map `Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ⟶ Γ(Y_K, H|_{Y_K})` on a section coming from `W`.** If a
global section `z` is, over the final object, the restriction of the pulled back section `u(a)`,
`a ∈ (i_* H)(W) = H(W ×_Ȳ Y)`, along the morphism given by `r : Ȳ_K ⟶ W`, then its image is the
restriction of `u(a)` along the morphism given by `(r ∘ i_K, p) : Y_K ⟶ W ×_Ȳ Y`. -/
theorem ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap (H : EtaleModules.{u, 0} R Y.left)
    {W : Yb.left.Etale} (a : H.obj.obj (op ((smallEtaleBaseChange i.left).obj W)))
    {r : fieldBaseChange Yb K ⟶ W.left} (hr : r ≫ W.hom = fieldBaseChangeProj Yb K)
    (z : (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)))
    (hz : ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Yb K)))) z =
      ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Yb K) W r hr).op
        (moduleUnitSection R (fieldBaseChangeProj Yb K)
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H) (V := W) a)) :
    ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (fieldBaseChangeGlobalSectionsDirectImageMap R i K H z) =
      ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) ((smallEtaleBaseChange i.left).obj W)
          (fieldBaseChangeDirectImageLift i K r hr)
          (fieldBaseChangeDirectImageLift_comp_hom i K r hr)).op
        (moduleUnitSection R (fieldBaseChangeProj Y K) H a) :=
  ΓRes_globalSections_map_comp_of_unit R i K H _
    (unit_comp_map_etaleModuleBaseChange R i.left (fieldBaseChangeMorphism i K)
      (fieldBaseChangeProj Yb K) (fieldBaseChangeProj Y K) (fieldBaseChangeMorphism_comp_fst i K) H)
    a hr z hz

end Core

/-! ### Finite stages -/

section Stages

variable (R : Type) [Ring R] {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u)
  [Field K] [Algebra k K] [Algebra.IsSeparable k K]

attribute [local instance] fextOrderBot fextIsDirected

/-- The lift into a base change is compatible with a morphism `f` of étale objects whose left
component carries `rA` to `rB`. -/
private theorem smallEtaleBaseChangeLift_comp_map_of_comp_eq {Z T : Scheme.{u}} (p : T ⟶ Z)
    {A B : Z.Etale} (f : A ⟶ B) (rA : T ⟶ A.left) (rB : T ⟶ B.left) (hA : rA ≫ A.hom = p)
    (hB : rB ≫ B.hom = p) (h : rA ≫ f.left = rB) :
    smallEtaleBaseChangeLift p A rA hA ≫ (smallEtaleBaseChange p).map f =
      smallEtaleBaseChangeLift p B rB hB := by
  apply smallEtaleBaseChange_hom_ext
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (smallEtaleBaseChange_map_left_fst _ _)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  exact ((congrArg (· ≫ f.left) (pullback.lift_fst _ _ _)).trans h).trans
    (pullback.lift_fst _ _ _).symm

/-- Auxiliary form of `map_comp_unit_comp_map_smallEtaleBaseChangeLift`, stated before its first
use. -/
private theorem map_comp_unit_comp_map_lift_aux {T : Scheme.{u}} (p : T ⟶ Y.left)
    (G : EtaleModules.{u, 0} R Y.left) {A B : Y.left.Etale} (f : A ⟶ B)
    (lA : Scheme.Etale.mk (𝟙 T) ⟶ (smallEtaleBaseChange p).obj A)
    (lB : Scheme.Etale.mk (𝟙 T) ⟶ (smallEtaleBaseChange p).obj B)
    (h : lA ≫ (smallEtaleBaseChange p).map f = lB) :
    G.obj.map f.op ≫ ((etaleModuleInverseImageAdj.{u, 0} R p).unit.app G).hom.app (op A) ≫
        ((etaleModuleInverseImage.{u, 0} R p).obj G).obj.map lA.op =
      ((etaleModuleInverseImageAdj.{u, 0} R p).unit.app G).hom.app (op B) ≫
        ((etaleModuleInverseImage.{u, 0} R p).obj G).obj.map lB.op := by
  have hn := ((etaleModuleInverseImageAdj.{u, 0} R p).unit.app G).hom.naturality f.op
  have hm := congrArg (fun t => ((etaleModuleInverseImage.{u, 0} R p).obj G).obj.map
    (Quiver.Hom.op t)) h
  simp only [op_comp, Functor.map_comp] at hm
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hm)))

/-- **The section pulled back from a finite stage does not change when the stage grows.** For
`E ⊆ E'`, the section pulled back from `a ∈ G(Y_E)` is the section pulled back from its restriction
to `Y_{E'}`. -/
theorem fieldStageSection_map (G : EtaleModules.{u, 0} R Y.left) {l m : FExt k K} (d : l ≤ m)
    (x : G.obj.obj (op ((fieldStageSystem Y K).obj (op l)))) :
    fieldStageSection R Y K G m (G.obj.map ((fieldStageSystem Y K).map (homOfLE d).op).op x) =
      fieldStageSection R Y K G l x := by
  exact ConcreteCategory.congr_hom (map_comp_unit_comp_map_lift_aux R Y
    (fieldBaseChangeProj Y K) G ((fieldStageSystem Y K).map (homOfLE d).op) _ _
    (smallEtaleBaseChangeLift_comp_map_of_comp_eq _ _ _ _ _ _
      ((fieldStageCone Y K).w (homOfLE d).op))) x

/-- Pulled back sections and restriction: for `f : A ⟶ B` over `Y` and morphisms `l_A`, `l_B` from
the final object of `T` into the base changes with `l_A ≫ p^{-1}(f) = l_B`, restricting a section
over `B` to `A` and pulling back along `l_A` is pulling back along `l_B`. -/
theorem map_comp_unit_comp_map_smallEtaleBaseChangeLift {T : Scheme.{u}} (p : T ⟶ Y.left)
    (G : EtaleModules.{u, 0} R Y.left) {A B : Y.left.Etale} (f : A ⟶ B)
    (lA : Scheme.Etale.mk (𝟙 T) ⟶ (smallEtaleBaseChange p).obj A)
    (lB : Scheme.Etale.mk (𝟙 T) ⟶ (smallEtaleBaseChange p).obj B)
    (h : lA ≫ (smallEtaleBaseChange p).map f = lB) :
    G.obj.map f.op ≫ ((etaleModuleInverseImageAdj.{u, 0} R p).unit.app G).hom.app (op A) ≫
        ((etaleModuleInverseImage.{u, 0} R p).obj G).obj.map lA.op =
      ((etaleModuleInverseImageAdj.{u, 0} R p).unit.app G).hom.app (op B) ≫
        ((etaleModuleInverseImage.{u, 0} R p).obj G).obj.map lB.op := by
  exact map_comp_unit_comp_map_lift_aux R Y p G f lA lB h

/-- **Two sections over a finite stage with the same pull back agree on a larger stage** (Stacks
09YQ in degree zero): if `a, a' ∈ G(Y_E)` pull back to the same global section of `G|_{Y_K}`, they
have the same restriction to `Y_{E'}` for some finite `E' ⊇ E`. -/
theorem exists_map_eq_of_fieldStageSection_eq [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (G : EtaleModules.{u, 0} R Y.left) {l : FExt k K}
    (x x' : G.obj.obj (op ((fieldStageSystem Y K).obj (op l))))
    (h : fieldStageSection R Y K G l x = fieldStageSection R Y K G l x') :
    ∃ (m : FExt k K) (d : l ≤ m),
      G.obj.map ((fieldStageSystem Y K).map (homOfLE d).op).op x =
        G.obj.map ((fieldStageSystem Y K).map (homOfLE d).op).op x' := by
  have : CompactSpace ((fieldStageSystem Y K).obj (op ⊥)).left :=
    compactSpace_fieldStage Y K (⊥ : FExt k K)
  have : QuasiSeparatedSpace ((fieldStageSystem Y K).obj (op ⊥)).left :=
    quasiSeparatedSpace_fieldStage Y K (⊥ : FExt k K)
  have : ∀ {i j : (FExt k K)ᵒᵖ} (a : i ⟶ j), IsAffineHom ((fieldStageSystem Y K).map a).left :=
    fun a => isAffineHom_fieldStageMap Y K a
  let p := fieldBaseChangeProj Y K
  let H := (etaleModuleInverseImage.{u, 0} R p).obj G
  let Gs := (etaleModuleUnderlyingSets R Y.left).obj G
  let eF := etaleModuleInverseImageForgetIso R p G
  let eU := Adjunction.leftAdjointUniq (smallEtaleInverseImageAdjunction.{u, 0} p)
    (etaleTypeInverseImageAdj p)
  let T0 := op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))
  let W := (fieldStageSystem Y K).obj (op l)
  let t := smallEtaleBaseChangeLift p W (fieldStageProj Y K (op l))
    (fieldStageCone_π_comp_hom Y K (op l))
  let T := (etaleTypeInverseImage p).obj Gs
  let Hs := (etaleModuleUnderlyingSets R _).obj H
  have bridge : ∀ y : G.obj.obj (op W), eF.hom.hom.app T0 ((eU.hom.app Gs).hom.app T0
      (EtaleLimitSections.limitSections (fieldStageSystem Y K) (fieldStageCone Y K)
        (fieldStageCone_π_comp_hom Y K) Gs (op l) y)) = fieldStageSection R Y K G l y := by
    intro y
    have h2 := type_hom_congr ((eU.hom.app Gs).hom.naturality t.op)
      (((smallEtaleInverseImageAdjunction.{u, 0} p).unit.app Gs).hom.app (op W) y)
    have h3 := type_hom_congr (congrArg
      (fun φ : Gs ⟶ ((smallEtaleBaseChange p).sheafPushforwardContinuous
        (Type (u + 1)) Y.left.smallEtaleTopology (fieldBaseChange Y K).smallEtaleTopology).obj
          ((etaleTypeInverseImage p).obj Gs) => φ.hom.app (op W))
      (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleInverseImageAdjunction.{u, 0} p)
        (etaleTypeInverseImageAdj p) Gs)) y
    have h4 := type_hom_congr (eF.hom.hom.naturality t.op)
      (((etaleTypeInverseImageAdj p).unit.app Gs).hom.app (op W) y)
    have h5 := etaleModuleInverseImageForgetIso_hom_typeUnitSection R p G (V := W) y
    exact (congrArg (eF.hom.hom.app T0) (h2.trans (congrArg (T.obj.map t.op) h3))).trans
      (h4.trans (congrArg (Hs.obj.map t.op) h5))
  have inj : Function.Injective (fun s => eF.hom.hom.app T0 ((eU.hom.app Gs).hom.app T0 s)) :=
    fun _ _ hs => (((sheafToPresheaf _ _).mapIso (eU.app Gs)).app T0).toEquiv.injective
      ((((sheafToPresheaf _ _).mapIso eF).app T0).toEquiv.injective hs)
  obtain ⟨m, d, hm⟩ := (EtaleLimitSections.limitSections_colimit (fieldStageSystem Y K)
    (fieldStageCone Y K) (fieldStageConeIsLimit Y K) (fieldStageCone_π_comp_hom Y K) Gs).2 l x x'
    (inj ((bridge x).trans (h.trans (bridge x').symm)))
  exact ⟨m, d, hm⟩

end Stages

/-! ### `Ȳ_E ×_Ȳ Y = Y_E` -/

section StageComparison

variable {k : Type u} [Field k] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb) (K : Type u)
  [Field K] [Algebra k K] [Algebra.IsSeparable k K]

/-- **`Ȳ_E ×_Ȳ Y ⟶ Y_E`**, as étale `Y`-schemes. -/
def fieldStageDirectImageHom (l : FExt k K) :
    (smallEtaleBaseChange i.left).obj ((fieldStageSystem Yb K).obj (op l)) ⟶
      (fieldStageSystem Y K).obj (op l) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst _ i.left ≫ pullback.fst (spectrumMap k l.1) Yb.hom)
      (pullback.snd _ i.left) (by
        have chain : ∀ {A B C D E F : Scheme.{u}} {f₁ : A ⟶ B} {f₂ : B ⟶ C} {s : C ⟶ D}
            {w : B ⟶ E} {y : E ⟶ D} {s₁ : A ⟶ F} {ι : F ⟶ E} {yh : F ⟶ D},
            f₂ ≫ s = w ≫ y → f₁ ≫ w = s₁ ≫ ι → ι ≫ y = yh → (f₁ ≫ f₂) ≫ s = s₁ ≫ yh := by
          intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
          rw [Category.assoc, h₁, reassoc_of% h₂, h₃]
        exact chain pullback.condition pullback.condition (Over.w i)))
    (pullback.lift_snd _ _ _) trivial

/-- **`Y_E ⟶ Ȳ_E ×_Ȳ Y`**, as étale `Y`-schemes. -/
def fieldStageDirectImageInv (l : FExt k K) :
    (fieldStageSystem Y K).obj (op l) ⟶
      (smallEtaleBaseChange i.left).obj ((fieldStageSystem Yb K).obj (op l)) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (pullback.lift (pullback.fst (spectrumMap k l.1) Y.hom)
        (pullback.snd (spectrumMap k l.1) Y.hom ≫ i.left)
        (pullback.condition.trans ((Category.assoc _ _ _).trans
          (congrArg (_ ≫ ·) (Over.w i))).symm))
      (pullback.snd (spectrumMap k l.1) Y.hom) (pullback.lift_snd _ _ _))
    (pullback.lift_snd _ _ _) trivial

/-- `Ȳ_E ×_Ȳ Y ⟶ Y_E ⟶ Ȳ_E ×_Ȳ Y` is the identity. -/
theorem fieldStageDirectImageHom_comp_inv (l : FExt k K) :
    fieldStageDirectImageHom i K l ≫ fieldStageDirectImageInv i K l = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  have c₁ : ∀ {A₀ A₁ A₂ A₃ : Scheme.{u}} {D : A₀ ⟶ A₁} {C : A₁ ⟶ A₀} {F : A₀ ⟶ A₂}
      {F' : A₂ ⟶ A₃} {L : A₁ ⟶ A₂} {P : A₁ ⟶ A₃} {e : A₀ ⟶ A₀}, e = 𝟙 _ →
      C ≫ F = L → L ≫ F' = P → D ≫ P = F ≫ F' → ((D ≫ C) ≫ F) ≫ F' = (e ≫ F) ≫ F' := by
    intro _ _ _ _ _ _ _ _ _ _ _ he h₁ h₂ h₃
    rw [he, Category.assoc, Category.assoc, reassoc_of% h₁, h₂, h₃, Category.id_comp]
  have c₂ : ∀ {A₀ A₁ A₂ A₃ B : Scheme.{u}} {D : A₀ ⟶ A₁} {C : A₁ ⟶ A₀} {F : A₀ ⟶ A₂}
      {F' : A₂ ⟶ A₃} {L : A₁ ⟶ A₂} {S : A₁ ⟶ B} {ι : B ⟶ A₃} {S' : A₀ ⟶ B}
      {e : A₀ ⟶ A₀}, e = 𝟙 _ →
      C ≫ F = L → L ≫ F' = S ≫ ι → D ≫ S = S' → F ≫ F' = S' ≫ ι →
      ((D ≫ C) ≫ F) ≫ F' = (e ≫ F) ≫ F' := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ he h₁ h₂ h₃ h₄
    rw [he, Category.id_comp, h₄, Category.assoc, Category.assoc, reassoc_of% h₁, h₂,
      reassoc_of% h₃]
  have c₃ : ∀ {A₀ A₁ A₂ : Scheme.{u}} {D : A₀ ⟶ A₁} {C : A₁ ⟶ A₀} {F : A₀ ⟶ A₂}
      {S : A₁ ⟶ A₂} {e : A₀ ⟶ A₀}, e = 𝟙 _ → C ≫ F = S → D ≫ S = F →
      (D ≫ C) ≫ F = e ≫ F := by
    intro _ _ _ _ _ _ _ _ he h₁ h₂
    rw [he, Category.assoc, h₁, h₂, Category.id_comp]
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · exact c₁ rfl (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)
  · exact c₂ rfl (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
      pullback.condition
  · exact c₃ rfl (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)

/-- `(p̄_E ∘ i_K, p) : Y_K ⟶ Ȳ_E ×_Ȳ Y` followed by `Ȳ_E ×_Ȳ Y ⟶ Y_E` is the projection
`Y_K ⟶ Y_E`. -/
theorem fieldBaseChangeDirectImageLift_comp_fieldStageDirectImageHom_left (l : FExt k K) :
    fieldBaseChangeDirectImageLift i K (fieldStageProj Yb K (op l))
        (fieldStageCone_π_comp_hom Yb K (op l)) ≫ (fieldStageDirectImageHom i K l).left =
      fieldStageProj Y K (op l) := by
  have c₁ : ∀ {A₀ A₁ A₂ A₃ A₄ B : Scheme.{u}} {r : A₀ ⟶ A₁} {D : A₁ ⟶ A₂} {F : A₂ ⟶ A₄}
      {F₁ : A₁ ⟶ A₃} {F₂ : A₃ ⟶ A₄} {ι : A₀ ⟶ B} {ρ : B ⟶ A₃} {σ : A₀ ⟶ A₄},
      D ≫ F = F₁ ≫ F₂ → r ≫ F₁ = ι ≫ ρ → ι ≫ ρ ≫ F₂ = σ → (r ≫ D) ≫ F = σ := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
    rw [Category.assoc, h₁, reassoc_of% h₂, h₃]
  have c₂ : ∀ {A₀ A₁ A₂ A₃ : Scheme.{u}} {r : A₀ ⟶ A₁} {D : A₁ ⟶ A₂} {F : A₂ ⟶ A₃}
      {S : A₁ ⟶ A₃} {σ : A₀ ⟶ A₃}, D ≫ F = S → r ≫ S = σ → (r ≫ D) ≫ F = σ := by
    intro _ _ _ _ _ _ _ _ _ h₁ h₂
    rw [Category.assoc, h₁, h₂]
  refine pullback.hom_ext ?_ ?_
  · refine (c₁ (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) ?_).trans
      (fieldStageProj_fst Y K (op l)).symm
    exact (congrArg (fieldBaseChangeMorphism i K ≫ ·) (fieldStageProj_fst Yb K (op l))).trans
      (fieldBaseChangeMorphism_comp_snd_assoc i K _)
  · exact (c₂ (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)).trans
      (fieldStageProj_snd Y K (op l)).symm

/-- `Y_K ⟶ Ȳ_E ×_Ȳ Y ⟶ Y_E` is the projection to the finite stage, in the small étale site of
`Y_K`. -/
theorem smallEtaleBaseChangeLift_comp_fieldStageDirectImageHom (l : FExt k K) :
    smallEtaleBaseChangeLift (fieldBaseChangeProj Y K)
        ((smallEtaleBaseChange i.left).obj ((fieldStageSystem Yb K).obj (op l)))
        (fieldBaseChangeDirectImageLift i K (fieldStageProj Yb K (op l))
          (fieldStageCone_π_comp_hom Yb K (op l)))
        (fieldBaseChangeDirectImageLift_comp_hom i K _ _) ≫
        (smallEtaleBaseChange (fieldBaseChangeProj Y K)).map (fieldStageDirectImageHom i K l) =
      smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) ((fieldStageSystem Y K).obj (op l))
        (fieldStageProj Y K (op l)) (fieldStageCone_π_comp_hom Y K (op l)) := by
  exact smallEtaleBaseChangeLift_comp_map_of_comp_eq _ _ _ _ _ _
    (fieldBaseChangeDirectImageLift_comp_fieldStageDirectImageHom_left i K l)

/-- `Ȳ_E ×_Ȳ Y ⟶ Y_E` is natural in the finite stage `E`. -/
theorem fieldStageDirectImageHom_naturality {l m : FExt k K} (d : l ≤ m) :
    (smallEtaleBaseChange i.left).map ((fieldStageSystem Yb K).map (homOfLE d).op) ≫
        fieldStageDirectImageHom i K l =
      fieldStageDirectImageHom i K m ≫ (fieldStageSystem Y K).map (homOfLE d).op := by
  apply MorphismProperty.Over.Hom.ext
  have c₁ : ∀ {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Scheme.{u}} {Bm : A₀ ⟶ A₁} {Dl : A₁ ⟶ A₂}
      {F : A₂ ⟶ A₃} {P₁ : A₁ ⟶ B₀} {P₂ : B₀ ⟶ A₃} {Q₁ : A₀ ⟶ B₁} {Wg : B₁ ⟶ B₀}
      {Q₂ : B₁ ⟶ B₂} {S : B₂ ⟶ A₃} {Dm : A₀ ⟶ B₃} {Vg : B₃ ⟶ A₂} {F' : B₃ ⟶ B₂},
      Dl ≫ F = P₁ ≫ P₂ → Bm ≫ P₁ = Q₁ ≫ Wg → Wg ≫ P₂ = Q₂ ≫ S → Vg ≫ F = F' ≫ S →
      Dm ≫ F' = Q₁ ≫ Q₂ → (Bm ≫ Dl) ≫ F = (Dm ≫ Vg) ≫ F := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅
    rw [Category.assoc, h₁, reassoc_of% h₂, h₃, Category.assoc, h₄, reassoc_of% h₅]
  have c₂ : ∀ {A₀ A₁ A₂ A₃ B₁ : Scheme.{u}} {Bm : A₀ ⟶ A₁} {Dl : A₁ ⟶ A₂}
      {Sn : A₂ ⟶ A₃} {T₁ : A₁ ⟶ A₃} {T₂ : A₀ ⟶ A₃} {Dm : A₀ ⟶ B₁} {Vg : B₁ ⟶ A₂}
      {Sn' : B₁ ⟶ A₃}, Dl ≫ Sn = T₁ → Bm ≫ T₁ = T₂ → Vg ≫ Sn = Sn' → Dm ≫ Sn' = T₂ →
      (Bm ≫ Dl) ≫ Sn = (Dm ≫ Vg) ≫ Sn := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
    rw [Category.assoc, h₁, h₂, Category.assoc, h₃, h₄]
  refine pullback.hom_ext ?_ ?_
  · exact c₁ (pullback.lift_fst _ _ _) (smallEtaleBaseChange_map_left_fst _ _)
      (fieldStageMap_fst Yb K (homOfLE d).op) (fieldStageMap_fst Y K (homOfLE d).op)
      (pullback.lift_fst _ _ _)
  · exact c₂ (pullback.lift_snd _ _ _)
      (MorphismProperty.Over.w ((smallEtaleBaseChange i.left).map
        ((fieldStageSystem Yb K).map (homOfLE d).op)))
      (fieldStageMap_snd Y K (homOfLE d).op) (pullback.lift_snd _ _ _)

end StageComparison

/-! ### Bijectivity -/

section Bijective

variable (R : Type) [Ring R] {k : Type u} [Field k] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb)
  (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]

attribute [local instance] fextOrderBot fextIsDirected

/-- **The map `Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ⟶ Γ(Y_K, H|_{Y_K})` on a section coming from a finite
stage**: the section pulled back from `a ∈ (i_* H)(Ȳ_E) = H(Ȳ_E ×_Ȳ Y)` goes to the section pulled
back from the restriction of `a` to `Y_E`. -/
theorem ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap_of_fieldStageSection
    (H : EtaleModules.{u, 0} R Y.left) (l : FExt k K)
    (x : H.obj.obj (op ((smallEtaleBaseChange i.left).obj ((fieldStageSystem Yb K).obj (op l)))))
    (z : (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)))
    (hz : ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Yb K)))) z =
      fieldStageSection R Yb K ((etaleModuleDirectImage.{u, 0} R i.left).obj H) l x) :
    ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (fieldBaseChangeGlobalSectionsDirectImageMap R i K H z) =
      fieldStageSection R Y K H l (H.obj.map (fieldStageDirectImageInv i K l).op x) := by
  rw [ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap R i K H x _ z hz]
  have hc : smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) ((fieldStageSystem Y K).obj (op l))
      (fieldStageProj Y K (op l)) (fieldStageCone_π_comp_hom Y K (op l)) ≫
      (smallEtaleBaseChange (fieldBaseChangeProj Y K)).map (fieldStageDirectImageInv i K l) =
      smallEtaleBaseChangeLift (fieldBaseChangeProj Y K)
        ((smallEtaleBaseChange i.left).obj ((fieldStageSystem Yb K).obj (op l)))
        (fieldBaseChangeDirectImageLift i K (fieldStageProj Yb K (op l))
          (fieldStageCone_π_comp_hom Yb K (op l)))
        (fieldBaseChangeDirectImageLift_comp_hom i K _ _) := by
    rw [← smallEtaleBaseChangeLift_comp_fieldStageDirectImageHom i K l, Category.assoc,
      ← Functor.map_comp, fieldStageDirectImageHom_comp_inv, CategoryTheory.Functor.map_id,
      Category.comp_id]
  exact (ConcreteCategory.congr_hom (map_comp_unit_comp_map_smallEtaleBaseChangeLift R Y
    (fieldBaseChangeProj Y K) H (fieldStageDirectImageInv i K l) _ _ hc) x).symm

variable [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]

/-- **`Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ⟶ Γ(Y_K, H|_{Y_K})` is bijective**: both sides are the colimit of
the `H(Y_E) = (i_* H)(Ȳ_E)` over the finite subextensions `E ⊆ K` (Stacks 09YQ in degree zero). -/
theorem bijective_fieldBaseChangeGlobalSectionsDirectImageMap
    (H : EtaleModules.{u, 0} R Y.left) :
    Function.Bijective (fieldBaseChangeGlobalSectionsDirectImageMap R i K H) := by
  let G := (etaleModuleDirectImage.{u, 0} R i.left).obj H
  have hzero : ∀ (Z : Over (Spec (.of k))) (F : EtaleModules.{u, 0} R Z.left) (l : FExt k K),
      fieldStageSection R Z K F l 0 = 0 := fun _ _ _ => by
    rw [fieldStageSection, moduleUnitSection, map_zero]
    exact map_zero _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz0
    obtain ⟨l, x, hx⟩ := exists_fieldStageSection_eq R Yb K G z
    have h1 := ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap_of_fieldStageSection R i K H l x z
      hx
    rw [hz0, map_zero] at h1
    obtain ⟨m, d, hm⟩ := exists_map_eq_of_fieldStageSection_eq R Y K H _ 0
      (h1.symm.trans (hzero Y H l).symm)
    rw [map_zero] at hm
    apply ΓRes_etaleMkId_injective
    rw [hx, map_zero, ← fieldStageSection_map R Yb K G d x]
    have hx0 : G.obj.map ((fieldStageSystem Yb K).map (homOfLE d).op).op x = 0 := by
      have e1 : H.obj.map (fieldStageDirectImageInv i K l).op ≫
          H.obj.map (fieldStageDirectImageHom i K l).op = 𝟙 _ := by
        rw [← Functor.map_comp, ← op_comp, fieldStageDirectImageHom_comp_inv, op_id,
          CategoryTheory.Functor.map_id]
      have e2 := congrArg (fun t => H.obj.map (Quiver.Hom.op t))
        (fieldStageDirectImageHom_naturality i K d)
      simp only [op_comp, Functor.map_comp] at e2
      have e3 : H.obj.map (fieldStageDirectImageHom i K l).op
          (H.obj.map (fieldStageDirectImageInv i K l).op x) = x :=
        ConcreteCategory.congr_hom e1 x
      have e4 : H.obj.map ((smallEtaleBaseChange i.left).map
            ((fieldStageSystem Yb K).map (homOfLE d).op)).op
            (H.obj.map (fieldStageDirectImageHom i K l).op
              (H.obj.map (fieldStageDirectImageInv i K l).op x)) =
          H.obj.map (fieldStageDirectImageHom i K m).op
            (H.obj.map ((fieldStageSystem Y K).map (homOfLE d).op).op
              (H.obj.map (fieldStageDirectImageInv i K l).op x)) :=
        ConcreteCategory.congr_hom e2 _
      rwa [e3, hm, map_zero] at e4
    rw [hx0, hzero]
  · intro t
    obtain ⟨l, b, hb⟩ := exists_fieldStageSection_eq R Y K H t
    let x := H.obj.map (fieldStageDirectImageHom i K l).op b
    obtain ⟨z, hz⟩ := (show Function.Surjective ⇑(((etaleModuleInverseImage.{u, 0} R
        (fieldBaseChangeProj Yb K)).obj G).ΓRes (op (Scheme.Etale.mk
          (𝟙 (fieldBaseChange Yb K))))) by
        rw [← Sheaf.ΓNatIsoSheafSections_hom_app_general (isTerminalEtaleMkId _)]
        exact (ConcreteCategory.bijective_of_isIso _).2)
      (fieldStageSection R Yb K G l x)
    refine ⟨z, ΓRes_etaleMkId_injective R _ ?_⟩
    rw [ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap R i K H x _ z hz, hb]
    exact ConcreteCategory.congr_hom (map_comp_unit_comp_map_smallEtaleBaseChangeLift R Y
      (fieldBaseChangeProj Y K) H (fieldStageDirectImageHom i K l) _ _
      (smallEtaleBaseChangeLift_comp_fieldStageDirectImageHom i K l)) b

end Bijective

/-! ### Galois equivariance -/

section Equivariance

variable (R : Type) [Ring R] {k : Type u} [Field k] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb)
  (K : Type u) [Field K] [Algebra k K]

/-- `(r ∘ i_K, p)` after `id × Spec σ` is `(r ∘ (id × Spec σ) ∘ i_K, p)`. -/
theorem galoisBaseChange_comp_fieldBaseChangeDirectImageLift (σ : K ≃ₐ[k] K) {W : Yb.left.Etale}
    (r : fieldBaseChange Yb K ⟶ W.left) (hr : r ≫ W.hom = fieldBaseChangeProj Yb K) :
    galoisBaseChange Y K σ ≫ fieldBaseChangeDirectImageLift i K r hr =
      fieldBaseChangeDirectImageLift i K (galoisBaseChange Yb K σ ≫ r)
        (galoisBaseChange_comp_lies_over Yb K σ hr) := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (galoisBaseChange Y K σ ≫ ·)
      (pullback.lift_fst _ _ _)).trans (((reassoc_of%
        (galoisBaseChange_comp_fieldBaseChangeMorphism i K σ)) r).trans
          (pullback.lift_fst _ _ _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (galoisBaseChange Y K σ ≫ ·)
      (pullback.lift_snd _ _ _)).trans ((galoisBaseChange_comp_fst Y K σ).trans
        (pullback.lift_snd _ _ _).symm))

variable [Algebra.IsSeparable k K] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]

/-- **`Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ⟶ Γ(Y_K, H|_{Y_K})` is `Aut_k(K)`-equivariant.** -/
theorem fieldBaseChangeGlobalSectionsDirectImageMap_galoisAction (σ : K ≃ₐ[k] K)
    (H : EtaleModules.{u, 0} R Y.left) :
    fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} R Yb K σ
        ((etaleModuleDirectImage.{u, 0} R i.left).obj H) ≫
        fieldBaseChangeGlobalSectionsDirectImageMap R i K H =
      fieldBaseChangeGlobalSectionsDirectImageMap R i K H ≫
        fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} R Y K σ H := by
  ext z
  apply ΓRes_etaleMkId_injective
  obtain ⟨l, x, hz⟩ := exists_fieldStageSection_eq R Yb K
    ((etaleModuleDirectImage.{u, 0} R i.left).obj H) z
  simp only [ConcreteCategory.comp_apply]
  rw [ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap R i K H (W := (fieldStageSystem Yb K).obj
      (op l)) x _ _ (ΓRes_fieldBaseChangeGlobalSectionsGaloisAction R Yb K σ _ x _ z hz),
    ΓRes_fieldBaseChangeGlobalSectionsGaloisAction R Y K σ H x _ _
      (ΓRes_fieldBaseChangeGlobalSectionsDirectImageMap R i K H x _ z hz)]
  exact congrArg (fun t => ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj
      H).obj.map (Quiver.Hom.op t) (moduleUnitSection R (fieldBaseChangeProj Y K) H x))
    (smallEtaleBaseChangeLift_congr _ _
      (galoisBaseChange_comp_fieldBaseChangeDirectImageLift i K σ _ _).symm _ _)

end Equivariance

/-! ### The isomorphism of discrete Galois modules -/

section GaloisIso

open scoped Stacks.DiscreteModuleTopology

variable (R : Type) [Ring R] {k : Type u} [Field k] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb)
  (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]

/-- `fieldBaseChangeGlobalSectionsDirectImageMap`, as an isomorphism of `R`-modules. -/
def fieldBaseChangeGlobalSectionsDirectImageIso (H : EtaleModules.{u, 0} R Y.left) :
    (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Yb K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Yb K)).obj
          ((etaleModuleDirectImage.{u, 0} R i.left).obj H)) ≅
      (etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Y K)).obj
        ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj H) :=
  haveI := (ConcreteCategory.isIso_iff_bijective
    (fieldBaseChangeGlobalSectionsDirectImageMap R i K H)).2
    (bijective_fieldBaseChangeGlobalSectionsDirectImageMap R i K H)
  asIso (fieldBaseChangeGlobalSectionsDirectImageMap R i K H)

/-- **`Γ^Gal(Ȳ, i_* H) ≅ Γ^Gal(Y, H)`, natural in `H`**: for a morphism `i : Y ⟶ Ȳ` of
quasi-compact and quasi-separated `k`-schemes and `K/k` separable algebraic, the base change map
`(i_* H)|_{Ȳ_K} ⟶ (i_K)_*(H|_{Y_K})` followed by `Γ(Ȳ_K, (i_K)_* -) = Γ(Y_K, -)` is an isomorphism
of discrete `R[Aut_k(K)]`-modules `Γ(Ȳ_K, (i_* H)|_{Ȳ_K}) ≅ Γ(Y_K, H|_{Y_K})`. -/
def galoisGlobalSectionsMapDirectImageIso :
    etaleModuleDirectImage.{u, 0} R i.left ⋙ galoisGlobalSections R Yb K ≅
      galoisGlobalSections R Y K :=
  NatIso.ofComponents
    (fun H => ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (Action.mkIso (fieldBaseChangeGlobalSectionsDirectImageIso R i K H)
        (fun σ => fieldBaseChangeGlobalSectionsDirectImageMap_galoisAction R i K σ H))))
    (fun {H H'} v => by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      exact fieldBaseChangeGlobalSectionsDirectImageMap_naturality R i K v)

/-- **Forgetting the Galois action**, the component of `galoisGlobalSectionsMapDirectImageIso` at
`H` is `fieldBaseChangeGlobalSectionsDirectImageMap`: global sections of the base change map
`(i_* H)|_{Ȳ_K} ⟶ (i_K)_*(H|_{Y_K})`, followed by `Γ(Ȳ_K, (i_K)_* -) = Γ(Y_K, -)`. -/
theorem galoisGlobalSectionsMapDirectImageIso_hom_app (H : EtaleModules.{u, 0} R Y.left) :
    (Stacks.Injectives.continuousModuleUnderlying R (K ≃ₐ[k] K)).map
        ((galoisGlobalSectionsMapDirectImageIso R i K).hom.app H) =
      fieldBaseChangeGlobalSectionsDirectImageMap R i K H :=
  rfl

end GaloisIso

/-! ### Compactifications -/

section Compactification

open scoped Stacks.DiscreteModuleTopology

variable (R : Type) [Ring R] {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (j : CompactificationOf (Over.mk f))

/-- A quasi-compact morphism to `Spec k`, as an object over `Spec k`, is quasi-compact. -/
local instance quasiCompact_overMk_hom_of_quasiCompact [QuasiCompact f] :
    QuasiCompact (Over.mk f).hom :=
  ‹QuasiCompact f›

/-- A quasi-separated morphism to `Spec k`, as an object over `Spec k`, is quasi-separated. -/
local instance quasiSeparated_overMk_hom_of_quasiSeparated [QuasiSeparated f] :
    QuasiSeparated (Over.mk f).hom :=
  ‹QuasiSeparated f›

variable [QuasiCompact f] [QuasiSeparated f]

/-- **`Γ^Gal(X̄, j_* H) ≅ Γ^Gal(X, H)`, natural in `H`**, for a compactification `j : X ⟶ X̄`
over `k` of a quasi-compact and quasi-separated `k`-scheme `X`: the isomorphism of discrete
`R[Aut_k(k̄)]`-modules `Γ(X̄_k̄, (j_* H)|_{X̄_k̄}) ≅ Γ(X_k̄, H|_{X_k̄})` given by the base change
map `(j_* H)|_{X̄_k̄} ⟶ (j_k̄)_*(H|_{X_k̄})` and `Γ(X̄_k̄, (j_k̄)_* -) = Γ(X_k̄, -)`
(`Stacks.EtaleCohomology.galoisGlobalSectionsMapDirectImageIso`). -/
def galoisGlobalSectionsDirectImageIso :
    etaleModuleDirectImage.{u, 0} R j.immersion ⋙ galoisGlobalSections R (Over.mk j.toBase) kbar ≅
      galoisGlobalSections R (Over.mk f) kbar :=
  galoisGlobalSectionsMapDirectImageIso R (Over.homMk j.immersion (Over.w j.obj.hom)) kbar

/-- **Forgetting the Galois action**, the component of `galoisGlobalSectionsDirectImageIso` at `H`
is global sections of the base change map `(j_* H)|_{X̄_k̄} ⟶ (j_k̄)_*(H|_{X_k̄})` followed by
`Γ(X̄_k̄, (j_k̄)_* -) = Γ(X_k̄, -)`. -/
theorem galoisGlobalSectionsDirectImageIso_hom_app (H : EtaleModules.{u, 0} R X) :
    (Stacks.Injectives.continuousModuleUnderlying R (kbar ≃ₐ[k] kbar)).map
        ((galoisGlobalSectionsDirectImageIso R kbar j).hom.app H) =
      fieldBaseChangeGlobalSectionsDirectImageMap R
        (Over.homMk j.immersion (Over.w j.obj.hom) : Over.mk f ⟶ Over.mk j.toBase) kbar H :=
  rfl

end Compactification

end Stacks.EtaleCohomology

end
