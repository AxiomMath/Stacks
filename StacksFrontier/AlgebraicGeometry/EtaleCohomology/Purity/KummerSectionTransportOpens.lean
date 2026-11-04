module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerSectionTransport

/-!
# The transposed degree-one base change map on local Kummer classes

Let `h ≫ f' = e ≫ g` be a commutative square of schemes, `g : T ⟶ S`, `h : Y ⟶ X'`, and `N`
invertible on `T` and on `Y`. The transpose `R¹ g_* μ_N ⟶ f'_* R¹ h_* μ_N` of the degree-one base
change map (`Stacks.EtaleCohomology.Purity.kummerBaseChangeMap`) carries the local Kummer class
`∂ t` of a function `t` on an open `O ⊆ S` to a section over `O ×_S X'` whose restriction to any
open `O' ⊆ f'⁻¹ O` is the local Kummer class of `f'^* t`
(`Stacks.EtaleCohomology.Purity.map_homEquiv_kummerBaseChangeMap_localKummerClass`). This
generalizes `Stacks.EtaleCohomology.Purity.homEquiv_kummerBaseChangeMap_localKummerClass` (the
case `O = ⊤` of a global function) to the local equations of a divisor.

## Main results

* `Stacks.EtaleCohomology.Purity.appTop_puncturedFunction_eq_appLE`.
* `Stacks.EtaleCohomology.Purity.map_homEquiv_kummerBaseChangeMap_localKummerClass`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

/-- A morphism into `O ×_U U₀` pulls the punctured function of `t ∈ Γ(U, O)` back to `t` along
the composite to `U`. -/
theorem appTop_puncturedFunction_eq_appLE {U₀ U Z : Scheme.{u}} (j : U₀ ⟶ U) (O : U.Opens)
    (φ : Z ⟶ pullback O.ι j) (t : Γ(U, O)) :
    φ.appTop (puncturedFunction j O t) =
      (φ ≫ pullback.fst O.ι j ≫ O.ι).appLE O ⊤ (by
        intro p _
        change O.ι ((pullback.fst O.ι j) (φ p)) ∈ O
        exact ((pullback.fst O.ι j) (φ p)).2) t := by
  rw [← Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top _ le_top]
  exact congrArg (fun ψ => ψ.hom t)
    (Scheme.Hom.appLE_comp_appLE φ (puncturedOpenHom j O) O ⊤ ⊤ _ _)

attribute [local instance] HasDerivedCategory.standard

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) {N : ℕ} (hN0 : N ≠ 0) (hNT : IsUnit ((N : ℕ) : Γ(T, ⊤)))
  (hNY : IsUnit ((N : ℕ) : Γ(Y, ⊤)))

/-- **The transposed base change map on a local Kummer class**: restricted to an open
`O' ⊆ f'⁻¹ O`, the image of `∂ t` (`t` a function on `O ⊆ S`) is `∂ (f'^* t)`. -/
theorem map_homEquiv_kummerBaseChangeMap_localKummerClass (O : S.Opens) (t : Γ(S, O))
    (ht : IsUnit (puncturedFunction g O t)) (O' : X'.Opens) (hO : O' ≤ f' ⁻¹ᵁ O)
    (ht' : IsUnit (puncturedFunction h O' (f'.appLE O O' hO t)))
    (m : (opensToEtale X').obj O' ⟶ (smallEtaleBaseChange f').obj ((opensToEtale S).obj O)) :
    (kummerTarget h N).obj.map m.op
        (((smallEtaleAdjunctionAb f').homEquiv _ _ (kummerBaseChangeMap f' g h e w N)).hom.app
          (op ((opensToEtale S).obj O)) (localKummerClass g hN0 hNT O t ht)) =
      localKummerClass h hN0 hNY O' (f'.appLE O O' hO t) ht' := by
  have H := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op ((opensToEtale S).obj O)))
      (kummerDirectImageδ_comp_homEquiv_kummerBaseChangeMap f' g h e w hN0 hNT hNY))
    (ofUnit.{u, 0} (X := T) (U := puncturedOpen g O) ht.unit)
  refine (congrArg _ H).trans ?_
  refine (NatTrans.naturality_apply (kummerDirectImageδ h hN0 hNY).hom m.op _).symm.trans ?_
  refine congrArg (ConcreteCategory.hom ((kummerDirectImageδ h hN0 hNY).hom.app
    (op ((opensToEtale X').obj O')))) ?_
  show ofUnit.{u, 0} (X := Y) (U := (smallEtaleBaseChange h).obj ((opensToEtale X').obj O'))
      (Units.map ((smallEtaleBaseChange h).map m).left.appTop.hom.toMonoidHom
        (Units.map ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app
            ((opensToEtale S).obj O)).left.appTop.hom.toMonoidHom
          (Units.map ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app
              ((opensToEtale S).obj O)).left.appTop.hom.toMonoidHom
            (Units.map (pullback.fst (puncturedOpen g O).hom e).appTop.hom.toMonoidHom
              ht.unit)))) =
    ofUnit.{u, 0} ht'.unit
  refine congrArg ofUnit.{u, 0} (Units.ext ?_)
  simp only [Units.coe_map, IsUnit.unit_spec]
  have L := appTop_puncturedFunction_eq_appLE g O (((smallEtaleBaseChange h).map m).left ≫
    ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app ((opensToEtale S).obj O)).left ≫
      ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app ((opensToEtale S).obj O)).left ≫
        pullback.fst (puncturedOpen g O).hom e) t
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at L
  refine L.trans ?_
  -- the morphism identity
  have c1 : pullback.fst (puncturedOpen g O).hom e ≫ pullback.snd O.ι g =
      pullback.snd (puncturedOpen g O).hom e ≫ e := pullback.condition
  have o1 : ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app
      ((opensToEtale S).obj O)).left ≫ pullback.snd (puncturedOpen g O).hom e =
      ((smallEtaleBaseChange (h ≫ f')).obj ((opensToEtale S).obj O)).hom :=
    MorphismProperty.Over.w ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app
      ((opensToEtale S).obj O))
  have o2 : (((smallEtaleBaseChange h).map m).left ≫
      ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app ((opensToEtale S).obj O)).left) ≫
        ((smallEtaleBaseChange (h ≫ f')).obj ((opensToEtale S).obj O)).hom =
      ((smallEtaleBaseChange h).obj ((opensToEtale X').obj O')).hom := by
    rw [Category.assoc, MorphismProperty.Over.w ((smallEtaleBaseChangeComp' h f' (h ≫ f')
      rfl).inv.app ((opensToEtale S).obj O))]
    exact MorphismProperty.Over.w ((smallEtaleBaseChange h).map m)
  have hmor := square_chain_eq (((smallEtaleBaseChange h).map m).left ≫
      ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app ((opensToEtale S).obj O)).left)
    ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app ((opensToEtale S).obj O)).left
    (pullback.fst (puncturedOpen g O).hom e) (pullback.snd O.ι g) g
    (pullback.snd (puncturedOpen g O).hom e) e
    ((smallEtaleBaseChange (h ≫ f')).obj ((opensToEtale S).obj O)).hom
    ((smallEtaleBaseChange h).obj ((opensToEtale X').obj O')).hom (𝟙 _)
    ((smallEtaleBaseChange h).obj ((opensToEtale X').obj O')).hom h f' c1 o1 o2
    (Category.id_comp _) w
  have c2 : pullback.fst O.ι g ≫ O.ι = pullback.snd O.ι g ≫ g := pullback.condition
  have c3 : pullback.fst O'.ι h ≫ O'.ι =
      ((smallEtaleBaseChange h).obj ((opensToEtale X').obj O')).hom ≫ h := pullback.condition
  have hmor' : (((smallEtaleBaseChange h).map m).left ≫
      ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app ((opensToEtale S).obj O)).left ≫
        ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app ((opensToEtale S).obj O)).left ≫
          pullback.fst (puncturedOpen g O).hom e) ≫ pullback.fst O.ι g ≫ O.ι =
      puncturedOpenHom h O' ≫ f' := by
    have e1 : (((smallEtaleBaseChange h).map m).left ≫
        ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app ((opensToEtale S).obj O)).left ≫
          ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app ((opensToEtale S).obj O)).left ≫
            pullback.fst (puncturedOpen g O).hom e) ≫ pullback.snd O.ι g ≫ g =
        (((smallEtaleBaseChange h).map m).left ≫
          ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app ((opensToEtale S).obj O)).left) ≫
          (((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app ((opensToEtale S).obj O)).left ≫
            pullback.fst (puncturedOpen g O).hom e) ≫ pullback.snd O.ι g ≫ g := by
      simp only [Category.assoc]
    have e2 : ((smallEtaleBaseChange h).obj ((opensToEtale X').obj O')).hom ≫ h ≫ f' =
        puncturedOpenHom h O' ≫ f' := by
      rw [← Category.assoc, ← c3]
      rfl
    exact (congrArg (_ ≫ ·) c2).trans (e1.trans (hmor.trans ((Category.id_comp _).trans e2)))
  rw [puncturedFunction]
  refine (congrArg (fun ψ => ψ.hom t) (appLE_eq_of_eq hmor' O ⊤ _
    (by intro p _; exact hO (top_le_preimage_puncturedOpenHom h O' trivial)))).trans ?_
  exact (congrArg (fun ψ => ψ.hom t)
    (Scheme.Hom.appLE_comp_appLE (puncturedOpenHom h O') f' O O' ⊤ hO _)).symm

end Stacks.EtaleCohomology.Purity

end
