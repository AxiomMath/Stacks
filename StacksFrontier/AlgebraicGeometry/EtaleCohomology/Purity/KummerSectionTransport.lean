module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerGeneratorSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerCoboundaryBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap

/-!
# The Kummer generator commutes with base change

Let `h ≫ f' = e ≫ g` be a commutative square of schemes, `g : T ⟶ S`, `h : Y ⟶ X'`, with `N`
invertible on `T` and `Y`, and let `t` be a global function on `S`, invertible on `T`, whose
pullback `f'^* t` is invertible on `Y`. The Kummer classes `∂ t ∈ Γ(S, R¹ g_* μ_N)` and
`∂ (f'^* t) ∈ Γ(X', R¹ h_* μ_N)` give morphisms `σ_{∂ t} : ℤ/N ⟶ R¹ g_* μ_N` and
`σ_{∂ (f'^* t)} : ℤ/N ⟶ R¹ h_* μ_N` (`Stacks.EtaleCohomology.Purity.torsionSectionSheafHom`), and
the degree-one base change map `f'⁻¹ R¹ g_* μ_N ⟶ R¹ h_* μ_N`
(`Stacks.EtaleCohomology.Purity.kummerBaseChangeMap`) carries the first to the second:
`f'⁻¹ σ_{∂ t} ≫ β = e ≫ σ_{∂ (f'^* t)}` with `e : f'⁻¹(ℤ/N) ≅ ℤ/N`
(`Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_localKummerClass_comp`).

The proof transposes along `f'⁻¹ ⊣ f'_*`. A morphism out of `f'⁻¹(ℤ/N)` is determined by its
transpose `ℤ/N ⟶ f'_*(-)`, that is, by one section over the final object of `S_ét`
(`Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_comp`; the transpose of `e` is
computed by `Stacks.EtaleCohomology.Purity.smallEtalePullbackAbConstantIso_transpose_apply`).
The transpose of `β` after `∂_g` is the restriction of units `g_* 𝐆_m ⟶ f'_* h_* 𝐆_m` followed
by `f'_* ∂_h`
(`Stacks.EtaleCohomology.Purity.kummerDirectImageδ_comp_homEquiv_kummerBaseChangeMap`, from the
compatibility of `∂` with base change,
`Stacks.EtaleCohomology.Purity.kummerDirectImageδ_baseChange`, and the description of the base
change map as a mate); on the unit `t` it is the restriction of `f'^* t`
(`Stacks.EtaleCohomology.Purity.homEquiv_kummerBaseChangeMap_localKummerClass`).

This is the form in which the generator property of the Kummer class of the coordinate of
`𝔸¹_k` is transported to the charts of a smooth relative curve, and in which the degree-one base
change map of relative purity is shown to be invertible.

## Main definitions

* `Stacks.EtaleCohomology.Purity.kummerBaseChangeMap`.

## Main results

* `Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_comp`.
* `Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_localKummerClass_comp`.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerCoboundaryBaseChange`, the
objects are spelled as the `δ`-functor produces them; the algebra is done on variables
(`Stacks.EtaleCohomology.Purity.square_map_comp_eq`,
`Stacks.EtaleCohomology.Purity.square_chain_eq`)
so that hypotheses are consumed up to definitional unfolding of their objects. The base change
maps are defined in the standard model of the derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology.Purity

/-- The canonical map to the sheafified constant presheaf commutes with restriction. -/
theorem toSheafify_app_comp_constantSheaf_map {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {A : Type*} [Category* A] [HasWeakSheafify J A] (M : A)
    {V W : C} (m : V ⟶ W) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op W) ≫
        ((constantSheaf J A).obj M).obj.map m.op =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op V) :=
  ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality m.op).symm.trans (Category.id_comp _)

/-- Restricting to an object and back to a terminal object is the identity. -/
theorem map_op_comp_map_op_of_isTerminal {C D : Type*} [Category* C] [Category* D]
    (F : Cᵒᵖ ⥤ D) {V W : C} (hV : IsTerminal V) (a : W ⟶ V) (q : V ⟶ W) :
    F.map a.op ≫ F.map q.op = 𝟙 (F.obj (op V)) := by
  rw [← Functor.map_comp, ← op_comp, hV.hom_ext (q ≫ a) (𝟙 V), op_id,
    CategoryTheory.Functor.map_id]

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The transpose of the identification `f⁻¹ A ≅ A` of constant sheaves**, on the canonical
sections over a final object: it carries the canonical section of `A` over the final object of
`S_ét` to the canonical section of `A` over its base change. -/
theorem smallEtalePullbackAbConstantIso_transpose_apply (M : Ab.{u + 1}) {T : S.Etale}
    (n : ToType M) :
    ((smallEtaleAdjunctionAb f).homEquiv _ _
        ((smallEtalePullbackAbConstantIso f).hom.app M)).hom.app (op T)
      ((toSheafify (smallEtaleTopology S) ((Functor.const _).obj M)).app (op T) n) =
    (toSheafify (smallEtaleTopology X) ((Functor.const _).obj M)).app
      (op ((smallEtaleBaseChange f).obj T)) n := by
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have hmkS : IsTerminal (Scheme.Etale.mk (𝟙 S)) := MorphismProperty.Over.mkIdTerminal _ _
  have hmkX : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  have hu : ∀ Y : Scheme.{u}, (smallEtaleConstantAdj Y).unit.app M =
      (toSheafify (smallEtaleTopology Y) ((Functor.const _).obj M)).app
        (op (Scheme.Etale.mk (𝟙 Y))) := fun Y =>
    Stacks.ConstantSheaf.constantSheafAdj_unit_app _ _ _ M
  have key := unit_conjugateEquiv_symm (smallEtaleConstantAdj X)
    ((smallEtaleConstantAdj S).comp (smallEtaleAdjunctionAb f))
    (smallEtalePushforwardAbΓIso f).inv M
  have hθ : ((conjugateEquiv (smallEtaleConstantAdj X)
      ((smallEtaleConstantAdj S).comp (smallEtaleAdjunctionAb f))).symm
        (smallEtalePushforwardAbΓIso f).inv).app M =
      (smallEtalePullbackAbConstantIso f).hom.app M := rfl
  rw [hθ, Adjunction.comp_unit_app, Category.assoc, Functor.comp_map, ← Functor.map_comp,
    ← Adjunction.homEquiv_unit] at key
  -- key : u_X ≫ Γiso.inv = u_S ≫ Γ_S.map θb
  have key' : (smallEtaleConstantAdj X).unit.app M =
      ((smallEtaleConstantAdj S).unit.app M ≫
        ((sheafSections (smallEtaleTopology S) Ab.{u + 1}).obj
          (op (Scheme.Etale.mk (𝟙 S)))).map ((smallEtaleAdjunctionAb f).homEquiv _ _
            ((smallEtalePullbackAbConstantIso f).hom.app M))) ≫
        (smallEtalePushforwardAbΓIso f).hom.app
          ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj M) := by
    rw [← key, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  have hc : ((smallEtaleAdjunctionAb f).homEquiv _ _
      ((smallEtalePullbackAbConstantIso f).hom.app M)).hom.app (op (Scheme.Etale.mk (𝟙 S)))
      ((toSheafify (smallEtaleTopology S) ((Functor.const _).obj M)).app
        (op (Scheme.Etale.mk (𝟙 S))) n) =
      (toSheafify (smallEtaleTopology X) ((Functor.const _).obj M)).app
        (op ((smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 S)))) n := by
    rw [hu, hu, smallEtalePushforwardAbΓIso_hom_app] at key'
    have e1n : ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj M).obj.map
        ((smallEtaleBaseChangeFinalIsTerminal f).from (Scheme.Etale.mk (𝟙 X))).op
          ((toSheafify (smallEtaleTopology X) ((Functor.const _).obj M)).app
            (op ((smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 S)))) n) =
        (toSheafify (smallEtaleTopology X) ((Functor.const _).obj M)).app
          (op (Scheme.Etale.mk (𝟙 X))) n :=
      ConcreteCategory.congr_hom (toSheafify_app_comp_constantSheaf_map (smallEtaleTopology X) M
        ((smallEtaleBaseChangeFinalIsTerminal f).from (Scheme.Etale.mk (𝟙 X)))) n
    have e2n : (toSheafify (smallEtaleTopology X) ((Functor.const _).obj M)).app
          (op (Scheme.Etale.mk (𝟙 X))) n =
        ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj M).obj.map
          ((smallEtaleBaseChangeFinalIsTerminal f).from (Scheme.Etale.mk (𝟙 X))).op
          (((smallEtaleAdjunctionAb f).homEquiv _ _
            ((smallEtalePullbackAbConstantIso f).hom.app M)).hom.app
              (op (Scheme.Etale.mk (𝟙 S)))
            ((toSheafify (smallEtaleTopology S) ((Functor.const _).obj M)).app
              (op (Scheme.Etale.mk (𝟙 S))) n)) :=
      ConcreteCategory.congr_hom key' n
    have hinv : ∀ y, ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj M).obj.map
        (hmkX.from ((smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 S)))).op
        (((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj M).obj.map
          ((smallEtaleBaseChangeFinalIsTerminal f).from (Scheme.Etale.mk (𝟙 X))).op y) = y :=
      fun y => ConcreteCategory.congr_hom (map_op_comp_map_op_of_isTerminal
        ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj M).obj
        (smallEtaleBaseChangeFinalIsTerminal f) _ _) y
    exact (hinv _).symm.trans ((congrArg _ (e2n.symm.trans e1n.symm)).trans (hinv _))
  let r : T ⟶ Scheme.Etale.mk (𝟙 S) := hmkS.from T
  refine (congrArg (ConcreteCategory.hom (((smallEtaleAdjunctionAb f).homEquiv _ _
    ((smallEtalePullbackAbConstantIso f).hom.app M)).hom.app (op T)))
      (ConcreteCategory.congr_hom
        (toSheafify_app_comp_constantSheaf_map (smallEtaleTopology S) M r) n).symm).trans ?_
  refine (NatTrans.naturality_apply ((smallEtaleAdjunctionAb f).homEquiv _ _
    ((smallEtalePullbackAbConstantIso f).hom.app M)).hom r.op
      ((toSheafify (smallEtaleTopology S) ((Functor.const _).obj M)).app
        (op (Scheme.Etale.mk (𝟙 S))) n)).trans ?_
  rw [hc]
  exact ConcreteCategory.congr_hom
    (toSheafify_app_comp_constantSheaf_map (smallEtaleTopology X) M
      ((smallEtaleBaseChange f).map r)) n

/-- **A morphism out of the inverse image of `σ_s` is read off on the transposed section.** Let
`φ : f⁻¹ F ⟶ G`, `s` a global section of `F` and `s'` one of `G`, both killed by `N`. If the
transpose `F ⟶ f_* G` of `φ` carries `s` to the restriction of `s'` to the base change of the
final object, then `f⁻¹ σ_s ≫ φ = e ≫ σ_{s'}`, `e : f⁻¹(ℤ/N) ≅ ℤ/N` being the identification of
the inverse image of a constant sheaf
(`Stacks.EtaleCohomology.smallEtalePullbackAbConstantIso`). -/
theorem pullback_map_torsionSectionSheafHom_comp {N : ℕ} [NeZero N]
    {F : Sheaf (smallEtaleTopology S) Ab.{u + 1}} {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj F ⟶ G)
    (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤)))) (hs : N • s = 0)
    (s' : ToType (G.obj.obj (op ((opensToEtale X).obj ⊤)))) (hs' : N • s' = 0)
    (h : ((smallEtaleAdjunctionAb f).homEquiv _ _ φ).hom.app (op ((opensToEtale S).obj ⊤)) s =
      G.obj.map ((isTerminal_opensToEtale_top X).from
        ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤))).op s') :
    (smallEtalePullbackAb f).map (torsionSectionSheafHom s hs) ≫ φ =
      (smallEtalePullbackAbConstantIso f).hom.app _ ≫ torsionSectionSheafHom s' hs' := by
  apply ((smallEtaleAdjunctionAb f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply ((constantSheafAdj (smallEtaleTopology S) Ab.{u + 1}
    (isTerminal_opensToEtale_top S)).homEquiv _ _).injective
  rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply,
    Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply]
  ext ⟨n⟩
  have hl := ConcreteCategory.congr_hom (toSheafify_app_comp_torsionSectionSheafHom s hs)
    (ULift.up n)
  rw [torsionSectionHom_apply] at hl
  have hr := ConcreteCategory.congr_hom (toSheafify_app_comp_torsionSectionSheafHom s' hs')
    (ULift.up n)
  rw [torsionSectionHom_apply] at hr
  have hθ := smallEtalePullbackAbConstantIso_transpose_apply f
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) (T := (opensToEtale S).obj ⊤) (ULift.up n)
  have hcX := ConcreteCategory.congr_hom (toSheafify_app_comp_constantSheaf_map
    (smallEtaleTopology X) (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))
    ((isTerminal_opensToEtale_top X).from
      ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤)))) (ULift.up n)
  have hnat := NatTrans.naturality_apply (torsionSectionSheafHom s' hs').hom
    ((isTerminal_opensToEtale_top X).from
      ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤))).op
    ((toSheafify (smallEtaleTopology X)
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
        (op ((opensToEtale X).obj ⊤)) (ULift.up n))
  change ((smallEtaleAdjunctionAb f).homEquiv _ _ φ).hom.app (op ((opensToEtale S).obj ⊤))
      ((torsionSectionSheafHom s hs).hom.app (op ((opensToEtale S).obj ⊤))
        ((toSheafify (smallEtaleTopology S)
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
            (op ((opensToEtale S).obj ⊤)) (ULift.up n))) =
    (torsionSectionSheafHom s' hs').hom.app
      (op ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤)))
      (((smallEtaleAdjunctionAb f).homEquiv _ _
        ((smallEtalePullbackAbConstantIso f).hom.app _)).hom.app
          (op ((opensToEtale S).obj ⊤))
        ((toSheafify (smallEtaleTopology S)
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
            (op ((opensToEtale S).obj ⊤)) (ULift.up n)))
  have hl' : (torsionSectionSheafHom s hs).hom.app (op ((opensToEtale S).obj ⊤))
      ((toSheafify (smallEtaleTopology S)
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
          (op ((opensToEtale S).obj ⊤)) (ULift.up n)) = n.val • s := hl
  have hr' : (torsionSectionSheafHom s' hs').hom.app (op ((opensToEtale X).obj ⊤))
      ((toSheafify (smallEtaleTopology X)
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
          (op ((opensToEtale X).obj ⊤)) (ULift.up n)) = n.val • s' := hr
  have hcX' : (torsionConstantSheaf X N).obj.map ((isTerminal_opensToEtale_top X).from
      ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤))).op
      ((toSheafify (smallEtaleTopology X)
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
          (op ((opensToEtale X).obj ⊤)) (ULift.up n)) =
      (toSheafify (smallEtaleTopology X)
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
          (op ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤))) (ULift.up n) := hcX
  refine ((congrArg (ConcreteCategory.hom (((smallEtaleAdjunctionAb f).homEquiv _ _ φ).hom.app
    (op ((opensToEtale S).obj ⊤)))) hl').trans ((map_nsmul _ _ _).trans
      (congrArg (n.val • ·) h))).trans ?_
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom ((torsionSectionSheafHom s' hs').hom.app
    (op ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤))))) hθ).symm
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom ((torsionSectionSheafHom s' hs').hom.app
    (op ((smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤))))) hcX')
  refine Eq.trans ?_ hnat.symm
  rw [hr', map_nsmul]
  rfl

/-- An algebraic identity on variables (stated so that its hypotheses are consumed up to
definitional unfolding of their objects). -/
theorem unit_comp_map_comp_eq {C D : Type*} [Category* C] [Category* D] (P : C ⥤ D) {a : D}
    {x y z : C} (η : a ⟶ P.obj x) (i : x ⟶ y) (m : y ⟶ z) (η' : a ⟶ P.obj y) (ρ : a ⟶ P.obj z)
    (h₁ : η ≫ P.map i = η') (h₂ : η' ≫ P.map m = ρ) : η ≫ P.map (i ≫ m) = ρ := by
  rw [P.map_comp, ← Category.assoc, h₁, h₂]

/-- The algebra of
`Stacks.EtaleCohomology.Purity.kummerDirectImageδ_comp_homEquiv_kummerBaseChangeMap`,
on variables. -/
theorem square_map_comp_eq {A B C D : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] (E : B ⥤ A) (G : A ⥤ C) (H : B ⥤ D) (F : D ⥤ C) (sq : E ⋙ G ≅ H ⋙ F)
    {u : A} {b m : B} {z : D} (η : u ⟶ E.obj b) (σ : b ⟶ m) (ρ : u ⟶ E.obj m)
    (hρ : η ≫ E.map σ = ρ) (d : H.obj m ⟶ z) :
    (G.map η ≫ sq.hom.app b) ≫ F.map (H.map σ ≫ d) = G.map ρ ≫ sq.hom.app m ≫ F.map d := by
  rw [← hρ, F.map_comp, G.map_comp, Category.assoc, Category.assoc, ← Category.assoc (sq.hom.app b),
    ← Functor.comp_map H F, ← sq.hom.naturality σ, Functor.comp_map, Category.assoc]

/-- The algebra of `Stacks.EtaleCohomology.Purity.homEquiv_kummerBaseChangeMap_localKummerClass`,
on variables. -/
theorem square_chain_eq {C : Type*} [Category* C] {V₁ V W P Q S T Y X' : C} (i₂ : V₁ ⟶ V)
    (i₁ : V ⟶ W) (p : W ⟶ P) (q : P ⟶ T) (g : T ⟶ S) (r : W ⟶ Y) (e : Y ⟶ T) (v : V ⟶ Y)
    (v₁ : V₁ ⟶ Y) (c : V₁ ⟶ Q) (r' : Q ⟶ Y) (h : Y ⟶ X') (f' : X' ⟶ S)
    (c₁ : p ≫ q = r ≫ e) (o₁ : i₁ ≫ r = v) (o₂ : i₂ ≫ v = v₁) (o₃ : c ≫ r' = v₁)
    (w : h ≫ f' = e ≫ g) : i₂ ≫ (i₁ ≫ p) ≫ q ≫ g = c ≫ r' ≫ h ≫ f' := by
  rw [Category.assoc, reassoc_of% c₁, reassoc_of% o₁, reassoc_of% o₂, w, ← reassoc_of% o₃]

section Kummer

open Stacks.Kummer

attribute [local instance] HasDerivedCategory.standard

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) (N : ℕ)

/-- **The degree-one base change map on `μ_N`**: `f'⁻¹ R¹ g_* μ_N ⟶ R¹ h_* e⁻¹ μ_N ⟶ R¹ h_* μ_N`,
the base change map followed by the comparison `e⁻¹ μ_N ⟶ μ_N`. -/
def kummerBaseChangeMap :
    (smallEtalePullbackAb f').obj (((smallEtalePushforwardAb g).rightDerived (0 + 1)).obj
      (kummerSequence.{u, 0} T N).X₁) ⟶
      ((smallEtalePushforwardAb h).rightDerived (0 + 1)).obj (kummerSequence.{u, 0} Y N).X₁ :=
  (higherBaseChangeMapAb f' g h e w (0 + 1)).app (kummerSequence.{u, 0} T N).X₁ ≫
    ((smallEtalePushforwardAb h).rightDerived (0 + 1)).map (kummerSequencePullbackMap e N).τ₁

/-- The unit of `e⁻¹ ⊣ e_*` followed by the comparison `e⁻¹ 𝐆_m ⟶ 𝐆_m` is the restriction of
units `𝐆_m ⟶ e_* 𝐆_m`. -/
theorem unit_comp_map_kummerSequencePullbackMap_τ₃ :
    (smallEtaleAdjunctionAb e).unit.app (kummerSequence.{u, 0} T N).X₃ ≫
        (smallEtalePushforwardAb e).map (kummerSequencePullbackMap e N).τ₃ =
      multiplicativeDirectImageComparison.{u, 0} e := by
  have h1 := Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleAdjunctionAb e)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} e) (kummerSequence.{u, 0} T N).X₃
  have h2 := multiplicativeInverseImageComparison_transpose.{u, 0} e
  rw [Adjunction.homEquiv_unit] at h2
  exact unit_comp_map_comp_eq (smallEtalePushforwardAb e) _
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage e).hom.app (kummerSequence.{u, 0} T N).X₃)
    (multiplicativeInverseImageComparison.{u, 0} e) _ _ h1 h2

variable {N} (hN0 : N ≠ 0) (hNT : IsUnit ((N : ℕ) : Γ(T, ⊤))) (hNY : IsUnit ((N : ℕ) : Γ(Y, ⊤)))

/-- **The transposed base change of the Kummer coboundary.** The transpose
`R¹ g_* μ_N ⟶ f'_* R¹ h_* μ_N` of the degree-one base change map, after `∂_g`, is the restriction
of units `g_* 𝐆_m ⟶ g_* e_* 𝐆_m ≅ f'_* h_* 𝐆_m` followed by `f'_* ∂_h`. -/
theorem kummerDirectImageδ_comp_homEquiv_kummerBaseChangeMap :
    kummerDirectImageδ g hN0 hNT ≫
        (smallEtaleAdjunctionAb f').homEquiv _ _ (kummerBaseChangeMap f' g h e w N) =
      (smallEtalePushforwardAb g).map (multiplicativeDirectImageComparison.{u, 0} e) ≫
        (smallEtaleSquarePushforwardIso f' g h e w).hom.app _ ≫
          (smallEtalePushforwardAb f').map (kummerDirectImageδ h hN0 hNY) := by
  have h4 : (smallEtaleAdjunctionAb f').homEquiv _ _
      ((smallEtaleBaseChangeAb f' g h e w).app (kummerSequence.{u, 0} T N).X₃) =
      (smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app
        (kummerSequence.{u, 0} T N).X₃) ≫
          (smallEtaleSquarePushforwardIso f' g h e w).hom.app _ := by
    rw [Adjunction.homEquiv_unit, smallEtaleBaseChangeAb_eq_mate,
      Stacks.Cohomology.BaseChange.unit_comp_map_mate]
  refine (Adjunction.homEquiv_naturality_left _ _ _).symm.trans ?_
  refine (congrArg ((smallEtaleAdjunctionAb f').homEquiv _ _)
    (kummerDirectImageδ_baseChange f' g h e w hN0 hNT hNY (kummerSequencePullbackMap e N))).trans ?_
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  refine (congrArg (· ≫ _) h4).trans ?_
  exact square_map_comp_eq (smallEtalePushforwardAb e) (smallEtalePushforwardAb g)
    (smallEtalePushforwardAb h) (smallEtalePushforwardAb f')
    (smallEtaleSquarePushforwardIso f' g h e w)
    _ _ _ (unit_comp_map_kummerSequencePullbackMap_τ₃ e N) (kummerDirectImageδ h hN0 hNY)

/-- A morphism into `⊤ ×_U U₀` pulls the punctured function of a global `t` back to the pullback
of `t` along the composite to `U`. -/
theorem appTop_puncturedFunction_top {U₀ U Z : Scheme.{u}} (j : U₀ ⟶ U)
    (φ : Z ⟶ pullback (⊤ : U.Opens).ι j) (t : Γ(U, ⊤)) :
    φ.appTop (puncturedFunction j ⊤ t) = (φ ≫ pullback.snd _ j ≫ j).appTop t := by
  rw [puncturedFunction_eq_appTop, openFunction,
    Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top]
  change (φ ≫ pullback.fst _ j ≫ (⊤ : U.Opens).ι).appTop t = _
  rw [pullback.condition]

/-- **The transposed base change map on a Kummer class.** The transpose
`R¹ g_* μ_N ⟶ f'_* R¹ h_* μ_N` of `Stacks.EtaleCohomology.Purity.kummerBaseChangeMap` carries the
Kummer class `∂ t` of a global function `t` on `S` to the restriction of the Kummer class
`∂ (f'^* t)` to the base change of the final object. -/
theorem homEquiv_kummerBaseChangeMap_localKummerClass (t : Γ(S, ⊤))
    (ht : IsUnit (puncturedFunction g ⊤ t))
    (ht' : IsUnit (puncturedFunction h ⊤ (f'.appTop t))) :
    ((smallEtaleAdjunctionAb f').homEquiv _ _ (kummerBaseChangeMap f' g h e w N)).hom.app
        (op ((opensToEtale S).obj ⊤)) (localKummerClass g hN0 hNT ⊤ t ht) =
      (kummerTarget h N).obj.map ((isTerminal_opensToEtale_top X').from
        ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤))).op
        (localKummerClass h hN0 hNY ⊤ (f'.appTop t) ht') := by
  refine (ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op ((opensToEtale S).obj ⊤)))
      (kummerDirectImageδ_comp_homEquiv_kummerBaseChangeMap f' g h e w hN0 hNT hNY))
    (ofUnit.{u, 0} (X := T) (U := puncturedOpen g ⊤) ht.unit)).trans ?_
  refine Eq.trans ?_ (NatTrans.naturality_apply (kummerDirectImageδ h hN0 hNY).hom
    ((isTerminal_opensToEtale_top X').from
      ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤))).op
    (ofUnit.{u, 0} (X := Y) (U := puncturedOpen h ⊤) ht'.unit))
  change (kummerDirectImageδ h hN0 hNY).hom.app
      (op ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤)))
      (((smallEtaleSquarePushforwardIso f' g h e w).hom.app (multiplicativeSheaf.{u, 0} Y)).hom.app
        (op ((opensToEtale S).obj ⊤))
        ((multiplicativeDirectImageComparison.{u, 0} e).hom.app (op (puncturedOpen g ⊤))
          (ofUnit.{u, 0} ht.unit))) = _
  refine congrArg (ConcreteCategory.hom ((kummerDirectImageδ h hN0 hNY).hom.app
    (op ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤))))) ?_
  change ofUnit.{u, 0} (X := Y) (U := (smallEtaleBaseChange h).obj
      ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤)))
      (Units.map ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app
          ((opensToEtale S).obj ⊤)).left.appTop.hom.toMonoidHom
        (Units.map ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app
            ((opensToEtale S).obj ⊤)).left.appTop.hom.toMonoidHom
          (Units.map (pullback.fst (puncturedOpen g ⊤).hom e).appTop.hom.toMonoidHom
            ht.unit))) =
    ofUnit.{u, 0} (Units.map ((smallEtaleBaseChange h).map ((isTerminal_opensToEtale_top X').from
        ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤)))).left.appTop.hom.toMonoidHom
          ht'.unit)
  refine congrArg ofUnit.{u, 0} (Units.ext ?_)
  simp only [Units.coe_map]
  have L := appTop_puncturedFunction_top g (((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app
    ((opensToEtale S).obj ⊤)).left ≫ ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app
      ((opensToEtale S).obj ⊤)).left ≫ pullback.fst (puncturedOpen g ⊤).hom e) t
  have R := appTop_puncturedFunction_top h ((smallEtaleBaseChange h).map
    ((isTerminal_opensToEtale_top X').from
      ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤)))).left (f'.appTop t)
  refine L.trans (Eq.trans ?_ R.symm)
  change _ = (((smallEtaleBaseChange h).map ((isTerminal_opensToEtale_top X').from
      ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤)))).left ≫
        pullback.snd _ h ≫ h ≫ f').appTop t
  refine congrArg (fun m => ConcreteCategory.hom (Scheme.Hom.appTop m) t) ?_
  have c1 : pullback.fst (puncturedOpen g ⊤).hom e ≫ pullback.snd (⊤ : S.Opens).ι g =
      pullback.snd (puncturedOpen g ⊤).hom e ≫ e := pullback.condition
  have o1 : ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app
      ((opensToEtale S).obj ⊤)).left ≫ pullback.snd (puncturedOpen g ⊤).hom e =
      ((smallEtaleBaseChange (h ≫ f')).obj ((opensToEtale S).obj ⊤)).hom :=
    MorphismProperty.Over.w ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app
      ((opensToEtale S).obj ⊤))
  have o2 := MorphismProperty.Over.w ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app
    ((opensToEtale S).obj ⊤))
  have o3 : ((smallEtaleBaseChange h).map ((isTerminal_opensToEtale_top X').from
      ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤)))).left ≫
        pullback.snd ((opensToEtale X').obj ⊤).hom h =
      ((smallEtaleBaseChange h).obj ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤))).hom :=
    MorphismProperty.Over.w ((smallEtaleBaseChange h).map
      ((isTerminal_opensToEtale_top X').from
        ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤))))
  exact square_chain_eq ((smallEtaleBaseChangeComp' h f' (h ≫ f') rfl).inv.app
      ((opensToEtale S).obj ⊤)).left
    ((smallEtaleBaseChangeComp' e g (h ≫ f') w).hom.app ((opensToEtale S).obj ⊤)).left
    (pullback.fst (puncturedOpen g ⊤).hom e) (pullback.snd (⊤ : S.Opens).ι g) g
    (pullback.snd (puncturedOpen g ⊤).hom e) e
    ((smallEtaleBaseChange (h ≫ f')).obj ((opensToEtale S).obj ⊤)).hom
    ((smallEtaleBaseChange h).obj ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤))).hom
    ((smallEtaleBaseChange h).map ((isTerminal_opensToEtale_top X').from
      ((smallEtaleBaseChange f').obj ((opensToEtale S).obj ⊤)))).left
    (pullback.snd ((opensToEtale X').obj ⊤).hom h) h f' c1 o1 o2 o3 w

/-- **The Kummer generator commutes with base change, at sheaf level.** For a commutative square
`h ≫ f' = e ≫ g` and a global function `t` on `S` invertible on `T` and with `f'^* t` invertible
on `Y`, the inverse image of `σ_{∂ t} : ℤ/N ⟶ R¹ g_* μ_N`, followed by the degree-one base change
map `Stacks.EtaleCohomology.Purity.kummerBaseChangeMap`, is `σ_{∂ (f'^* t)}` after the
identification `f'⁻¹(ℤ/N) ≅ ℤ/N`. -/
theorem pullback_map_torsionSectionSheafHom_localKummerClass_comp [NeZero N] (t : Γ(S, ⊤))
    (ht : IsUnit (puncturedFunction g ⊤ t))
    (ht' : IsUnit (puncturedFunction h ⊤ (f'.appTop t))) :
    (smallEtalePullbackAb f').map (torsionSectionSheafHom (localKummerClass g hN0 hNT ⊤ t ht)
        (nsmul_localKummerClass g hN0 hNT ⊤ t ht)) ≫ kummerBaseChangeMap f' g h e w N =
      (smallEtalePullbackAbConstantIso f').hom.app _ ≫
        torsionSectionSheafHom (localKummerClass h hN0 hNY ⊤ (f'.appTop t) ht')
          (nsmul_localKummerClass h hN0 hNY ⊤ (f'.appTop t) ht') :=
  pullback_map_torsionSectionSheafHom_comp f' (kummerBaseChangeMap f' g h e w N) _ _ _ _
    (homEquiv_kummerBaseChangeMap_localKummerClass f' g h e w hN0 hNT hNY t ht ht')

end Kummer

end Stacks.EtaleCohomology.Purity

end
