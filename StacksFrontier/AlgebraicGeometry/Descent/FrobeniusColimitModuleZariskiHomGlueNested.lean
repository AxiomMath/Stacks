module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitModuleZariskiHomGlue
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquarePaste
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Morphisms of Frobenius-colimit modules over nested opens, and gluing along overlap schemes

`AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver` and
`AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion` identify morphisms of slice
restrictions `M.over V ⟶ N.over V` with morphisms of the transition functors of [Stacks, Tag 0EXE].
This file proves that these bijections are compatible with passing to a smaller open — the
*slice-to-slice comparison* that the roadmap in
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitTwoGeneratorSquare.lean` records as missing
for the existence half of the stack condition — and draws the gluing of morphisms with the overlap
compatibility given over chosen overlap schemes, in the transition-functor spelling.

## Main results

* `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver_overMap`: **the comparison for a nested
  pair of opens `W ≤ V`**, at an arbitrary morphism over `V`.
* `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion_overMap` and
  `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion_overMap_map`: **the comparison
  along open immersions** `a ≫ g = h`.
* `AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_pairwise`: **gluing of
  morphisms along a family of open immersions, the compatibility given over overlap schemes.**
* `Stacks.SheafOfModules.overFunctor_hom_ext_of_comp`: an assignment on morphisms of slice
  restrictions respecting composition is determined by its values on restrictions of global
  morphisms.

## Implementation notes

**No natural isomorphism on the slice category is built.** The comparison has to hold at morphisms
of slice restrictions which do not come from global morphisms, so whiskering a comparison of
functors with `CategoryTheory.SheafOfModules.overFunctor` would carry none of the content, and a
natural isomorphism of functors on the slice category would have to be checked against the
comparison isomorphisms built from `CategoryTheory.Adjunction.leftAdjointUniq`. Instead, every
morphism `φ : M.over U ⟶ N.over U` is written as `ψ.over U ≫ (χ.over U)⁻¹` with `ψ`, `χ` global
(`Stacks.SheafOfModules.exists_comp_overFunctor_map_eq`, from the adjunction `j^* ⊣ j_*` of the
open subspace, whose counit is invertible). Both sides of each comparison respect composition and
agree on restrictions of global morphisms — there by naturality of
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso` — so they agree everywhere.

**Every identification of `(overMap (homOfLE h)).obj (M.over V)` with `M.over W` is expensive** at
the Frobenius-colimit sheaf of rings, since checking it unfolds that sheaf; a declaration making
more than a couple of them exhausts the heartbeat budget. The general lemmas are therefore stated
at an arbitrary sheaf of rings, where the identification is made once at variable objects, and the
consumers are arranged so that the morphisms restricted are variables (not `Equiv.symm` images).

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe t u

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- **A functor which is the first factor of a left adjoint with invertible counit is "locally
full up to an invertible correction".** If `o ⋙ S ⊣ R` with invertible counit and `S` faithful
and conservative, then every morphism `φ : o M ⟶ o N` becomes the image of a morphism `M ⟶ P`
after composing with the image `o χ` of a morphism `χ : N ⟶ P` whose image is invertible.

Take `P = R (S (o N))`, `χ` the unit at `N`, and `ψ` the adjoint transpose of `S φ`; the triangle
identity makes `o χ` a section of the invertible counit, hence invertible. -/
theorem exists_comp_map_eq_map_of_isIso_counit (o : C ⥤ D) (S : D ⥤ E) [S.Faithful]
    [S.ReflectsIsomorphisms] {R : E ⥤ C} (adj : o ⋙ S ⊣ R) (hε : IsIso adj.counit) {M N : C}
    (φ : o.obj M ⟶ o.obj N) :
    ∃ (P : C) (ψ : M ⟶ P) (χ : N ⟶ P), IsIso (o.map χ) ∧ φ ≫ o.map χ = o.map ψ := by
  have htri : (o ⋙ S).map (adj.unit.app N) = inv (adj.counit.app ((o ⋙ S).obj N)) :=
    IsIso.eq_inv_of_inv_hom_id (adj.left_triangle_components N)
  have hc : (o ⋙ S).map (adj.unit.app M ≫ R.map (S.map φ)) ≫
      adj.counit.app ((o ⋙ S).obj N) = S.map φ := by
    rw [Functor.map_comp, Category.assoc]
    exact (congrArg _ (adj.counit_naturality (S.map φ))).trans
      (adj.left_triangle_components_assoc M (S.map φ))
  refine ⟨R.obj ((o ⋙ S).obj N), adj.unit.app M ≫ R.map (S.map φ), adj.unit.app N, ?_, ?_⟩
  · have : IsIso (S.map (o.map (adj.unit.app N))) := by
      show IsIso ((o ⋙ S).map (adj.unit.app N))
      rw [htri]
      infer_instance
    exact isIso_of_reflects_iso _ S
  · apply S.map_injective
    rw [S.map_comp]
    show S.map φ ≫ (o ⋙ S).map (adj.unit.app N) =
      (o ⋙ S).map (adj.unit.app M ≫ R.map (S.map φ))
    rw [htri, IsIso.comp_inv_eq, hc]

end CategoryTheory.Adjunction

namespace Stacks.SheafOfModules

variable {Z : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}}

/-- **Every morphism of slice restrictions is, up to an invertible restriction, the restriction
of a global morphism.** For `φ : M.over U ⟶ N.over U` there are a module `P`, a morphism
`ψ : M ⟶ P` and a morphism `χ : N ⟶ P` whose restriction to `U` is invertible, with
`φ ≫ χ.over U = ψ.over U`.

This is `CategoryTheory.Adjunction.exists_comp_map_eq_map_of_isIso_counit` for restriction to the
open subspace `U` and its right adjoint `ExtensionByZeroModules.jPush`, whose counit is invertible
(`j^* j_* = id`); restriction to the slice followed by the equivalence
`TopologicalSpace.Opens.sheafOfModulesEquivOver` *is* restriction to the open subspace. -/
theorem exists_comp_overFunctor_map_eq (U : Opens Z)
    {M N : _root_.SheafOfModules.{u} O} (φ : M.over U ⟶ N.over U) :
    ∃ (P : _root_.SheafOfModules.{u} O) (ψ : M ⟶ P) (χ : N ⟶ P),
      IsIso ((_root_.SheafOfModules.overFunctor O U).map χ) ∧
        φ ≫ (_root_.SheafOfModules.overFunctor O U).map χ =
          (_root_.SheafOfModules.overFunctor O U).map ψ :=
  Adjunction.exists_comp_map_eq_map_of_isIso_counit (_root_.SheafOfModules.overFunctor O U)
    ((U.sheafOfModulesEquivOver O).functor :
      _root_.SheafOfModules.{u} (O.over U) ⥤
        _root_.SheafOfModules.{u} (ExtensionByZeroModules.resRing U O))
    (ExtensionByZeroModules.jStarAdjunction U O)
    (ExtensionByZeroModules.isIso_jStarAdjunction_counit U O) φ

/-- **An assignment on morphisms of slice restrictions which respects composition is determined by
its values on restrictions of global morphisms.** Two such assignments `F₁`, `F₂`, with values in
`G P ⟶ G Q` for a functor `G` on global modules and both sending the restriction of a global `f`
to `G f`, agree at every morphism `φ : M.over U ⟶ N.over U`, global or not.

By `Stacks.SheafOfModules.exists_comp_overFunctor_map_eq`, `φ = ψ.over U ≫ (χ.over U)⁻¹` with `ψ`,
`χ` global; both assignments send `(χ.over U)⁻¹` to the inverse of `G χ`. This is what replaces a
natural isomorphism of functors on the slice category: no comparison of comparison isomorphisms is
needed, only compatibility with composition. -/
theorem overFunctor_hom_ext_of_comp {E : Type*} [Category E] (U : Opens Z)
    (G : _root_.SheafOfModules.{u} O ⥤ E)
    (F₁ F₂ : ∀ {P Q : _root_.SheafOfModules.{u} O}, (P.over U ⟶ Q.over U) → (G.obj P ⟶ G.obj Q))
    (h₁ : ∀ {P Q K : _root_.SheafOfModules.{u} O} (f : P.over U ⟶ Q.over U)
      (g : Q.over U ⟶ K.over U), F₁ (f ≫ g) = F₁ f ≫ F₁ g)
    (h₂ : ∀ {P Q K : _root_.SheafOfModules.{u} O} (f : P.over U ⟶ Q.over U)
      (g : Q.over U ⟶ K.over U), F₂ (f ≫ g) = F₂ f ≫ F₂ g)
    (e₁ : ∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
      F₁ ((_root_.SheafOfModules.overFunctor O U).map f) = G.map f)
    (e₂ : ∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
      F₂ ((_root_.SheafOfModules.overFunctor O U).map f) = G.map f)
    {M N : _root_.SheafOfModules.{u} O} (φ : M.over U ⟶ N.over U) : F₁ φ = F₂ φ := by
  obtain ⟨P, ψ, χ, hχ, hφ⟩ := exists_comp_overFunctor_map_eq U φ
  have hφ' : φ = (_root_.SheafOfModules.overFunctor O U).map ψ ≫
      inv ((_root_.SheafOfModules.overFunctor O U).map χ) := (IsIso.eq_comp_inv _).mpr hφ
  have hl : ∀ (F : ∀ {P Q : _root_.SheafOfModules.{u} O},
        (P.over U ⟶ Q.over U) → (G.obj P ⟶ G.obj Q)),
      (∀ {P Q K : _root_.SheafOfModules.{u} O} (f : P.over U ⟶ Q.over U)
        (g : Q.over U ⟶ K.over U), F (f ≫ g) = F f ≫ F g) →
      (∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
        F ((_root_.SheafOfModules.overFunctor O U).map f) = G.map f) →
      G.map χ ≫ F (inv ((_root_.SheafOfModules.overFunctor O U).map χ)) = 𝟙 _ ∧
        F (inv ((_root_.SheafOfModules.overFunctor O U).map χ)) ≫ G.map χ = 𝟙 _ := by
    intro F hF eF
    refine ⟨?_, ?_⟩
    · rw [← eF, ← hF, IsIso.hom_inv_id, ← (_root_.SheafOfModules.overFunctor O U).map_id, eF,
        G.map_id]
    · rw [← eF, ← hF, IsIso.inv_hom_id, ← (_root_.SheafOfModules.overFunctor O U).map_id, eF,
        G.map_id]
  have hinv : F₁ (inv ((_root_.SheafOfModules.overFunctor O U).map χ)) =
      F₂ (inv ((_root_.SheafOfModules.overFunctor O U).map χ)) := by
    obtain ⟨-, h1⟩ := hl (fun f => F₁ f) h₁ e₁
    obtain ⟨h2, -⟩ := hl (fun f => F₂ f) h₂ e₂
    calc F₁ (inv ((_root_.SheafOfModules.overFunctor O U).map χ))
        = F₁ (inv ((_root_.SheafOfModules.overFunctor O U).map χ)) ≫ G.map χ ≫
            F₂ (inv ((_root_.SheafOfModules.overFunctor O U).map χ)) := by rw [h2, Category.comp_id]
      _ = F₂ (inv ((_root_.SheafOfModules.overFunctor O U).map χ)) := by
            rw [← Category.assoc, h1, Category.id_comp]
  rw [hφ', h₁, h₂, e₁, e₂, hinv]

/-- **The same, read after passing to a smaller open.** For `W ≤ V`, an assignment `H` on
morphisms over `W` and an assignment `F` on morphisms over `V`, both respecting composition and
both sending restrictions of global morphisms to their image under `G`, satisfy
`H (φ restricted to W) = F φ` at every morphism `φ` over `V`.

The restriction from `V` to `W` is named once, as a local function, so that the identification of
`(overMap (homOfLE hle)).obj (M.over V)` with `M.over W` is made at variable objects only; every
further occurrence of that identification costs a comparison which unfolds the sheaf of rings. -/
theorem overMap_hom_ext_of_comp {E : Type*} [Category E] {V W : Opens Z} (hle : W ≤ V)
    (G : _root_.SheafOfModules.{u} O ⥤ E)
    (H : ∀ {P Q : _root_.SheafOfModules.{u} O}, (P.over W ⟶ Q.over W) → (G.obj P ⟶ G.obj Q))
    (F : ∀ {P Q : _root_.SheafOfModules.{u} O}, (P.over V ⟶ Q.over V) → (G.obj P ⟶ G.obj Q))
    (hH : ∀ {P Q K : _root_.SheafOfModules.{u} O} (f : P.over W ⟶ Q.over W)
      (g : Q.over W ⟶ K.over W), H (f ≫ g) = H f ≫ H g)
    (hF : ∀ {P Q K : _root_.SheafOfModules.{u} O} (f : P.over V ⟶ Q.over V)
      (g : Q.over V ⟶ K.over V), F (f ≫ g) = F f ≫ F g)
    (eH : ∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
      H ((_root_.SheafOfModules.overFunctor O W).map f) = G.map f)
    (eF : ∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
      F ((_root_.SheafOfModules.overFunctor O V).map f) = G.map f)
    {M N : _root_.SheafOfModules.{u} O} (φ : M.over V ⟶ N.over V) :
    H ((_root_.SheafOfModules.overMap O (homOfLE hle)).map φ) = F φ := by
  let ov : ∀ {P Q : _root_.SheafOfModules.{u} O}, (P.over V ⟶ Q.over V) → (P.over W ⟶ Q.over W) :=
    fun f => (_root_.SheafOfModules.overMap O (homOfLE hle)).map f
  have hov : ∀ {P Q K : _root_.SheafOfModules.{u} O} (f : P.over V ⟶ Q.over V)
      (g : Q.over V ⟶ K.over V), ov (f ≫ g) = ov f ≫ ov g :=
    fun _ _ => _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
      ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))
  have h1 : ∀ {P Q K : _root_.SheafOfModules.{u} O} (f : P.over V ⟶ Q.over V)
      (g : Q.over V ⟶ K.over V), H (ov (f ≫ g)) = H (ov f) ≫ H (ov g) :=
    fun f g => (congrArg H (hov f g)).trans (hH _ _)
  have e1 : ∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
      H (ov ((_root_.SheafOfModules.overFunctor O V).map f)) = G.map f :=
    fun f => (congrArg H (_root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
      ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)) :
        ov ((_root_.SheafOfModules.overFunctor O V).map f) =
          (_root_.SheafOfModules.overFunctor O W).map f)).trans (eH f)
  exact overFunctor_hom_ext_of_comp V G (fun f => H (ov f)) F h1 hF e1 eF φ

/-- A version of `overMap_hom_ext_of_comp` where `F` is conjugated by a comparison `K ⋙ L ≅ G`. -/
private theorem overMap_hom_ext_of_comp_conj {E D : Type*} [Category E] [Category D]
    {V W : Opens Z} (hle : W ≤ V) (G : _root_.SheafOfModules.{u} O ⥤ E)
    (K : _root_.SheafOfModules.{u} O ⥤ D) (L : D ⥤ E) (T : K ⋙ L ≅ G)
    (H : ∀ {P Q : _root_.SheafOfModules.{u} O}, (P.over W ⟶ Q.over W) → (G.obj P ⟶ G.obj Q))
    (F : ∀ {P Q : _root_.SheafOfModules.{u} O}, (P.over V ⟶ Q.over V) → (K.obj P ⟶ K.obj Q))
    (hH : ∀ {P Q R : _root_.SheafOfModules.{u} O} (f : P.over W ⟶ Q.over W)
      (g : Q.over W ⟶ R.over W), H (f ≫ g) = H f ≫ H g)
    (hF : ∀ {P Q R : _root_.SheafOfModules.{u} O} (f : P.over V ⟶ Q.over V)
      (g : Q.over V ⟶ R.over V), F (f ≫ g) = F f ≫ F g)
    (eH : ∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
      H ((_root_.SheafOfModules.overFunctor O W).map f) = G.map f)
    (eF : ∀ {P Q : _root_.SheafOfModules.{u} O} (f : P ⟶ Q),
      F ((_root_.SheafOfModules.overFunctor O V).map f) = K.map f)
    {M N : _root_.SheafOfModules.{u} O} (φ : M.over V ⟶ N.over V) :
    H ((_root_.SheafOfModules.overMap O (homOfLE hle)).map φ) =
      T.inv.app M ≫ L.map (F φ) ≫ T.hom.app N := by
  refine overMap_hom_ext_of_comp hle G H (fun f => T.inv.app _ ≫ L.map (F f) ≫ T.hom.app _)
    hH ?_ eH ?_ φ
  · intro P Q R f f'
    simp [hF]
  · intro P Q f
    rw [eF]
    exact (congrArg (fun t => T.inv.app P ≫ t) (T.hom.naturality f)).trans
      (T.inv_hom_id_app_assoc P (G.map f))

/-- Two morphisms over `V₁` and `V₂` whose restrictions to a common smaller open `H` agree have
the same restriction to every open `W ≤ H`: a component of the restriction to `W` *is* a component
of the restriction to `H`. -/
theorem overMap_map_eq_of_overMap_map_eq {V₁ V₂ H W : Opens Z} (h₁ : H ≤ V₁) (h₂ : H ≤ V₂)
    (hW : W ≤ H) (hW₁ : W ≤ V₁) (hW₂ : W ≤ V₂) {M N : _root_.SheafOfModules.{u} O}
    (θ₁ : M.over V₁ ⟶ N.over V₁) (θ₂ : M.over V₂ ⟶ N.over V₂)
    (hθ : @Eq (M.over H ⟶ N.over H)
      ((_root_.SheafOfModules.overMap O (homOfLE h₁)).map θ₁)
      ((_root_.SheafOfModules.overMap O (homOfLE h₂)).map θ₂)) :
    (_root_.SheafOfModules.overMap O (homOfLE hW₁)).map θ₁ =
      (_root_.SheafOfModules.overMap O (homOfLE hW₂)).map θ₂ :=
  _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T =>
    congrArg (fun t : M.over H ⟶ N.over H =>
      t.val.app (op (Over.mk (homOfLE ((leOfHom T.unop.hom).trans hW))))) hθ)

end Stacks.SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver` respects composition. -/
theorem frobeniusColimitPullbackHomEquivOver_comp (V : X.Opens)
    (hV : IsInCharacteristic V.toScheme p)
    {M N K : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (f : M.over V ⟶ N.over V) (g : N.over V ⟶ K.over V) :
    frobeniusColimitPullbackHomEquivOver X p hX V hV M K (f ≫ g) =
      frobeniusColimitPullbackHomEquivOver X p hX V hV M N f ≫
        frobeniusColimitPullbackHomEquivOver X p hX V hV N K g :=
  (congrArg (Iso.homCongr ((frobeniusColimitModuleRestrictIsoPullback X p hX V hV).app M)
      ((frobeniusColimitModuleRestrictIsoPullback X p hX V hV).app K))
    ((frobeniusColimitModuleOpenEquiv X p hX V hV).functor.map_comp f g)).trans
      (Iso.homCongr_comp _ _ _ _ _)

/-- `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOfFactor` respects composition. -/
theorem frobeniusColimitPullbackHomEquivOfFactor_comp (V : X.Opens)
    (hV : IsInCharacteristic V.toScheme p) {Y : Scheme.{u}} (j : Y ⟶ X)
    (hY : IsInCharacteristic Y p) (θ : Y ⟶ V.toScheme) [IsIso θ] (hθ : θ ≫ V.ι = j)
    {M N K : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (f : (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj N)
    (g : (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj N ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj K) :
    frobeniusColimitPullbackHomEquivOfFactor X p hX V hV j hY θ hθ M K (f ≫ g) =
      frobeniusColimitPullbackHomEquivOfFactor X p hX V hV j hY θ hθ M N f ≫
        frobeniusColimitPullbackHomEquivOfFactor X p hX V hV j hY θ hθ N K g :=
  (congrArg (Iso.homCongr ((frobeniusColimitPullbackTriangleIso p θ V.ι j hY hV hX hθ).app M)
      ((frobeniusColimitPullbackTriangleIso p θ V.ι j hY hV hX hθ).app K))
    ((frobeniusColimitPullbackEquivOfIso p (asIso θ) hY hV).functor.map_comp f g)).trans
      (Iso.homCongr_comp _ _ _ _ _)

/-- `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion` respects composition. -/
theorem frobeniusColimitPullbackHomEquivOpenImmersion_comp {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (hY : IsInCharacteristic Y p)
    {M N K : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (f : M.over g.opensRange ⟶ N.over g.opensRange)
    (f' : N.over g.opensRange ⟶ K.over g.opensRange) :
    frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY M K (f ≫ f') =
      frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY M N f ≫
        frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY N K f' := by
  unfold frobeniusColimitPullbackHomEquivOpenImmersion
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
    frobeniusColimitPullbackHomEquivOver_comp, frobeniusColimitPullbackHomEquivOfFactor_comp]

/-- **The slice-to-slice comparison along open immersions, at an arbitrary slice morphism.** For
open immersions `g : Y ⟶ X` and `h : Y' ⟶ X` with `a ≫ g = h`, restricting a morphism
`φ : M.over g.opensRange ⟶ N.over g.opensRange` to the smaller open `h.opensRange` corresponds,
under `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion`, to the transition of the
corresponding morphism along `a`, conjugated by
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`.

The morphism `φ` is arbitrary — not a restriction of a global morphism. Both sides respect
composition and send the restriction of a global morphism `f` to `h^* f`, so they agree by
`Stacks.SheafOfModules.overMap_hom_ext_of_comp`. -/
theorem frobeniusColimitPullbackHomEquivOpenImmersion_overMap_map {Y Y' : Scheme.{u}}
    (g : Y ⟶ X) [IsOpenImmersion g] (a : Y' ⟶ Y) (h : Y' ⟶ X) [IsOpenImmersion h]
    (hY : IsInCharacteristic Y p) (hY' : IsInCharacteristic Y' p) (ha : a ≫ g = h)
    (hle : h.opensRange ≤ g.opensRange)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ : M.over g.opensRange ⟶ N.over g.opensRange) :
    frobeniusColimitPullbackHomEquivOpenImmersion X p hX h hY' M N
        ((_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX)
          (homOfLE hle)).map φ) =
      (frobeniusColimitPullbackTriangleIso p a g h hY' hY hX ha).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p a hY' hY)).map
          (frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY M N φ) ≫
        (frobeniusColimitPullbackTriangleIso p a g h hY' hY hX ha).hom.app N := by
  exact Stacks.SheafOfModules.overMap_hom_ext_of_comp_conj hle
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p h hY' hX))
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p g hY hX))
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p a hY' hY))
    (frobeniusColimitPullbackTriangleIso p a g h hY' hY hX ha)
    (fun {P Q} f => frobeniusColimitPullbackHomEquivOpenImmersion X p hX h hY' P Q f)
    (fun {P Q} f => frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY P Q f)
    (fun f f' => frobeniusColimitPullbackHomEquivOpenImmersion_comp X p hX h hY' f f')
    (fun f f' => frobeniusColimitPullbackHomEquivOpenImmersion_comp X p hX g hY f f')
    (fun f => frobeniusColimitPullbackHomEquivOpenImmersion_apply_overFunctor_map X p hX h hY' f)
    (fun f => frobeniusColimitPullbackHomEquivOpenImmersion_apply_overFunctor_map X p hX g hY f)
    φ

/-- **The slice-to-slice comparison along open immersions, in the transition-functor spelling.**
`AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion_overMap_map` read at the slice
morphism corresponding to a given morphism `ψ : g^* M ⟶ g^* N`: restricting it to the smaller open
`h.opensRange` corresponds to `a^* ψ` conjugated by
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`. This is the comparison the existence half
of the stack condition at a Zariski family needs: a local solution over one member is compared with
one over another member on their overlap. -/
theorem frobeniusColimitPullbackHomEquivOpenImmersion_overMap {Y Y' : Scheme.{u}}
    (g : Y ⟶ X) [IsOpenImmersion g] (a : Y' ⟶ Y) (h : Y' ⟶ X) [IsOpenImmersion h]
    (hY : IsInCharacteristic Y p) (hY' : IsInCharacteristic Y' p) (ha : a ≫ g = h)
    (hle : h.opensRange ≤ g.opensRange)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (ψ : (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p g hY hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p g hY hX)).obj N) :
    frobeniusColimitPullbackHomEquivOpenImmersion X p hX h hY' M N
        ((_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX)
          (homOfLE hle)).map
          ((frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY M N).symm ψ)) =
      (frobeniusColimitPullbackTriangleIso p a g h hY' hY hX ha).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p a hY' hY)).map ψ ≫
        (frobeniusColimitPullbackTriangleIso p a g h hY' hY hX ha).hom.app N :=
  (frobeniusColimitPullbackHomEquivOpenImmersion_overMap_map X p hX g a h hY hY' ha hle _).trans
    (congrArg (fun t => (frobeniusColimitPullbackTriangleIso p a g h hY' hY hX ha).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p a hY' hY)).map t ≫
        (frobeniusColimitPullbackTriangleIso p a g h hY' hY hX ha).hom.app N)
      (Equiv.apply_symm_apply _ ψ))

/-- **The slice-to-slice comparison for a nested pair of opens.** For `W ≤ V` and an arbitrary
`φ : M.over V ⟶ N.over V`, the bijection
`AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver` at `W` of the restriction of `φ` to `W` is
the transition along `X.homOfLE h` of its value at `V`, conjugated by
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`. Proved as the open-immersion form, by
`Stacks.SheafOfModules.overMap_hom_ext_of_comp`. -/
theorem frobeniusColimitPullbackHomEquivOver_overMap {V W : X.Opens} (h : W ≤ V)
    (hV : IsInCharacteristic V.toScheme p) (hW : IsInCharacteristic W.toScheme p)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ : M.over V ⟶ N.over V) :
    frobeniusColimitPullbackHomEquivOver X p hX W hW M N
        ((_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE h)).map φ) =
      (frobeniusColimitPullbackTriangleIso p (X.homOfLE h) V.ι W.ι hW hV hX
          (Scheme.homOfLE_ι X h)).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (X.homOfLE h) hW hV)).map
            (frobeniusColimitPullbackHomEquivOver X p hX V hV M N φ) ≫
        (frobeniusColimitPullbackTriangleIso p (X.homOfLE h) V.ι W.ι hW hV hX
          (Scheme.homOfLE_ι X h)).hom.app N := by
  exact Stacks.SheafOfModules.overMap_hom_ext_of_comp_conj h
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p W.ι hW hX))
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p V.ι hV hX))
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (X.homOfLE h) hW hV))
    (frobeniusColimitPullbackTriangleIso p (X.homOfLE h) V.ι W.ι hW hV hX (Scheme.homOfLE_ι X h))
    (fun {P Q} f => frobeniusColimitPullbackHomEquivOver X p hX W hW P Q f)
    (fun {P Q} f => frobeniusColimitPullbackHomEquivOver X p hX V hV P Q f)
    (fun f f' => frobeniusColimitPullbackHomEquivOver_comp X p hX W hW f f')
    (fun f f' => frobeniusColimitPullbackHomEquivOver_comp X p hX V hV f f')
    (fun f => frobeniusColimitPullbackHomEquivOver_apply_overFunctor_map X p hX W hW f)
    (fun f => frobeniusColimitPullbackHomEquivOver_apply_overFunctor_map X p hX V hV f)
    φ

/-- `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver` sends identities to identities. -/
theorem frobeniusColimitPullbackHomEquivOver_id (V : X.Opens)
    (hV : IsInCharacteristic V.toScheme p)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :
    frobeniusColimitPullbackHomEquivOver X p hX V hV M M (𝟙 _) = 𝟙 _ :=
  (frobeniusColimitPullbackHomEquivOver_apply_overFunctor_map X p hX V hV (𝟙 M)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion` sends identities to
identities. -/
theorem frobeniusColimitPullbackHomEquivOpenImmersion_id {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (hY : IsInCharacteristic Y p)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :
    frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY M M (𝟙 _) = 𝟙 _ :=
  (frobeniusColimitPullbackHomEquivOpenImmersion_apply_overFunctor_map X p hX g hY (𝟙 M)).trans
    (CategoryTheory.Functor.map_id _ _)

/-- **Local solutions compatible in the transition-functor spelling over an overlap scheme have
equal slice restrictions below it.** If `h : Y₁₂ ⟶ X` is an open immersion factoring as `a ≫ g₁`
and `b ≫ g₂` and the transitions of the images of `φ₁`, `φ₂` along `a` and `b` agree (conjugated
by `AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`), then the slice restrictions of `φ₁`
and `φ₂` to any `W ≤ h.opensRange` agree. Over `h.opensRange` this is the slice-to-slice
comparison and injectivity of `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion`;
below it, `Stacks.SheafOfModules.overMap_map_eq_of_overMap_map_eq`. -/
theorem frobeniusColimitPullbackHomEquivOpenImmersion_overMap_eq_of_triangle
    {Y₁ Y₂ Y₁₂ : Scheme.{u}}
    (g₁ : Y₁ ⟶ X) [IsOpenImmersion g₁] (g₂ : Y₂ ⟶ X) [IsOpenImmersion g₂]
    (h : Y₁₂ ⟶ X) [IsOpenImmersion h] (a : Y₁₂ ⟶ Y₁) (b : Y₁₂ ⟶ Y₂)
    (hY₁ : IsInCharacteristic Y₁ p) (hY₂ : IsInCharacteristic Y₂ p)
    (hY₁₂ : IsInCharacteristic Y₁₂ p) (ha : a ≫ g₁ = h) (hb : b ≫ g₂ = h)
    (h₁ : h.opensRange ≤ g₁.opensRange) (h₂ : h.opensRange ≤ g₂.opensRange)
    {W : X.Opens} (hW : W ≤ h.opensRange) (hW₁ : W ≤ g₁.opensRange) (hW₂ : W ≤ g₂.opensRange)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ₁ : M.over g₁.opensRange ⟶ N.over g₁.opensRange)
    (φ₂ : M.over g₂.opensRange ⟶ N.over g₂.opensRange)
    (hφ : (frobeniusColimitPullbackTriangleIso p a g₁ h hY₁₂ hY₁ hX ha).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p a hY₁₂ hY₁)).map
          (frobeniusColimitPullbackHomEquivOpenImmersion X p hX g₁ hY₁ M N φ₁) ≫
        (frobeniusColimitPullbackTriangleIso p a g₁ h hY₁₂ hY₁ hX ha).hom.app N =
      (frobeniusColimitPullbackTriangleIso p b g₂ h hY₁₂ hY₂ hX hb).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p b hY₁₂ hY₂)).map
          (frobeniusColimitPullbackHomEquivOpenImmersion X p hX g₂ hY₂ M N φ₂) ≫
        (frobeniusColimitPullbackTriangleIso p b g₂ h hY₁₂ hY₂ hX hb).hom.app N) :
    (_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE hW₁)).map φ₁ =
      (_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE hW₂)).map φ₂ :=
  Stacks.SheafOfModules.overMap_map_eq_of_overMap_map_eq h₁ h₂ hW hW₁ hW₂ φ₁ φ₂
    ((frobeniusColimitPullbackHomEquivOpenImmersion X p hX h hY₁₂ M N).injective
      ((frobeniusColimitPullbackHomEquivOpenImmersion_overMap_map X p hX g₁ a h hY₁ hY₁₂ ha h₁
          φ₁).trans
        (hφ.trans (frobeniusColimitPullbackHomEquivOpenImmersion_overMap_map X p hX g₂ b h hY₂
          hY₁₂ hb h₂ φ₂).symm)))

/-- **Morphisms of sheaves of `colim_F 𝒪_X`-modules given in the transition-functor spelling of
[Stacks, Tag 0EXE] over the members of a family of open immersions whose images cover `X`, and
agreeing over chosen overlap schemes, glue to a unique global morphism.**

The overlap of the `i`-th and `j`-th member is presented by an open immersion `h i j` with image
the intersection of the two images, factoring through both members by `a i j` and `b i j`; the
compatibility is the equality of the two transitions of the given morphisms to it, conjugated by
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`. This is the shape a morphism of descent
data along a Zariski family of the big h category over `S` has. It is
`AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion_of_overMap`, the
slice compatibility being supplied by
`AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion_overMap_eq_of_triangle`. -/
theorem existsUnique_frobeniusColimitPullback_map_eq_of_pairwise {ι : Type t}
    {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hY : ∀ i, IsInCharacteristic (Y i) p) (hcov : ⨆ i, (g i).opensRange = ⊤)
    {Y₂ : ι → ι → Scheme.{u}} (h : ∀ i j, Y₂ i j ⟶ X) [∀ i j, IsOpenImmersion (h i j)]
    (hY₂ : ∀ i j, IsInCharacteristic (Y₂ i j) p)
    (hrange : ∀ i j, (h i j).opensRange = (g i).opensRange ⊓ (g j).opensRange)
    (a : ∀ i j, Y₂ i j ⟶ Y i) (b : ∀ i j, Y₂ i j ⟶ Y j)
    (ha : ∀ i j, a i j ≫ g i = h i j) (hb : ∀ i j, b i j ≫ g j = h i j)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (ψ : ∀ i, (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj N)
    (hψ : ∀ i j,
      (frobeniusColimitPullbackTriangleIso p (a i j) (g i) (h i j) (hY₂ i j) (hY i) hX
          (ha i j)).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (a i j) (hY₂ i j) (hY i))).map (ψ i) ≫
        (frobeniusColimitPullbackTriangleIso p (a i j) (g i) (h i j) (hY₂ i j) (hY i) hX
          (ha i j)).hom.app N =
      (frobeniusColimitPullbackTriangleIso p (b i j) (g j) (h i j) (hY₂ i j) (hY j) hX
          (hb i j)).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (b i j) (hY₂ i j) (hY j))).map (ψ j) ≫
        (frobeniusColimitPullbackTriangleIso p (b i j) (g j) (h i j) (hY₂ i j) (hY j) hX
          (hb i j)).hom.app N) :
    ∃! χ : M ⟶ N, ∀ i, (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).map χ = ψ i := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ∀ i, M.over (g i).opensRange ⟶ N.over (g i).opensRange,
      ∀ i, frobeniusColimitPullbackHomEquivOpenImmersion X p hX (g i) (hY i) M N (φ i) = ψ i :=
    ⟨fun i => (frobeniusColimitPullbackHomEquivOpenImmersion X p hX (g i) (hY i) M N).symm (ψ i),
      fun i => Equiv.apply_symm_apply _ _⟩
  refine existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion_of_overMap X p hX g hY
    hcov φ ψ hφ fun i j W hWi hWj => ?_
  obtain rfl : ψ = fun i => frobeniusColimitPullbackHomEquivOpenImmersion X p hX (g i) (hY i)
      M N (φ i) := funext fun i => (hφ i).symm
  exact frobeniusColimitPullbackHomEquivOpenImmersion_overMap_eq_of_triangle X p hX (g i) (g j)
    (h i j) (a i j) (b i j) (hY i) (hY j) (hY₂ i j) (ha i j) (hb i j)
    ((hrange i j).trans_le inf_le_left) ((hrange i j).trans_le inf_le_right)
    ((le_inf hWi hWj).trans_eq (hrange i j).symm) hWi hWj (φ i) (φ j) (hψ i j)

end AlgebraicGeometry
