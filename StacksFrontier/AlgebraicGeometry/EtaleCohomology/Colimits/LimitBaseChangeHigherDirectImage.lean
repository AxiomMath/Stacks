module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeCube
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitAssertion

/-!
# Base change for higher direct images passes to the limit

Let `I` be a directed set and consider an inverse system of cartesian diagrams of schemes

```
X_i  ←-h_i-  Y_i
|f_i         |e_i
S_i  ←-g_i-  T_i
```

with affine transition morphisms and with every `g_i` quasi-compact and quasi-separated, with
limit the cartesian square `X ← Y, S ← T` with morphisms `f, g, h, e`. Let `(ℱ_i, φ_{i'i})` be a
system of abelian sheaves on `(T_i)` as in [Stacks, Tag 0EZL] and let `ℱ = colim p_i^{-1}ℱ_i` on
`T`. [Stacks, Tag 0EZT] (2) asserts: if `f_i^{-1}R^q g_{i,*}ℱ_i = R^q h_{i,*}e_i^{-1}ℱ_i` for all
`i`, then `f^{-1}R^q g_*ℱ = R^q h_*e^{-1}ℱ`. This file proves it, by the source's argument.

* `e^{-1}ℱ = colim q_i^{-1}e_i^{-1}ℱ_i`, the inverse image along `e` of the presentation of `ℱ`
  (`Stacks.EtaleCohomology.LimitBaseChange.isPullbackColimitPresentation_inverseImageSystem`);
* `h_i` is quasi-compact and quasi-separated, as a base change of `g_i`;
* [Stacks, Tag 0EYM] twice: `R^q g_*ℱ = colim s_i^{-1}R^q g_{i,*}ℱ_i` and
  `R^q h_*e^{-1}ℱ = colim r_i^{-1}R^q h_{i,*}e_i^{-1}ℱ_i`
  (`Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_of_isLimit`);
* inverse image along `f` is a left adjoint, so it carries the first colimit to
  `f^{-1}R^q g_*ℱ = colim r_i^{-1}f_i^{-1}R^q g_{i,*}ℱ_i`;
* the base change map of the limit square is compatible with the base change maps of the levels
  and these with the diagram maps (`Colimits/LimitBaseChangeCube.lean`), so it is the colimit of
  the base change maps of the levels, which are isomorphisms.

## Main results

* `Stacks.EtaleCohomology.isIso_of_existsUnique_desc_of_leftAdjoint` — a map out of the image
  under a left adjoint of a colimit, compatible with a levelwise invertible map of diagrams into
  another colimit, is invertible (both colimits in universal-property form).
* `Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_of_isLimit` —
  **[Stacks, Tag 0EZT] (2).**

## Implementation notes

The colimits of [Stacks, Tag 0EYM] are in the universal-property form of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsHigherDirectImageColimit`, so the final step is
`Stacks.EtaleCohomology.isIso_of_existsUnique_desc_of_leftAdjoint` rather than the transfer of
invertibility between colimit cocones `Stacks.EtaleCohomology.LimitBaseChange.isIso_of_isColimit`
that `Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit` uses.

The limit morphisms are named morphisms with the equations characterising them, as in
`Stacks.EtaleCohomology.LimitBaseChange.isPullback_limitSquare`; the commutativity of the limit
square is `Stacks.EtaleCohomology.LimitBaseChange.limitSquare_comm`.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-- **A map compatible with a levelwise invertible map of colimit diagrams is invertible**, for
colimits in universal-property form and with the source the image under a left adjoint `L` of a
colimit. If the `ψM_i : M_i ⟶ MM` present `MM` as the colimit of a diagram with maps `dM`, the
`ψN_i : N_i ⟶ NN` present `NN` as the colimit of a diagram with maps `dN`, the `ψM_i` form a
cocone, and `β : L(MM) ⟶ NN` is compatible with isomorphisms `L(M_i) ≅ N_i` commuting with the
diagram maps, then `β` is an isomorphism. -/
theorem isIso_of_existsUnique_desc_of_leftAdjoint {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {J : Type*} [Category* J] {M : J → C} {N : J → D}
    {MM : C} {NN : D} (ψM : ∀ i, M i ⟶ MM) (ψN : ∀ i, N i ⟶ NN)
    (dM : ∀ ⦃i j : J⦄, (i ⟶ j) → (M j ⟶ M i)) (dN : ∀ ⦃i j : J⦄, (i ⟶ j) → (N j ⟶ N i))
    (hM : ∀ (Z : C) (τ : ∀ i, M i ⟶ Z), (∀ ⦃i j : J⦄ (a : i ⟶ j), dM a ≫ τ i = τ j) →
      ∃! χ : MM ⟶ Z, ∀ i, ψM i ≫ χ = τ i)
    (hN : ∀ (Z : D) (τ : ∀ i, N i ⟶ Z), (∀ ⦃i j : J⦄ (a : i ⟶ j), dN a ≫ τ i = τ j) →
      ∃! χ : NN ⟶ Z, ∀ i, ψN i ≫ χ = τ i)
    (hψM : ∀ ⦃i j : J⦄ (a : i ⟶ j), dM a ≫ ψM i = ψM j)
    (stage : ∀ i, L.obj (M i) ⟶ N i) (hstage : ∀ i, IsIso (stage i)) (β : L.obj MM ⟶ NN)
    (hcube : ∀ i, L.map (ψM i) ≫ β = stage i ≫ ψN i)
    (htrans : ∀ ⦃i j : J⦄ (a : i ⟶ j), L.map (dM a) ≫ stage i = stage j ≫ dN a) :
    IsIso β := by
  have := hstage
  have hdN : ∀ ⦃i j : J⦄ (a : i ⟶ j), dN a = inv (stage j) ≫ L.map (dM a) ≫ stage i := by
    intro i j a
    rw [htrans a, IsIso.inv_hom_id_assoc]
  have hψN : ∀ ⦃i j : J⦄ (a : i ⟶ j), dN a ≫ ψN i = ψN j := by
    intro i j a
    rw [hdN a, Category.assoc, Category.assoc, ← hcube i, ← L.map_comp_assoc, hψM a, hcube j,
      IsIso.inv_hom_id_assoc]
  let τ : ∀ i, N i ⟶ L.obj MM := fun i => inv (stage i) ≫ L.map (ψM i)
  have hτ : ∀ ⦃i j : J⦄ (a : i ⟶ j), dN a ≫ τ i = τ j := by
    intro i j a
    simp only [τ]
    rw [hdN a, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← L.map_comp, hψM a]
  obtain ⟨χ, hχ, -⟩ := hN _ τ hτ
  have h₁ : χ ≫ β = 𝟙 NN := by
    obtain ⟨_, _, hu⟩ := hN _ ψN hψN
    refine (hu _ fun i => ?_).trans (hu _ fun i => Category.comp_id _).symm
    rw [← Category.assoc, hχ i]
    simp only [τ, Category.assoc, hcube i, IsIso.inv_hom_id_assoc]
  have h₂ : β ≫ χ = 𝟙 (L.obj MM) := by
    apply (adj.homEquiv _ _).injective
    obtain ⟨_, _, hu⟩ := hM _ (fun i => ψM i ≫ adj.homEquiv _ _ (𝟙 (L.obj MM)))
      (fun i j a => by rw [← Category.assoc, hψM a])
    refine (hu _ fun i => ?_).trans (hu _ fun i => rfl).symm
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
    congr 1
    rw [reassoc_of% hcube i, hχ i]
    simp only [τ, IsIso.hom_inv_id_assoc, Category.comp_id]
  exact ⟨χ, h₂, h₁⟩

/-- `Stacks.EtaleCohomology.isIso_of_existsUnique_desc_of_leftAdjoint` with the target diagram
written through functors: its objects are `R_i(G_i(F_i(A_i)))` and its colimit is `G(F(A))`, while
the comparisons `L(M_i) ⟶ R_i((F_i ⋙ G_i)(A_i))` and the map `β : L(MM) ⟶ (F ⋙ G)(A)` are
written with the composite functors. The comparison is given as a composite `κ_i ≫ m_i`. -/
theorem isIso_of_existsUnique_desc_of_leftAdjoint_comp.{v₀, v₁, v₂, v₃, v₄, v₅, v₆, u₀, u₁,
    u₂, u₃, u₄, u₅, u₆, w}
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {J : Type w} [Category.{w} J] {M : J → C} {MM : C}
    {W : J → Type u₂} [∀ i, Category.{v₂} (W i)] {Y : J → Type u₃} [∀ i, Category.{v₃} (Y i)]
    {Z : J → Type u₄} [∀ i, Category.{v₄} (Z i)]
    (Fi : ∀ i, W i ⥤ Y i) (Gi : ∀ i, Y i ⥤ Z i) (Ri : ∀ i, Z i ⥤ D) (Ai : ∀ i, W i)
    {W' : Type u₅} [Category.{v₅} W'] {Y' : Type u₆} [Category.{v₆} Y'] (Fe : W' ⥤ Y')
    (Ge : Y' ⥤ D) (A : W')
    (ψM : ∀ i, M i ⟶ MM) (ψN : ∀ i, (Ri i).obj ((Gi i).obj ((Fi i).obj (Ai i))) ⟶ Ge.obj (Fe.obj A))
    (dM : ∀ ⦃i j : J⦄, (i ⟶ j) → (M j ⟶ M i))
    (dN : ∀ ⦃i j : J⦄, (i ⟶ j) →
      ((Ri j).obj ((Gi j).obj ((Fi j).obj (Ai j))) ⟶ (Ri i).obj ((Gi i).obj ((Fi i).obj (Ai i)))))
    (hM : ∀ (Q : C) (τ : ∀ i, M i ⟶ Q), (∀ ⦃i j : J⦄ (a : i ⟶ j), dM a ≫ τ i = τ j) →
      ∃! χ : MM ⟶ Q, ∀ i, ψM i ≫ χ = τ i)
    (hN : ∀ (Q : D) (τ : ∀ i, (Ri i).obj ((Gi i).obj ((Fi i).obj (Ai i))) ⟶ Q),
      (∀ ⦃i j : J⦄ (a : i ⟶ j), dN a ≫ τ i = τ j) →
      ∃! χ : Ge.obj (Fe.obj A) ⟶ Q, ∀ i, ψN i ≫ χ = τ i)
    (hψM : ∀ ⦃i j : J⦄ (a : i ⟶ j), dM a ≫ ψM i = ψM j)
    {P : J → D} (κ : ∀ i, L.obj (M i) ⟶ P i)
    (m : ∀ i, P i ⟶ (Ri i).obj ((Fi i ⋙ Gi i).obj (Ai i)))
    (hstage : ∀ i, IsIso (κ i ≫ m i)) (β : L.obj MM ⟶ (Fe ⋙ Ge).obj A)
    (hcube : ∀ i, L.map (ψM i) ≫ β = κ i ≫ m i ≫ ψN i)
    (htrans : ∀ ⦃i j : J⦄ (a : i ⟶ j), L.map (dM a) ≫ κ i ≫ m i = (κ j ≫ m j) ≫ dN a) :
    IsIso β :=
  isIso_of_existsUnique_desc_of_leftAdjoint adj ψM ψN dM dN hM hN hψM (fun i => κ i ≫ m i)
    hstage β (fun i => (hcube i).trans (Category.assoc _ _ _).symm) htrans

/-! ### The comparisons of the squares at the limit -/

/-- The comparison of the two composite inverse images of a commutative square is natural, written
with the components of the isomorphism. -/
theorem smallEtalePullbackAbSquareIso_app_naturality {X' X Y' Y : Scheme.{u}} (f' : X' ⟶ Y')
    (e' : X' ⟶ X) (e : Y' ⟶ Y) (f : X ⟶ Y) (P : X' ⟶ Y) (h₁ : P = f' ≫ e) (h₂ : P = e' ≫ f)
    {A A' : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : A ⟶ A') :
    (smallEtalePullbackAb f').map ((smallEtalePullbackAb e).map φ) ≫
        ((smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).app A').hom =
      ((smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).app A).hom ≫
        (smallEtalePullbackAb e').map ((smallEtalePullbackAb f).map φ) :=
  (smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).hom.naturality φ

/-- `Stacks.EtaleCohomology.smallEtalePullbackAbSquareIso_vcomp` with the comparison along the
second composite moved to the other side, and the two comparisons of inverse images along the
composites given as maps equal to them. -/
theorem smallEtalePullbackAbSquareIso_vcomp_app {X' Y' X Y X₀ Y₀ : Scheme.{u}}
    (f' : X' ⟶ Y') (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀)
    (e'₁ : X' ⟶ X) (e'₂ : X ⟶ X₀) (e'₁₂ : X' ⟶ X₀) (hE' : e'₁₂ = e'₁ ≫ e'₂)
    (e₁ : Y' ⟶ Y) (e₂ : Y ⟶ Y₀) (e₁₂ : Y' ⟶ Y₀) (hE : e₁₂ = e₁ ≫ e₂)
    (PU : X' ⟶ Y) (hPU : PU = f' ≫ e₁) (hPU' : PU = e'₁ ≫ f)
    (PW : X ⟶ Y₀) (hPW : PW = f ≫ e₂) (hPW' : PW = e'₂ ≫ f₀)
    (P : X' ⟶ Y₀) (hP : P = f' ≫ e₁₂) (hP' : P = e'₁₂ ≫ f₀)
    (A : Sheaf (smallEtaleTopology Y₀) Ab.{u + 1})
    (c : (smallEtalePullbackAb e₁₂).obj A ⟶
      (smallEtalePullbackAb e₂ ⋙ smallEtalePullbackAb e₁).obj A)
    (hc : c = (smallEtalePullbackAbComp' e₁ e₂ e₁₂ hE).inv.app A)
    (c' : (smallEtalePullbackAb e'₁₂).obj ((smallEtalePullbackAb f₀).obj A) ⟶
      (smallEtalePullbackAb e'₂ ⋙ smallEtalePullbackAb e'₁).obj ((smallEtalePullbackAb f₀).obj A))
    (hc' : c' = (smallEtalePullbackAbComp' e'₁ e'₂ e'₁₂ hE').inv.app
      ((smallEtalePullbackAb f₀).obj A)) :
    (smallEtalePullbackAb f').map c ≫
        ((smallEtalePullbackAbSquareIso f' e'₁ e₁ f PU hPU hPU').app
          ((smallEtalePullbackAb e₂).obj A)).hom ≫
        (smallEtalePullbackAb e'₁).map
          (((smallEtalePullbackAbSquareIso f e'₂ e₂ f₀ PW hPW hPW').app A).hom) =
      ((smallEtalePullbackAbSquareIso f' e'₁₂ e₁₂ f₀ P hP hP').app A).hom ≫ c' := by
  subst hc hc'
  rw [Iso.app_hom, Iso.app_hom, Iso.app_hom, ← smallEtalePullbackAbSquareIso_vcomp f' f f₀ e'₁ e'₂
    e'₁₂ hE' e₁ e₂ e₁₂ hE PU hPU hPU' PW hPW hPW' P hP hP' A]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

namespace LimitBaseChange

open LimitHigherDirectImage

/-- The rearrangement behind `stageMap_transition`, in an abstract category. -/
theorem stageMap_transition_algebra {C : Type*} [Category* C]
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ : C} {d : o₀ ⟶ o₂} {c : o₀ ⟶ o₁} {l : o₁ ⟶ o₂}
    {κ : o₂ ⟶ o₃} {m : o₃ ⟶ o₄} {κ' : o₁ ⟶ o₅} {r : o₅ ⟶ o₃} {rκ : o₅ ⟶ o₆} {rM : o₆ ⟶ o₇}
    {rψ : o₇ ⟶ o₄} {κj : o₀ ⟶ o₈} {mj : o₈ ⟶ o₉} {cX : o₉ ⟶ o₇} {cX' : o₈ ⟶ o₆}
    {dX : o₉ ⟶ o₄}
    (h₁ : d = c ≫ l) (h₂ : l ≫ κ = κ' ≫ r) (h₃ : r ≫ m = rκ ≫ rM ≫ rψ)
    (h₄ : c ≫ κ' ≫ rκ = κj ≫ cX') (h₅ : mj ≫ cX = cX' ≫ rM) (h₆ : dX = cX ≫ rψ) :
    d ≫ κ ≫ m = (κj ≫ mj) ≫ dX := by
  rw [h₁, h₆]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, h₃, reassoc_of% h₄, reassoc_of% h₅]

variable {I : Type v} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i) (q : ℕ)
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
  (fL : cX.pt ⟶ cS.pt) (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)

/-- The inverse image along `f` of a diagram map of the first colimit diagram, split into the
comparison of inverse images and the transition map. -/
private theorem map_diagramMap_eq (F : EtaleSheafSystem DT Ab.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    (smallEtalePullbackAb fL).map ((conePullbackComp cS a).inv.app
        (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j)) ≫
      (smallEtalePullbackAb (cS.π.app i)).map (transitionMap g q F a)) =
    (smallEtalePullbackAb fL).map ((conePullbackComp cS a).inv.app
        (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j))) ≫
      (smallEtalePullbackAb fL).map
        ((smallEtalePullbackAb (cS.π.app i)).map (transitionMap g q F a)) :=
  (smallEtalePullbackAb fL).map_comp _ _

/-- The compatibility of the base change maps of the levels with the transition maps, pulled back
to the limit along the projection `r_i`. -/
private theorem map_transitionMap_comp_higherBaseChangeMapAb (F : EtaleSheafSystem DT Ab.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (cX.π.app i)).map
        ((smallEtalePullbackAb (f.app i)).map (transitionMap g q F a)) ≫
      (smallEtalePullbackAb (cX.π.app i)).map
        ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i)) =
    (smallEtalePullbackAb (cX.π.app i)).map
        (((smallEtalePullbackAbSquareIso (f.app i) (DX.map a) (DS.map a) (f.app j)
          (f.app i ≫ DS.map a) rfl (f.naturality a).symm).app
          (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j))).hom) ≫
      (smallEtalePullbackAb (cX.π.app i)).map ((smallEtalePullbackAb (DX.map a)).map
        ((higherBaseChangeMapAb (f.app j) (g.app j) (h.app j) (e.app j) (w j) q).app (F.obj j))) ≫
      (smallEtalePullbackAb (cX.π.app i)).map (transitionMap h q (inverseImageSystem e F) a) :=
  (((smallEtalePullbackAb (cX.π.app i)).map_comp _ _).symm.trans
    (congrArg (smallEtalePullbackAb (cX.π.app i)).map
      (transitionMap_comp_higherBaseChangeMapAb f g h e w q F a))).trans
    (((smallEtalePullbackAb (cX.π.app i)).map_comp _ _).trans
      (congrArg (fun z => _ ≫ z) ((smallEtalePullbackAb (cX.π.app i)).map_comp _ _)))

/-- The comparison of inverse images along a factorisation of a projection of a cone is natural,
at the base change map of a level. -/
private theorem higherBaseChangeMapAb_conePullbackComp (F : EtaleSheafSystem DT Ab.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (cX.π.app j)).map
        ((higherBaseChangeMapAb (f.app j) (g.app j) (h.app j) (e.app j) (w j) q).app (F.obj j)) ≫
      (conePullbackComp cX a).inv.app
        (((smallEtalePushforwardAb (h.app j)).rightDerived q).obj
          ((inverseImageSystem e F).obj j)) =
    (conePullbackComp cX a).inv.app ((smallEtalePullbackAb (f.app j)).obj
        (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j))) ≫
      (smallEtalePullbackAb (cX.π.app i)).map ((smallEtalePullbackAb (DX.map a)).map
        ((higherBaseChangeMapAb (f.app j) (g.app j) (h.app j) (e.app j) (w j) q).app (F.obj j))) :=
  (conePullbackComp cX a).inv.naturality
    ((higherBaseChangeMapAb (f.app j) (g.app j) (h.app j) (e.app j) (w j) q).app (F.obj j))

/-- **The comparisons of the levels, pulled back to the limit, commute with the diagram maps** of
the two colimit diagrams of [Stacks, Tag 0EYM]: the inverse image along `f` of the diagram of the
`s_i^{-1}R^q g_{i,*}ℱ_i` and the diagram of the `r_i^{-1}R^q h_{i,*}e_i^{-1}ℱ_i`. The comparison
at `i` is the comparison `f^{-1}s_i^{-1} ≅ r_i^{-1}f_i^{-1}` followed by `r_i^{-1}` of the base
change map of the `i`-th square. -/
theorem stageMap_transition (F : EtaleSheafSystem DT Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb fL).map ((conePullbackComp cS a).inv.app
        (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j)) ≫
      (smallEtalePullbackAb (cS.π.app i)).map (transitionMap g q F a)) ≫
      ((smallEtalePullbackAbSquareIso (X' := cX.pt) fL (cX.π.app i) (cS.π.app i) (f.app i)
          (fL ≫ cS.π.app i) rfl (hfL i)).app
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).hom ≫
      (smallEtalePullbackAb (cX.π.app i)).map
        ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i)) =
    (((smallEtalePullbackAbSquareIso (X' := cX.pt) fL (cX.π.app j) (cS.π.app j) (f.app j)
          (fL ≫ cS.π.app j) rfl (hfL j)).app
          (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j))).hom ≫
      (smallEtalePullbackAb (cX.π.app j)).map
        ((higherBaseChangeMapAb (f.app j) (g.app j) (h.app j) (e.app j) (w j) q).app (F.obj j))) ≫
    ((conePullbackComp cX a).inv.app
        (((smallEtalePushforwardAb (h.app j)).rightDerived q).obj
          ((inverseImageSystem e F).obj j)) ≫
      (smallEtalePullbackAb (cX.π.app i)).map (transitionMap h q (inverseImageSystem e F) a)) :=
  stageMap_transition_algebra (map_diagramMap_eq g q fL F a)
    (smallEtalePullbackAbSquareIso_app_naturality (X' := cX.pt) fL (cX.π.app i) (cS.π.app i)
      (f.app i) (fL ≫ cS.π.app i) rfl (hfL i) (transitionMap g q F a))
    (map_transitionMap_comp_higherBaseChangeMapAb f g h e w q F a)
    (smallEtalePullbackAbSquareIso_vcomp_app (X' := cX.pt) (Y' := cS.pt) fL (f.app i) (f.app j)
      (cX.π.app i) (DX.map a) (cX.π.app j) (cX.w a).symm (cS.π.app i) (DS.map a) (cS.π.app j)
      (cS.w a).symm (fL ≫ cS.π.app i) rfl (hfL i) (f.app i ≫ DS.map a) rfl (f.naturality a).symm
      (fL ≫ cS.π.app j) rfl (hfL j) (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj
        (F.obj j)) _ (congrArg (fun z => z.inv.app
          (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j)))
        (conePullbackComp_eq cS a)) _ (congrArg (fun z => z.inv.app
          ((smallEtalePullbackAb (f.app j)).obj
            (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j))))
        (conePullbackComp_eq cX a)))
    (higherBaseChangeMapAb_conePullbackComp f g h e w q F a) rfl

section Main

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}} (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX)
  (e : DY ⟶ DT)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (g.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (g.app i)]
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
  (fL : cX.pt ⟶ cS.pt) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt) (eL : cY.pt ⟶ cT.pt)

/-- **[Stacks, Tag 0EZT] (2): base change for the higher direct images passes to the limit.**
Let `I` be a directed set and let `(X_i ← Y_i, S_i ← T_i)` be an inverse system over `I` of
cartesian squares of schemes `h_i ≫ f_i = e_i ≫ g_i`, with affine transition morphisms and with
every `g_i` quasi-compact and quasi-separated. Let `X, S, T, Y` be the limits, with the limit
morphisms `f, g, h, e` characterised by `f ≫ s_i = r_i ≫ f_i`, `g ≫ s_i = p_i ≫ g_i`,
`h ≫ r_i = q_i ≫ h_i` and `e ≫ p_i = q_i ≫ e_i`. Let `(ℱ_i, φ_{i'i})` be a system of abelian
sheaves on `(T_i)` (Stacks 0EZL) and let `ℱ = colim p_i^{-1}ℱ_i` on `T`, presented by legs
`ι_i : p_i^{-1}ℱ_i ⟶ ℱ`. If for every `i` the base change map
`f_i^{-1}R^q g_{i,*}ℱ_i ⟶ R^q h_{i,*}e_i^{-1}ℱ_i` is an isomorphism, then so is the base change
map `f^{-1}R^q g_*ℱ ⟶ R^q h_*e^{-1}ℱ` of the limit square. -/
@[stacks 0EZT "conclusion (2), at the source's hypotheses: for an inverse system over a directed \
set of cartesian squares of schemes with affine transition morphisms and quasi-compact \
quasi-separated `g_i`, with limit square `(f, g, h, e)`, and a system of abelian sheaves `ℱ_i` on \
the `T_i` with `ℱ = colim p_i^{-1}ℱ_i`, if every base change map \
`f_i^{-1}R^q g_{i,*}ℱ_i ⟶ R^q h_{i,*}e_i^{-1}ℱ_i` is an isomorphism then so is \
`f^{-1}R^q g_*ℱ ⟶ R^q h_*e^{-1}ℱ`. Together with \
`Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_of_isLimit`, \
conclusion (1), this covers the tag."]
theorem isIso_higherBaseChangeMapAb_of_isLimit
    (hsq : ∀ i : Iᵒᵖ, IsPullback (h.app i) (e.app i) (f.app i) (g.app i))
    (hcX : IsLimit cX) (hcS : IsLimit cS) (hcT : IsLimit cT) (hcY : IsLimit cY)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hgL : ∀ i : Iᵒᵖ, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i) (q : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (F : EtaleSheafSystem DT Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp cT a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (cT.π.app i)).map (F.map a) ≫ ι i = ι j)
    (hpres : IsPullbackColimitPresentation cT 𝓕 F ι)
    (hstage : ∀ i : Iᵒᵖ,
      IsIso ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (hsq i).w q).app
        (F.obj i))) :
    IsIso ((higherBaseChangeMapAb fL gL hL eL
      (limitSquare_comm f g h e cX cS cT cY fL gL hL eL hcS hfL hgL hhL heL fun i => (hsq i).w)
      q).app 𝓕) := by
  obtain rfl : gL = limitMorphism g cT cS hcS :=
    hcS.hom_ext fun i => (hgL i).trans (limitMorphism_comp_π g cT cS hcS i).symm
  obtain rfl : hL = limitMorphism h cY cX hcX :=
    hcX.hom_ext fun i => (hhL i).trans (limitMorphism_comp_π h cY cX hcX i).symm
  have : ∀ i : Iᵒᵖ, QuasiCompact (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hsq i).flip inferInstance
  have : ∀ i : Iᵒᵖ, QuasiSeparated (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (hsq i).flip inferInstance
  have hg := isHigherDirectImageColimit_of_isLimit.{u, u} g hcT cS hcS q 𝓕 F ι hι hpres
  have hh := isHigherDirectImageColimit_of_isLimit.{u, u} h hcY cX hcX q
    ((smallEtalePullbackAb eL).obj 𝓕) (inverseImageSystem e F)
    (inverseImageSystemLeg e eL heL 𝓕 F ι)
    (fun a => inverseImageSystemLeg_compatible e eL heL 𝓕 F ι a (hι a))
    (isPullbackColimitPresentation_inverseImageSystem e eL heL 𝓕 F ι hpres)
  have hstage' : ∀ i : Iᵒᵖ, IsIso
      (((smallEtalePullbackAbSquareIso (X' := cX.pt) fL (cX.π.app i) (cS.π.app i) (f.app i)
          (fL ≫ cS.π.app i) rfl (hfL i)).app
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).hom ≫
        (smallEtalePullbackAb (cX.π.app i)).map
          ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (hsq i).w q).app
            (F.obj i))) := fun i => by
    have := hstage i
    infer_instance
  exact isIso_of_existsUnique_desc_of_leftAdjoint_comp (smallEtaleAdjunctionAb fL)
    (fun i => smallEtalePullbackAb (e.app i))
    (fun i => (smallEtalePushforwardAb (h.app i)).rightDerived q)
    (fun i => smallEtalePullbackAb (cX.π.app i)) (fun i => F.obj i)
    (smallEtalePullbackAb eL) ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q)
    𝓕
    (projectionMap g cT cS hcS q 𝓕 F ι)
    (projectionMap h cY cX hcX q ((smallEtalePullbackAb eL).obj 𝓕) (inverseImageSystem e F)
      (inverseImageSystemLeg e eL heL 𝓕 F ι))
    (fun i j a => (conePullbackComp cS a).inv.app
        (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j)) ≫
      (smallEtalePullbackAb (cS.π.app i)).map (transitionMap g q F a))
    (fun i j a => (conePullbackComp cX a).inv.app
        (((smallEtalePushforwardAb (h.app j)).rightDerived q).obj
          ((inverseImageSystem e F).obj j)) ≫
      (smallEtalePullbackAb (cX.π.app i)).map (transitionMap h q (inverseImageSystem e F) a))
    (fun Z τ hτ => hg Z τ fun a => (Category.assoc _ _ _).symm.trans (hτ a))
    (fun Z τ hτ => hh Z τ fun a => (Category.assoc _ _ _).symm.trans (hτ a))
    (fun i j a => (Category.assoc _ _ _).trans (projectionMap_cocone g q cT cS hcS 𝓕 F ι a
      (by rw [← hι a, Iso.hom_inv_id_app_assoc])))
    (fun i => ((smallEtalePullbackAbSquareIso (X' := cX.pt) fL (cX.π.app i) (cS.π.app i)
        (f.app i) (fL ≫ cS.π.app i) rfl (hfL i)).app
        (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).hom)
    (fun i => (smallEtalePullbackAb (cX.π.app i)).map
        ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (hsq i).w q).app
          (F.obj i)))
    hstage' _
    (fun i => projectionMap_comp_higherBaseChangeMapAb f g h e (fun i => (hsq i).w) q hcS hcX
      fL eL hfL heL _ 𝓕 F ι i)
    (fun i j a => stageMap_transition f g h e (fun i => (hsq i).w) q fL hfL F a)

end Main

end LimitBaseChange

end Stacks.EtaleCohomology

end
