module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethCompositeCoherence

/-!
# The relative Künneth map as a chain of three comparisons, with a map in the second factor

Let `a : X ⟶ S`, `b : Y ⟶ S`, `p : W ⟶ X`, `q : W ⟶ Y` be morphisms of ringed spaces with
`q ≫ b = p ≫ a`.  The relative Künneth map of [Stacks, Tag 0FLP]

`Ra_*K ⊗^𝐋 Rb_*M ⟶ R(p ≫ a)_*(Lp^*K ⊗^𝐋 Lq^*M)`

is the composite of the projection formula of [Stacks, Tag 08EU] at `a`, of the base-change
comparison `La^*Rb_*M ⟶ Rp_*Lq^*M` in the second factor and of the interchanged-order
projection formula at `p` (the factorization the first proof of [Stacks, Tag 0FLQ] uses, proved
in `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` as an
invertibility statement).  This file records that factorization as an *equation*, and its
version after a map `c : Lq^*M ⟶ Q'` is applied in the second factor of the target: then `c`
is absorbed into the base-change leg, which becomes `La^*Rb_*M ⟶ Rp_*Lq^*M ⟶ Rp_*Q'`.

That is what the Künneth formula of [Stacks, Tag 0FU4] needs when `X` and `Y` are not Tor
independent over `S`: the base-change leg is then not invertible, but the leg followed by the
derived-to-ordinary comparison `Lq^*𝒢 ⟶ q^*𝒢` is, for `𝒢` flat over `S`.

## Main results

* `AlgebraicGeometry.FlatKunneth.homEquiv_bitensor_comp_tensorMap_eq` and
  `AlgebraicGeometry.FlatKunneth.isIso_homEquiv_bitensor_comp_tensorMap`: the equation and the
  invertibility criterion over abstract adjunctions.
* `AlgebraicGeometry.FlatKunneth.kunnethMap_eq_chain`: the relative Künneth map is the chain of
  the three comparisons.
* `AlgebraicGeometry.FlatKunneth.isIso_kunnethMap_comp_tensorMap`: the relative Künneth map
  followed by `R(p ≫ a)_*` of a map in the second factor is invertible as soon as the projection
  formula at `a`, the base-change leg followed by that map, and the projection formula at `p` are.
* `AlgebraicGeometry.FlatKunneth.isIso_comp_map_bifunctor_comp`,
  `AlgebraicGeometry.FlatKunneth.isIso_comp_natIso_map`: the reassociations that insert a
  derived-to-ordinary comparison and the Leray isomorphism into the global Künneth map.

## References

* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedKunneth (adjunctionTensorMapRight kunnethMap kunnethBaseChangeLeg
  homEquiv_comp_bitensor_eq pullbackCounitLeg pullbackCounitLegComp)
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.FlatKunneth

section Abstract

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- **The interchanged-order projection-formula map is natural in its second variable.** -/
theorem adjunctionTensorMapRight_naturality_right {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) {G G' : D}
    (c : G ⟶ G') :
    adjunctionTensorMapRight adj A B α H G ≫ R.map (B.map (𝟙 (L.obj H) ×ₘ c)) =
      A.map (𝟙 H ×ₘ R.map c) ≫ adjunctionTensorMapRight adj A B α H G' := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adjunctionTensorMapRight, adjunctionTensorMapRight,
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm]
  simp only [Equiv.symm_apply_apply]
  have hα := α.naturality (𝟙 H ×ₘ R.map c)
  simp only [Functor.comp_map, Functor.prod_map] at hα
  rw [← Category.assoc, hα, Category.assoc, Category.assoc, ← B.map_comp, ← B.map_comp]
  congr 2
  exact CategoryTheory.Prod.hom_ext (by simp) (by simp)

variable {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}

/-- **The Künneth transpose along a composite is the chain of three comparisons**, as an
equation: the projection-formula map of `adj₁`, the transpose of `gM` in the second factor, and
the interchanged-order projection-formula map of `adj₂`, followed by `cR`.  This is the equation
behind `Stacks.Cohomology.DerivedKunneth.isIso_homEquiv_bitensor_comp`. -/
theorem homEquiv_bitensor_comp_eq_chain (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {Lf : C ⥤ E} {Rf : E ⥤ C} (adjf : Lf ⊣ Rf)
    (cL : L₁ ⋙ L₂ ≅ Lf) (cR : R₂ ⋙ R₁ ≅ Rf)
    (hcompat : ∀ (Z : C) (T : E) (φ : Lf.obj Z ⟶ T),
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (cL.hom.app Z ≫ φ)) ≫ cR.hom.app T =
        adjf.homEquiv Z T φ)
    (TA : C × C ⥤ C) (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (α₁ : TA ⋙ L₁ ⟶ L₁.prod L₁ ⋙ TD) (α₂ : TD ⋙ L₂ ⟶ L₂.prod L₂ ⋙ TE)
    (K : D) (N : C) (Q : E)
    (αf : Lf.obj (TA.obj (R₁.obj K, N)) ⟶ TE.obj (Lf.obj (R₁.obj K), Lf.obj N))
    (gM : Lf.obj N ⟶ Q) (bK : Lf.obj (R₁.obj K) ⟶ L₂.obj K)
    (hbK : bK = cL.inv.app (R₁.obj K) ≫ L₂.map (adj₁.counit.app K))
    (hαf : (cL.hom.app (TA.obj (R₁.obj K, N)) ≫ αf) ≫
        TE.map (cL.inv.app (R₁.obj K) ×ₘ cL.inv.app N) =
      L₂.map (α₁.app (R₁.obj K, N)) ≫ α₂.app (L₁.obj (R₁.obj K), L₁.obj N)) :
    adjf.homEquiv _ _ (αf ≫ TE.map (bK ×ₘ gM)) =
      CategoryTheory.adjunctionTensorMap adj₁ TA TD α₁ K N ≫
        R₁.map (TD.map (𝟙 K ×ₘ adj₂.homEquiv _ _ (cL.hom.app N ≫ gM))) ≫
          R₁.map (adjunctionTensorMapRight adj₂ TD TE α₂ K Q) ≫ cR.hom.app _ := by
  have hin : cL.hom.app (TA.obj (R₁.obj K, N)) ≫ αf ≫ TE.map (bK ×ₘ gM) =
      L₂.map (α₁.app (R₁.obj K, N)) ≫
        α₂.app (L₁.obj (R₁.obj K), L₁.obj N) ≫
          TE.map (L₂.map (adj₁.counit.app K) ×ₘ (cL.hom.app N ≫ gM)) := by
    have hs : (bK ×ₘ gM) =
        (cL.inv.app (R₁.obj K) ×ₘ cL.inv.app N) ≫
          (L₂.map (adj₁.counit.app K) ×ₘ (cL.hom.app N ≫ gM)) :=
      CategoryTheory.Prod.hom_ext (by simpa using hbK)
        (by simp only [CategoryTheory.prod_comp]; simp)
    rw [hs, Functor.map_comp]
    simp only [← Category.assoc]
    rw [hαf]
  rw [← hcompat, hin, homEquiv_comp_bitensor_eq]
  simp only [Category.assoc]

/-- `homEquiv_bitensor_comp_eq_chain` followed by `Rf` of a map in the second factor: the map is
absorbed into the transpose of the second leg, by naturality of the interchanged-order
projection-formula map and of `cR`. -/
theorem homEquiv_bitensor_comp_tensorMap_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {Lf : C ⥤ E} {Rf : E ⥤ C} (adjf : Lf ⊣ Rf)
    (cL : L₁ ⋙ L₂ ≅ Lf) (cR : R₂ ⋙ R₁ ≅ Rf)
    (hcompat : ∀ (Z : C) (T : E) (φ : Lf.obj Z ⟶ T),
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (cL.hom.app Z ≫ φ)) ≫ cR.hom.app T =
        adjf.homEquiv Z T φ)
    (TA : C × C ⥤ C) (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (α₁ : TA ⋙ L₁ ⟶ L₁.prod L₁ ⋙ TD) (α₂ : TD ⋙ L₂ ⟶ L₂.prod L₂ ⋙ TE)
    (K : D) (N : C) (Q : E)
    (αf : Lf.obj (TA.obj (R₁.obj K, N)) ⟶ TE.obj (Lf.obj (R₁.obj K), Lf.obj N))
    (gM : Lf.obj N ⟶ Q) (bK : Lf.obj (R₁.obj K) ⟶ L₂.obj K)
    (hbK : bK = cL.inv.app (R₁.obj K) ≫ L₂.map (adj₁.counit.app K))
    (hαf : (cL.hom.app (TA.obj (R₁.obj K, N)) ≫ αf) ≫
        TE.map (cL.inv.app (R₁.obj K) ×ₘ cL.inv.app N) =
      L₂.map (α₁.app (R₁.obj K, N)) ≫ α₂.app (L₁.obj (R₁.obj K), L₁.obj N))
    {Q' : E} (cq : Q ⟶ Q') :
    adjf.homEquiv _ _ (αf ≫ TE.map (bK ×ₘ gM)) ≫ Rf.map (TE.map (𝟙 (L₂.obj K) ×ₘ cq)) =
      CategoryTheory.adjunctionTensorMap adj₁ TA TD α₁ K N ≫
        R₁.map (TD.map (𝟙 K ×ₘ (adj₂.homEquiv _ _ (cL.hom.app N ≫ gM) ≫ R₂.map cq))) ≫
          R₁.map (adjunctionTensorMapRight adj₂ TD TE α₂ K Q') ≫ cR.hom.app _ := by
  rw [homEquiv_bitensor_comp_eq_chain adj₁ adj₂ adjf cL cR hcompat TA TD TE α₁ α₂ K N Q αf gM bK
    hbK hαf]
  simp only [Category.assoc]
  rw [← cR.hom.naturality, Functor.comp_map, ← Functor.map_comp_assoc R₁ _ (R₂.map _),
    adjunctionTensorMapRight_naturality_right]
  have hprod : TD.map (𝟙 K ×ₘ adj₂.homEquiv _ _ (cL.hom.app N ≫ gM)) ≫ TD.map (𝟙 K ×ₘ R₂.map cq) =
      TD.map (𝟙 K ×ₘ (adj₂.homEquiv _ _ (cL.hom.app N ≫ gM) ≫ R₂.map cq)) := by
    rw [← TD.map_comp, CategoryTheory.prod_comp, Category.id_comp]
  rw [← hprod]
  simp only [Functor.map_comp, Category.assoc]

/-- The composite of `homEquiv_bitensor_comp_tensorMap_eq` is invertible as soon as its three
factors are. -/
theorem isIso_homEquiv_bitensor_comp_tensorMap (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {Lf : C ⥤ E} {Rf : E ⥤ C} (adjf : Lf ⊣ Rf)
    (cL : L₁ ⋙ L₂ ≅ Lf) (cR : R₂ ⋙ R₁ ≅ Rf)
    (hcompat : ∀ (Z : C) (T : E) (φ : Lf.obj Z ⟶ T),
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (cL.hom.app Z ≫ φ)) ≫ cR.hom.app T =
        adjf.homEquiv Z T φ)
    (TA : C × C ⥤ C) (TD : D × D ⥤ D) (TE : E × E ⥤ E)
    (α₁ : TA ⋙ L₁ ⟶ L₁.prod L₁ ⋙ TD) (α₂ : TD ⋙ L₂ ⟶ L₂.prod L₂ ⋙ TE)
    (K : D) (N : C) (Q : E)
    (αf : Lf.obj (TA.obj (R₁.obj K, N)) ⟶ TE.obj (Lf.obj (R₁.obj K), Lf.obj N))
    (gM : Lf.obj N ⟶ Q) (bK : Lf.obj (R₁.obj K) ⟶ L₂.obj K)
    (hbK : bK = cL.inv.app (R₁.obj K) ≫ L₂.map (adj₁.counit.app K))
    (hαf : (cL.hom.app (TA.obj (R₁.obj K, N)) ≫ αf) ≫
        TE.map (cL.inv.app (R₁.obj K) ×ₘ cL.inv.app N) =
      L₂.map (α₁.app (R₁.obj K, N)) ≫ α₂.app (L₁.obj (R₁.obj K), L₁.obj N))
    {Q' : E} (cq : Q ⟶ Q')
    (hone : IsIso (CategoryTheory.adjunctionTensorMap adj₁ TA TD α₁ K N))
    (htwo : IsIso (adj₂.homEquiv _ _ (cL.hom.app N ≫ gM) ≫ R₂.map cq))
    (hthree : IsIso (adjunctionTensorMapRight adj₂ TD TE α₂ K Q')) :
    IsIso (adjf.homEquiv _ _ (αf ≫ TE.map (bK ×ₘ gM)) ≫ Rf.map (TE.map (𝟙 (L₂.obj K) ×ₘ cq))) := by
  rw [homEquiv_bitensor_comp_tensorMap_eq adj₁ adj₂ adjf cL cR hcompat TA TD TE α₁ α₂ K N Q αf
    gM bK hbK hαf cq]
  have h₄ : IsIso (𝟙 K ×ₘ (adj₂.homEquiv _ _ (cL.hom.app N ≫ gM) ≫ R₂.map cq)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, htwo⟩
  infer_instance

/-- A triple composite is invertible as soon as its first two factors compose to an isomorphism
and the third is one. -/
theorem isIso_comp_assoc_of {X₀ X₁ X₂ X₃ : E} (x : X₀ ⟶ X₁) (y : X₁ ⟶ X₂) (z : X₂ ⟶ X₃)
    (hxy : IsIso (x ≫ y)) (hz : IsIso z) : IsIso (x ≫ y ≫ z) := by
  rw [← Category.assoc]
  infer_instance

/-- Invertibility of `x ≫ R(y)` transported along `x = x'` and a factorization `y = y₁ ≫ y₂`
with `y₂` invertible. -/
theorem isIso_comp_map_of_eq {B : Type u₂} [Category.{v₂} B] (R : E ⥤ B) {b : B} {T T₁ T₂ : E}
    {x x' : b ⟶ R.obj T} {y : T ⟶ T₂} (y₁ : T ⟶ T₁) (y₂ : T₁ ⟶ T₂) (hx : x = x')
    (hy : y = y₁ ≫ y₂) (h : IsIso (x' ≫ R.map y₁)) (h₂ : IsIso y₂) : IsIso (x ≫ R.map y) := by
  subst hx hy
  rw [Functor.map_comp, ← Category.assoc]
  infer_instance

/-- **Reordering the derived-to-ordinary comparison.**  For a bifunctor `T` and maps `cp`, `cq`
in its two variables, `R` of `T(cp, -)` then `T(-, cq)` then `t`, after `k`, is invertible as
soon as `k` followed by `R(T(-, cq))` is and `T(cp, -)` followed by `t` is. -/
theorem isIso_comp_map_bifunctor {B : Type u₂} [Category.{v₂} B] (R : E ⥤ B) (T : E ⥤ E ⥤ E)
    {P P' Y Y' Z : E} (cp : P ⟶ P') (cq : Y ⟶ Y') (t : (T.obj P').obj Y' ⟶ Z) {b : B}
    (k : b ⟶ R.obj ((T.obj P).obj Y))
    (hk : IsIso (k ≫ R.map ((Functor.uncurry.obj T).map (𝟙 P ×ₘ cq))))
    (ht : IsIso ((T.map cp).app Y' ≫ t)) :
    IsIso (k ≫ R.map ((T.map cp).app Y ≫ (T.obj P').map cq ≫ t)) := by
  have hn : (T.map cp).app Y ≫ (T.obj P').map cq = (T.obj P).map cq ≫ (T.map cp).app Y' :=
    ((T.map cp).naturality cq).symm
  have hu : (Functor.uncurry.obj T).map (𝟙 P ×ₘ cq) = (T.obj P).map cq := by simp
  rw [← Category.assoc ((T.map cp).app Y), hn, Category.assoc, Functor.map_comp, ← Category.assoc,
    ← hu]
  infer_instance

/-- `isIso_comp_map_bifunctor` with the last map split into two factors, the second of which is
invertible. -/
theorem isIso_comp_map_bifunctor_comp {B : Type u₂} [Category.{v₂} B] (R : E ⥤ B)
    (T : E ⥤ E ⥤ E) {P P' Y Y' Z Z' : E} (cp : P ⟶ P') (cq : Y ⟶ Y')
    (t₁ : (T.obj P').obj Y' ⟶ Z) (t₂ : Z ⟶ Z') {b : B} (k : b ⟶ R.obj ((T.obj P).obj Y))
    (hk : IsIso (k ≫ R.map ((Functor.uncurry.obj T).map (𝟙 P ×ₘ cq))))
    (ht₁ : IsIso ((T.map cp).app Y' ≫ t₁)) (ht₂ : IsIso t₂) :
    IsIso (k ≫ R.map ((T.map cp).app Y ≫ (T.obj P').map cq ≫ t₁ ≫ t₂)) :=
  isIso_comp_map_bifunctor R T cp cq (t₁ ≫ t₂) k hk (isIso_comp_assoc_of _ _ _ ht₁ ht₂)

/-- **The global Künneth map, with the comparison inserted.**  For a natural isomorphism
`λ : R ⋙ Γ ≅ Σ`, the composite `A ≫ κ ≫ Γ(k) ≫ λ ≫ Σ(e)` is invertible as soon as `A`, `κ` and
`k ≫ R(e)` are. -/
theorem isIso_comp_natIso_map {B : Type u₂} [Category.{v₂} B] {Γ' : Type u₁} [Category.{v₁} Γ']
    (R : E ⥤ B) (Γ : B ⥤ Γ') (Sg : E ⥤ Γ') (lam : R ⋙ Γ ≅ Sg) {x₀ x₁ : Γ'} {b : B} {T T' : E}
    (A : x₀ ⟶ x₁) (κ : x₁ ⟶ Γ.obj b) (k : b ⟶ R.obj T) (e : T ⟶ T')
    (hA : IsIso A) (hκ : IsIso κ) (hk : IsIso (k ≫ R.map e)) :
    IsIso ((A ≫ κ ≫ Γ.map k ≫ lam.hom.app T) ≫ Sg.map e) := by
  simp only [Category.assoc]
  rw [← lam.hom.naturality, Functor.comp_map, ← Functor.map_comp_assoc]
  infer_instance

end Abstract

section Geometry

attribute [local instance] HasDerivedCategory.standard

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (hq : q ≫ b = p ≫ a)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The relative Künneth map of [Stacks, Tag 0FLP] is the chain of the source's three
comparisons**: the projection formula of [Stacks, Tag 08EU] at `a`, the base-change leg in the
second factor, and the interchanged-order projection formula at `p`, followed by the
identification `Ra_*Rp_* ≅ R(p ≫ a)_*`. -/
theorem kunnethMap_eq_chain
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethMap a b p q (p ≫ a) rfl hq K M =
      CategoryTheory.adjunctionTensorMap (derivedAdjunction a)
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (pullbackTensorComparison a) K ((derivedPushforward b).obj M) ≫
        (derivedPushforward a).map ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          (𝟙 K ×ₘ kunnethBaseChangeLeg a b p q hq M)) ≫
        (derivedPushforward a).map (adjunctionTensorMapRight (derivedAdjunction p)
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
          (pullbackTensorComparison p) K ((derivedPullback q).obj M)) ≫
        (derivedPushforwardCompIso p a).hom.app _ :=
  homEquiv_bitensor_comp_eq_chain (derivedAdjunction a) (derivedAdjunction p)
    (derivedAdjunction (p ≫ a)) (derivedPullbackCompIsoCanonical p a)
    (derivedPushforwardCompIso p a) (derivedAdjunction_comp_homEquiv p a)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
    (pullbackTensorComparison a) (pullbackTensorComparison p) K
    ((derivedPushforward b).obj M) ((derivedPullback q).obj M)
    ((pullbackTensorComparison (p ≫ a)).app
      ((derivedPushforward a).obj K, (derivedPushforward b).obj M))
    ((pullbackCounitLeg b q (p ≫ a) hq).app M)
    ((pullbackCounitLeg a p (p ≫ a) rfl).app K)
    (by simp [pullbackCounitLeg, pullbackCounitLegComp])
    (Stacks.Cohomology.DerivedKunneth.pullbackTensorComparisonComp a p _ _)

/-- **The relative Künneth map followed by a map in the second factor.**  For
`c : Lq^*M ⟶ Q'`, the relative Künneth map of [Stacks, Tag 0FLP] followed by
`R(p ≫ a)_*(Lp^*K ⊗^𝐋 c)` is invertible as soon as the projection formula at `a`, the
base-change leg `La^*Rb_*M ⟶ Rp_*Lq^*M` followed by `Rp_*c`, and the interchanged-order
projection formula at `(K, Q')` are. -/
theorem isIso_kunnethMap_comp_tensorMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    {Q' : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))}
    (cq : (derivedPullback q).obj M ⟶ Q')
    (h1 : IsIso (CategoryTheory.adjunctionTensorMap (derivedAdjunction a)
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (pullbackTensorComparison a) K ((derivedPushforward b).obj M)))
    (h2 : IsIso (kunnethBaseChangeLeg a b p q hq M ≫ (derivedPushforward p).map cq))
    (h3 : IsIso (adjunctionTensorMapRight (derivedAdjunction p)
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
          (pullbackTensorComparison p) K Q')) :
    IsIso (kunnethMap a b p q (p ≫ a) rfl hq K M ≫
        (derivedPushforward (p ≫ a)).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            (𝟙 ((derivedPullback p).obj K) ×ₘ cq))) :=
  isIso_homEquiv_bitensor_comp_tensorMap (derivedAdjunction a) (derivedAdjunction p)
    (derivedAdjunction (p ≫ a)) (derivedPullbackCompIsoCanonical p a)
    (derivedPushforwardCompIso p a) (derivedAdjunction_comp_homEquiv p a)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
    (pullbackTensorComparison a) (pullbackTensorComparison p) K
    ((derivedPushforward b).obj M) ((derivedPullback q).obj M)
    ((pullbackTensorComparison (p ≫ a)).app
      ((derivedPushforward a).obj K, (derivedPushforward b).obj M))
    ((pullbackCounitLeg b q (p ≫ a) hq).app M)
    ((pullbackCounitLeg a p (p ≫ a) rfl).app K)
    (by simp [pullbackCounitLeg, pullbackCounitLegComp])
    (Stacks.Cohomology.DerivedKunneth.pullbackTensorComparisonComp a p _ _) cq h1 h2 h3

end Geometry

end AlgebraicGeometry.FlatKunneth

end
