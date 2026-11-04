module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Natural transformations compatible with the shift: connecting morphisms and derivation

A natural transformation `τ : Φ ⟶ Ψ` between functors `Φ, Ψ : 𝒞 ⥤ 𝒟` of categories with a shift
is *compatible with the shift* when `CategoryTheory.NatTrans.CommShift τ ℤ` holds. This file
records two consequences of that compatibility.

The first is what the notion is for when two long exact sequences are to be compared: for a
functor `H : 𝒟 ⥤ 𝒜` with a shift sequence, the maps `H ⁿ(τ)` commute with the connecting
morphisms `H ⁿ(T.obj₃) ⟶ H ⁿ⁺¹(T.obj₁)` attached to the images of a triangle `T` of `𝒞` under
`Φ` and under `Ψ`. Compatibility with the shift is exactly what makes `τ` a morphism of
triangles, and the connecting morphism is natural in the triangle.

The second is a descent statement. If `α : F ⟶ L ⋙ RF` exhibits `RF` as a right derived functor
of `F` along a localization `L`, then a natural transformation out of `RF` is determined by one
out of `F` (`CategoryTheory.Functor.rightDerivedDesc`), and the descended transformation is
compatible with the shift as soon as the undescended one is. This reduces the compatibility with
the shift of a comparison map between total derived functors to the same question for the
underived comparison.

Two elementary criteria for recognizing the compatibility are recorded as well: it may be
checked after composing with a faithful functor on the left, or after composing with a functor
whose image contains every object on the right. The first of them is applied to the inclusion of
a full subcategory closed under the shift, which turns the compatibility of a natural
transformation between functors lifted through that subcategory into the same question in the
ambient category.

## Main results

* `Stacks.Triangulated.homologySequenceδ_natTrans`: a natural transformation compatible with the
  shift commutes with the connecting morphisms of the homology sequence.
* `Stacks.Triangulated.natTransCommShift_rightDerivedDesc`: the descent of a natural
  transformation compatible with the shift along a right derived functor is again compatible
  with the shift.
* `Stacks.Triangulated.natTransCommShift_of_whiskerRight`,
  `Stacks.Triangulated.natTransCommShift_of_whiskerLeft`: compatibility with the shift descends
  from a whiskering by a faithful functor, and from a whiskering by a functor hitting every
  object.
* `Stacks.Triangulated.natTransCommShift_of_whiskerRight_eq`,
  `Stacks.Triangulated.natTransCommShift_of_whiskerLeft_eq`: the same two criteria, with the
  whiskered transformation presented through isomorphisms of its source and target.
* `Stacks.Triangulated.natTransCommShift_lift`,
  `Stacks.Triangulated.natTransCommShift_liftComp`: a natural transformation between functors
  lifted through a full subcategory closed under the shift is compatible with the shift as soon
  as the transformation it lifts is.

## Implementation notes

The morphism of triangles induced by `τ` is written out inside the proof of
`homologySequenceδ_natTrans` rather than named: its three components are `τ` itself, and the only
content is the third commuting square, where the compatibility with the shift is spent through
`CategoryTheory.NatTrans.shift_app_comm`. That square is proved in term mode, because
`(Φ.mapTriangle.obj T).obj₁` is `Φ.obj T.obj₁` only after `CategoryTheory.Functor.mapTriangle` is
unfolded and the step needed happens underneath `(shiftFunctor 𝒟 1).map`, so a tactic proof
builds a goal that is not type-correct at the `implicit` transparency level.

The descent statement is proved by the uniqueness half of the universal property. Both sides of
the required identity are natural transformations out of `shiftFunctor 𝒟 a ⋙ RF`, which Mathlib's
`CategoryTheory.Functor.IsRightDerivedFunctor.precomposeShiftNatTrans` exhibits as a right
derived functor of `shiftFunctor 𝒞 a ⋙ F`; so it suffices to compare them after composing with
that unit, and there the two shift compatibilities and the defining factorization of the descent
finish the computation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

namespace Stacks.Triangulated

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### Two criteria -/

section Criteria

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]

/-- **Compatibility with the shift may be checked after whiskering by a faithful functor.** If
`Θ` is faithful and commutes with the shift, a natural transformation `σ` is compatible with the
shift as soon as `σ` whiskered by `Θ` is. -/
public theorem natTransCommShift_of_whiskerRight (Θ : D ⥤ E) [Θ.CommShift A] [Θ.Faithful]
    {F₁ F₂ : C ⥤ D} [F₁.CommShift A] [F₂.CommShift A] (σ : F₁ ⟶ F₂)
    (h : NatTrans.CommShift (Functor.whiskerRight σ Θ) A) : NatTrans.CommShift σ A := by
  have := h
  refine ⟨fun a => ?_⟩
  ext X
  dsimp
  apply Θ.map_injective
  have key := NatTrans.shift_app_comm (Functor.whiskerRight σ Θ) a X
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app,
    Category.assoc] at key
  rwa [Θ.map_comp, Θ.map_comp, ← cancel_mono ((Θ.commShiftIso a).hom.app (F₂.obj X)),
    Category.assoc, Category.assoc, Functor.commShiftIso_hom_naturality Θ (σ.app X) a]

/-- **Compatibility with the shift may be checked after whiskering by a functor hitting every
object.** If every object of the source of `σ` is in the image of a functor `Θ` commuting with
the shift, then `σ` is compatible with the shift as soon as `Θ` whiskered into `σ` is. -/
public theorem natTransCommShift_of_whiskerLeft {X : Type*} [Category* X] [HasShift X A]
    (Θ : X ⥤ C) [Θ.CommShift A] (hΘ : ∀ Y : C, ∃ K : X, Θ.obj K = Y)
    {F₁ F₂ : C ⥤ D} [F₁.CommShift A] [F₂.CommShift A] (σ : F₁ ⟶ F₂)
    (h : NatTrans.CommShift (Functor.whiskerLeft Θ σ) A) : NatTrans.CommShift σ A := by
  have := h
  refine ⟨fun a => ?_⟩
  ext Y
  obtain ⟨K, rfl⟩ := hΘ Y
  dsimp
  have key := NatTrans.shift_app_comm (Functor.whiskerLeft Θ σ) a K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at key
  rwa [← cancel_epi (F₁.map ((Θ.commShiftIso a).hom.app K)),
    reassoc_of% (σ.naturality ((Θ.commShiftIso a).hom.app K))]

/-- **Compatibility with the shift may be checked after whiskering by a faithful functor and
reading the result through isomorphisms.** If `Θ` is faithful and commutes with the shift, and
`σ` whiskered by `Θ` becomes, after conjugating by isomorphisms `u₁` and `u₂` compatible with the
shift, a natural transformation `σ₀` compatible with the shift, then `σ` is compatible with the
shift. -/
public theorem natTransCommShift_of_whiskerRight_eq (Θ : D ⥤ E) [Θ.CommShift A] [Θ.Faithful]
    {F₁ F₂ : C ⥤ D} [F₁.CommShift A] [F₂.CommShift A] (σ : F₁ ⟶ F₂)
    {G₁ G₂ : C ⥤ E} [G₁.CommShift A] [G₂.CommShift A]
    (u₁ : F₁ ⋙ Θ ≅ G₁) (u₂ : F₂ ⋙ Θ ≅ G₂) (σ₀ : G₁ ⟶ G₂)
    (hu₁ : NatTrans.CommShift u₁.hom A) (hu₂ : NatTrans.CommShift u₂.hom A)
    (hσ₀ : NatTrans.CommShift σ₀ A)
    (h : Functor.whiskerRight σ Θ = u₁.hom ≫ σ₀ ≫ u₂.inv) :
    NatTrans.CommShift σ A := by
  have := hu₁
  have := hu₂
  have := hσ₀
  refine natTransCommShift_of_whiskerRight A Θ σ ?_
  rw [h]
  infer_instance

/-- **Compatibility with the shift may be checked after whiskering by a functor hitting every
object and reading the result through isomorphisms.** If every object of the source of `σ` is in
the image of a functor `Θ` commuting with the shift, and `Θ` whiskered into `σ` becomes, after
conjugating by isomorphisms `u₁` and `u₂` compatible with the shift, a natural transformation
`σ₀` compatible with the shift, then `σ` is compatible with the shift. -/
public theorem natTransCommShift_of_whiskerLeft_eq {X : Type*} [Category* X] [HasShift X A]
    (Θ : X ⥤ C) [Θ.CommShift A] (hΘ : ∀ Y : C, ∃ K : X, Θ.obj K = Y)
    {F₁ F₂ : C ⥤ D} [F₁.CommShift A] [F₂.CommShift A] (σ : F₁ ⟶ F₂)
    {G₁ G₂ : X ⥤ D} [G₁.CommShift A] [G₂.CommShift A]
    (u₁ : Θ ⋙ F₁ ≅ G₁) (u₂ : Θ ⋙ F₂ ≅ G₂) (σ₀ : G₁ ⟶ G₂)
    (hu₁ : NatTrans.CommShift u₁.hom A) (hu₂ : NatTrans.CommShift u₂.hom A)
    (hσ₀ : NatTrans.CommShift σ₀ A)
    (h : Functor.whiskerLeft Θ σ = u₁.hom ≫ σ₀ ≫ u₂.inv) :
    NatTrans.CommShift σ A := by
  have := hu₁
  have := hu₂
  have := hσ₀
  refine natTransCommShift_of_whiskerLeft A Θ hΘ σ ?_
  rw [h]
  infer_instance

end Criteria

/-! ### Natural transformations between functors into a full subcategory -/

section Lift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (P : ObjectProperty D) (Q : ObjectProperty E)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  [P.IsStableUnderShift A] [Q.IsStableUnderShift A]

/-- **A natural transformation between two functors lifted through a full subcategory is
compatible with the shift as soon as the transformation it lifts is.** The shift on the full
subcategory of objects satisfying `P` is the one induced by the inclusion, which is faithful, so
the compatibility may be read off in the ambient category. -/
public theorem natTransCommShift_lift {F₁ F₂ : C ⥤ D} [F₁.CommShift A] [F₂.CommShift A]
    (hF₁ : ∀ X, P (F₁.obj X)) (hF₂ : ∀ X, P (F₂.obj X)) (σ₀ : F₁ ⟶ F₂)
    (hσ₀ : NatTrans.CommShift σ₀ A) (σ : P.lift F₁ hF₁ ⟶ P.lift F₂ hF₂)
    (hσ : ∀ X, (σ.app X).hom = σ₀.app X) :
    NatTrans.CommShift σ A := by
  refine natTransCommShift_of_whiskerRight_eq A P.ι σ
    (P.liftCompιIso F₁ hF₁) (P.liftCompιIso F₂ hF₂) σ₀ inferInstance inferInstance hσ₀ ?_
  ext X
  simp [ObjectProperty.liftCompιIso, hσ X]

/-- **A natural transformation from a composite of two lifts to a lift is compatible with the
shift as soon as the transformation it lifts is.** The source of `σ` is the composite of the lift
of `Φ` through the subcategory of objects satisfying `P` with the lift of `P.ι ⋙ Ψ` through the
subcategory of objects satisfying `Q`, and whiskering by the inclusion `Q.ι` identifies `σ` with
the transformation `ρ` out of `Φ ⋙ Ψ`. -/
public theorem natTransCommShift_liftComp {Φ : C ⥤ D} {Ψ : D ⥤ E} {Λ : C ⥤ E}
    [Φ.CommShift A] [Ψ.CommShift A] [Λ.CommShift A]
    (hΦ : ∀ X, P (Φ.obj X)) (hΨ : ∀ X : P.FullSubcategory, Q ((P.ι ⋙ Ψ).obj X))
    (hΛ : ∀ X, Q (Λ.obj X)) (ρ : Φ ⋙ Ψ ⟶ Λ) (hρ : NatTrans.CommShift ρ A)
    (σ : P.lift Φ hΦ ⋙ Q.lift (P.ι ⋙ Ψ) hΨ ⟶ Q.lift Λ hΛ)
    (hσ : ∀ X, (σ.app X).hom = ρ.app X) :
    NatTrans.CommShift σ A := by
  refine natTransCommShift_of_whiskerRight_eq A Q.ι σ
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (P.lift Φ hΦ)
        (Q.liftCompιIso (P.ι ⋙ Ψ) hΨ) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (P.liftCompιIso Φ hΦ) Ψ)
    (Q.liftCompιIso Λ hΛ) ρ ?_ inferInstance hρ ?_
  · dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  · ext X
    simp [ObjectProperty.liftCompιIso, hσ X]

end Lift

/-! ### Connecting morphisms -/

section Connecting

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] [HasShift C ℤ] [HasShift D ℤ]
  {Φ Ψ : C ⥤ D} [Φ.CommShift ℤ] [Ψ.CommShift ℤ]

/-- **A natural transformation compatible with the shift commutes with the connecting morphisms
of the homology sequence.** For `τ : Φ ⟶ Ψ` compatible with the shift, a triangle `T` of the
source and a functor `H` with a shift sequence, the square formed by `H ⁿ⁰(τ)`, `H ⁿ¹(τ)` and the
two connecting morphisms of the triangles `Φ T` and `Ψ T` commutes. -/
public theorem homologySequenceδ_natTrans (H : D ⥤ A) [H.ShiftSequence ℤ] (τ : Φ ⟶ Ψ)
    [NatTrans.CommShift τ ℤ] (T : Triangle C) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    (H.shift n₀).map (τ.app T.obj₃) ≫ H.homologySequenceδ (Ψ.mapTriangle.obj T) n₀ n₁ hn =
      H.homologySequenceδ (Φ.mapTriangle.obj T) n₀ n₁ hn ≫ (H.shift n₁).map (τ.app T.obj₁) :=
  H.homologySequenceδ_naturality (T := Φ.mapTriangle.obj T) (T' := Ψ.mapTriangle.obj T)
    { hom₁ := τ.app T.obj₁
      hom₂ := τ.app T.obj₂
      hom₃ := τ.app T.obj₃
      comm₁ := τ.naturality T.mor₁
      comm₂ := τ.naturality T.mor₂
      comm₃ :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ Φ.map T.mor₃ ≫ z)
              (NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁)).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun z ↦ z ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app T.obj₁)
                  (τ.naturality T.mor₃)).trans (Category.assoc _ _ _)))) }
    n₀ n₁ hn

end Connecting

/-! ### Descent along a right derived functor -/

section Descent

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {L : C ⥤ D} {F : C ⥤ E} (RF : D ⥤ E) (α : F ⟶ L ⋙ RF)
  (W : MorphismProperty C) [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift E A]
  [W.IsCompatibleWithShift A] [F.CommShift A] [L.CommShift A] [RF.CommShift A]
  [NatTrans.CommShift α A]
  (G : D ⥤ E) [G.CommShift A] (β : F ⟶ L ⋙ G) [NatTrans.CommShift β A]

/-- **The descent of a natural transformation compatible with the shift along a right derived
functor is again compatible with the shift.** If `α : F ⟶ L ⋙ RF` exhibits `RF` as a right
derived functor of `F` and both `α` and `β : F ⟶ L ⋙ G` are compatible with the shift, then so is
the unique natural transformation `RF ⟶ G` through which `β` factors. -/
public theorem natTransCommShift_rightDerivedDesc :
    NatTrans.CommShift (RF.rightDerivedDesc α W G β) A where
  shift_comm a := by
    refine Functor.rightDerived_ext (CategoryTheory.shiftFunctor D a ⋙ RF)
      (Functor.IsRightDerivedFunctor.precomposeShiftNatTrans RF α a) W
      (G ⋙ CategoryTheory.shiftFunctor E a) _ _ ?_
    ext X
    dsimp
    have hα := NatTrans.shift_app_comm α a X
    have hβ := NatTrans.shift_app_comm β a X
    simp only [Functor.commShiftIso_comp_hom_app] at hα hβ
    have hnat : RF.map ((Functor.commShiftIso L a).hom.app X) ≫
        (RF.rightDerivedDesc α W G β).app ((CategoryTheory.shiftFunctor D a).obj (L.obj X)) =
        (RF.rightDerivedDesc α W G β).app (L.obj ((CategoryTheory.shiftFunctor C a).obj X)) ≫
          G.map ((Functor.commShiftIso L a).hom.app X) :=
      (RF.rightDerivedDesc α W G β).naturality _
    simp only [Functor.IsRightDerivedFunctor.precomposeShiftNatTrans_app, Category.assoc]
    rw [reassoc_of% hnat, Functor.rightDerived_fac_app_assoc RF α W G β,
      ← reassoc_of% hα, ← (CategoryTheory.shiftFunctor E a).map_comp,
      Functor.rightDerived_fac_app RF α W G β, hβ]

end Descent

end Stacks.Triangulated

end
