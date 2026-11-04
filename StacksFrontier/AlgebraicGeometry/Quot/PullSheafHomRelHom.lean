module

public import StacksFrontier.AlgebraicGeometry.Quot.PullSheafHomComparison
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomFunctorNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp

/-!
# Morphisms between derived pullbacks as sections of a pulled-back internal Hom

Let `q : T ⟶ Z` be a morphism of algebraic spaces and `P`, `M` objects of `D(𝒪_Z)`.  A
morphism `γ : Lq^*𝒪_Z ⟶ Lq^*R𝓗om(P, M)` gives a morphism `Lq^*P ⟶ Lq^*M`, namely

`Lq^*P ≅ Lq^*(𝒪_Z ⊗^L P) ≅ Lq^*𝒪_Z ⊗^L Lq^*P ⟶ Lq^*R𝓗om(P, M) ⊗^L Lq^*P
  ≅ Lq^*(R𝓗om(P, M) ⊗^L P) ⟶ Lq^*M`,

built from the unit constraint, the isomorphism of Stacks 07A4, `γ` and the evaluation map.
This file proves two things about this construction.

* It is compatible with the comparison triangles of the derived pullback pseudofunctor datum,
  because Stacks 07A4 is compatible with composition
  (`AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_comp`).
* It is bijective when `P` is perfect, because it factors through the canonical map of
  Stacks 08JF and the tensor–Hom adjunction of Stacks 08J8.

So it gives an isomorphism between the relative Hom functors `T ↦ Hom(Lq^*𝒪, Lq^*R𝓗om(P, M))`
and `T ↦ Hom(Lq^*P, Lq^*M)` at every cone.

## Main definitions

* `CategoryTheory.Functor.tensorEvalTransport`: the construction for an abstract functor with a
  comparison of tensor products.
* `AlgebraicGeometry.Space.SmallEtaleDerivedPullbackDataCompIsoEq`: the composition comparison
  of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` is the inverse of the composition
  isomorphism of Stacks 0D6D (internal; proved as
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataCompIsoEq` in
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedPullbackDataCompIso.lean`),
  as a proposition.
* `AlgebraicGeometry.Space.pullHomOfSections`: the construction for algebraic spaces.

## Main results

* `CategoryTheory.Functor.tensorEvalTransport_comp`: the abstract compatibility with
  composition.
* `AlgebraicGeometry.Space.pullHomOfSections_eq`: the factorization through Stacks 08JF.
* `AlgebraicGeometry.Space.bijective_pullHomOfSections`: bijectivity when the map of Stacks
  08JF is invertible.
* `AlgebraicGeometry.Space.isTriangleNatural_pullHomOfSections`: compatibility with the
  comparison triangles.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

variable {CZ Cb Ca : Type*} [Category* CZ] [Category* Cb] [Category* Ca]

/-- For a functor `F` with a comparison `μ : F(- ⊗ -) ≅ F(-) ⊗ F(-)`, a morphism
`γ : F O ⟶ F R` and morphisms `l : P ⟶ O ⊗ P`, `ev : R ⊗ P ⟶ M`, the composite
`F P ⟶ F(O ⊗ P) ≅ F O ⊗ F P ⟶ F R ⊗ F P ≅ F(R ⊗ P) ⟶ F M`. -/
abbrev tensorEvalTransport {C' : Type*} [Category* C'] {TZ : CZ ⥤ CZ ⥤ CZ}
    {T' : C' ⥤ C' ⥤ C'} (F : CZ ⥤ C')
    (μ : Functor.uncurry.obj TZ ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj T')
    {O P R M : CZ} (l : P ⟶ (TZ.obj O).obj P) (ev : (TZ.obj R).obj P ⟶ M)
    (γ : F.obj O ⟶ F.obj R) : F.obj P ⟶ F.obj M :=
  F.map l ≫ μ.hom.app (O, P) ≫ (T'.map γ).app (F.obj P) ≫ μ.inv.app (R, P) ≫ F.map ev

/-- **The construction is compatible with composition.**  If `c : Q ⋙ H ≅ K` carries the
comparison of tensor products of `K` to that of `Q` followed by that of `H`, then the
construction for `K` at the conjugate of `γ` by `c` is the conjugate by `c` of the construction
for `Q` at `γ`. -/
theorem tensorEvalTransport_comp {TZ : CZ ⥤ CZ ⥤ CZ} {Tb : Cb ⥤ Cb ⥤ Cb} {Ta : Ca ⥤ Ca ⥤ Ca}
    {Q : CZ ⥤ Cb} {H : Cb ⥤ Ca} {Kf : CZ ⥤ Ca} (c : Q ⋙ H ≅ Kf)
    (μQ : Functor.uncurry.obj TZ ⋙ Q ≅ Q.prod Q ⋙ Functor.uncurry.obj Tb)
    (μH : Functor.uncurry.obj Tb ⋙ H ≅ H.prod H ⋙ Functor.uncurry.obj Ta)
    (μK : Functor.uncurry.obj TZ ⋙ Kf ≅ Kf.prod Kf ⋙ Functor.uncurry.obj Ta)
    (hμ : Functor.whiskerLeft (Functor.uncurry.obj TZ) c.hom ≫ μK.hom =
      Functor.whiskerRight μQ.hom H ≫ Functor.whiskerLeft (Q.prod Q) μH.hom ≫
        Functor.whiskerRight (NatTrans.prod c.hom c.hom) (Functor.uncurry.obj Ta))
    {O P R M : CZ} (l : P ⟶ (TZ.obj O).obj P) (ev : (TZ.obj R).obj P ⟶ M)
    (γ : Q.obj O ⟶ Q.obj R) :
    tensorEvalTransport Kf μK l ev (c.inv.app O ≫ H.map γ ≫ c.hom.app R) =
      c.inv.app P ≫ H.map (tensorEvalTransport Q μQ l ev γ) ≫ c.hom.app M := by
  have hc : ∀ (A B : CZ), μK.hom.app (A, B) = c.inv.app _ ≫ H.map (μQ.hom.app (A, B)) ≫
      μH.hom.app (Q.obj A, Q.obj B) ≫ (Ta.map (c.hom.app A)).app _ ≫
        (Ta.obj _).map (c.hom.app B) := by
    intro A B
    have := NatTrans.congr_app hμ (A, B)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj] at this
    rw [← cancel_epi (c.hom.app ((Functor.uncurry.obj TZ).obj (A, B))), this,
      Iso.hom_inv_id_app_assoc]
    rfl
  have hc' : ∀ (A B : CZ), μK.inv.app (A, B) =
      (Ta.obj _).map (c.inv.app B) ≫ (Ta.map (c.inv.app A)).app _ ≫
        μH.inv.app (Q.obj A, Q.obj B) ≫ H.map (μQ.inv.app (A, B)) ≫ c.hom.app _ := by
    intro A B
    rw [← cancel_epi (μK.hom.app (A, B)), Iso.hom_inv_id_app, hc]
    simp only [Category.assoc]
    simp [← Functor.map_comp_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp]
  have hn := μH.hom.naturality (X := (Q.obj O, Q.obj P)) (Y := (Q.obj R, Q.obj P)) (γ, 𝟙 _)
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.map_id,
    Category.comp_id, Functor.prod_obj, Functor.comp_obj, Functor.uncurry_obj_obj] at hn
  have hmid : (Ta.map (c.hom.app O)).app (H.obj (Q.obj P)) ≫
      (Ta.obj (Kf.obj O)).map (c.hom.app P) ≫
      (Ta.map (c.inv.app O) ≫ Ta.map (H.map γ) ≫ Ta.map (c.hom.app R)).app (Kf.obj P) ≫
      (Ta.obj (Kf.obj R)).map (c.inv.app P) ≫ (Ta.map (c.inv.app R)).app (H.obj (Q.obj P)) =
      (Ta.map (H.map γ)).app (H.obj (Q.obj P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.naturality_assoc]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, ← NatTrans.naturality_assoc]
    simp [← NatTrans.comp_app_assoc, ← Functor.map_comp]
  have hnl := c.inv.naturality l
  have hne := c.hom.naturality ev
  simp only [Functor.comp_map, Functor.comp_obj] at hnl hne
  simp only [tensorEvalTransport, hc, hc', Functor.map_comp, Category.assoc, Functor.prod_obj,
    Functor.comp_obj, Functor.uncurry_obj_obj]
  rw [reassoc_of% hnl, reassoc_of% hmid, ← reassoc_of% hn, Iso.hom_inv_id_app_assoc, hne]

/-- Composing with an isomorphism on the left is bijective. -/
theorem bijective_iso_hom_comp {C : Type*} [Category* C] {X Y : C} (i : X ≅ Y) (Z : C) :
    Function.Bijective (fun γ : Y ⟶ Z => i.hom ≫ γ) :=
  ⟨fun a b h => (cancel_epi i.hom).1 h, fun b => ⟨i.inv ≫ b, by simp⟩⟩

/-- Composing with an isomorphism on the right is bijective. -/
theorem bijective_comp_isIso {C : Type*} [Category* C] {Y Z : C} (X : C) (i : Y ⟶ Z)
    [hi : IsIso i] :
    Function.Bijective (fun γ : X ⟶ Y => γ ≫ i) :=
  ⟨fun a b h => (cancel_mono i).1 h, fun b => ⟨b ≫ CategoryTheory.inv i, by simp⟩⟩

end CategoryTheory.Functor

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The composition comparison of the derived pullback pseudofunctor datum is the inverse of
the composition isomorphism of Stacks 0D6D** (internal; proved as
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataCompIsoEq` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedPullbackDataCompIso.lean`),
as a proposition. -/
def SmallEtaleDerivedPullbackDataCompIsoEq : Prop :=
  ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
    (smallEtaleDerivedPullbackData B S hS).compIso f g =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).symm

variable {B S hS}

/-- **A morphism between derived pullbacks from a section of a pulled-back internal Hom.**  For
`q : T ⟶ Z` and `γ : Lq^*𝒪_Z ⟶ Lq^*R𝓗om(P, M)`, the morphism
`Lq^*P ≅ Lq^*(𝒪_Z ⊗^L P) ≅ Lq^*𝒪_Z ⊗^L Lq^*P ⟶ Lq^*R𝓗om(P, M) ⊗^L Lq^*P
  ≅ Lq^*(R𝓗om(P, M) ⊗^L P) ⟶ Lq^*M`. -/
def pullHomOfSections {T Z : AlgebraicSpaces B S hS} (q : T ⟶ Z) (P M : derivedModules B S hS Z)
    (γ : ((smallEtaleDerivedPullbackData B S hS).pull q).obj (structureObject B S hS Z) ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull q).obj
        (((smallEtaleDerivedSheafHom B S hS Z).obj (Opposite.op P)).obj M)) :
    ((smallEtaleDerivedPullbackData B S hS).pull q).obj P ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull q).obj M :=
  Functor.tensorEvalTransport ((smallEtaleDerivedPullbackData B S hS).pull q)
    (smallEtaleDerivedPullbackTensorIso q) (smallEtaleDerivedLeftUnitIso B S hS P).inv
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS Z P).counit.app M) γ

/-- The construction factors through the map of Stacks 08JF and the tensor–Hom adjunction of
Stacks 08J8 on `T`. -/
theorem pullHomOfSections_eq {T Z : AlgebraicSpaces B S hS} (q : T ⟶ Z)
    (P M : derivedModules B S hS Z)
    (γ : ((smallEtaleDerivedPullbackData B S hS).pull q).obj (structureObject B S hS Z) ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull q).obj
        (((smallEtaleDerivedSheafHom B S hS Z).obj (Opposite.op P)).obj M)) :
    pullHomOfSections q P M γ =
      ((smallEtaleDerivedPullbackData B S hS).pull q).map
          (smallEtaleDerivedLeftUnitIso B S hS P).inv ≫
        (smallEtaleDerivedPullbackTensorIso q).hom.app (structureObject B S hS Z, P) ≫
          ((smallEtaleDerivedTensorSheafHomAdjunction B S hS T
            (((smallEtaleDerivedPullbackData B S hS).pull q).obj P)).homEquiv _ _).symm
            (γ ≫ pullSheafHomComparison q P M) := by
  have h1 := (smallEtaleDerivedTensorSheafHomAdjunction B S hS T
    (((smallEtaleDerivedPullbackData B S hS).pull q).obj P)).homEquiv_naturality_left_symm γ
      (pullSheafHomComparison q P M)
  rw [homEquiv_symm_pullSheafHomComparison] at h1
  change _ ≫ _ ≫ (((smallEtaleDerivedTensor B S hS T).flip.obj
      (((smallEtaleDerivedPullbackData B S hS).pull q).obj P)).map γ ≫
        pullSheafHomComparisonTranspose q P M) = _
  congr 2
  exact h1.symm

/-- **The construction is bijective when the map of Stacks 08JF is invertible**, in particular
when `P` is perfect and `AlgebraicGeometry.Space.PullSheafHomComparisonIsIso` holds. -/
theorem bijective_pullHomOfSections {T Z : AlgebraicSpaces B S hS} (q : T ⟶ Z)
    (P M : derivedModules B S hS Z) (h : IsIso (pullSheafHomComparison q P M)) :
    Function.Bijective (pullHomOfSections q P M) := by
  let ι := ((smallEtaleDerivedPullbackData B S hS).pull q).mapIso
      (smallEtaleDerivedLeftUnitIso B S hS P).symm ≪≫
    (smallEtaleDerivedPullbackTensorIso q).app (structureObject B S hS Z, P)
  have e : pullHomOfSections q P M = (fun γ => ι.hom ≫ γ) ∘
      ((smallEtaleDerivedTensorSheafHomAdjunction B S hS T
            (((smallEtaleDerivedPullbackData B S hS).pull q).obj P)).homEquiv _ _).symm ∘
      (fun γ => γ ≫ pullSheafHomComparison q P M) := by
    funext γ
    exact (pullHomOfSections_eq q P M γ).trans (Category.assoc _ _ _).symm
  rw [e]
  exact (Functor.bijective_iso_hom_comp ι _).comp
    ((Equiv.bijective _).comp (Functor.bijective_comp_isIso (hi := h) _ _))

/-- **The construction is compatible with the comparison triangles** of the derived pullback
pseudofunctor datum, given that its composition comparison is that of Stacks 0D6D. -/
theorem isTriangleNatural_pullHomOfSections (hc : SmallEtaleDerivedPullbackDataCompIsoEq B S hS)
    {Z : AlgebraicSpaces B S hS} (P M : derivedModules B S hS Z) :
    (smallEtaleDerivedPullbackData B S hS).IsTriangleNatural
      (M := structureObject B S hS Z)
      (N := ((smallEtaleDerivedSheafHom B S hS Z).obj (Opposite.op P)).obj M) (M' := P) (N' := M)
      (fun q γ => pullHomOfSections q P M γ) := by
  intro a b h q k hk γ
  subst hk
  rw [PullbackData.triangle_rfl, hc h q]
  exact Functor.tensorEvalTransport_comp (smallEtaleDerivedModulePullbackCompIso B S hS h q)
    (smallEtaleDerivedPullbackTensorIso q) (smallEtaleDerivedPullbackTensorIso h)
    (smallEtaleDerivedPullbackTensorIso (h ≫ q)) (smallEtaleDerivedPullbackTensorIso_comp h q)
    _ _ γ

end AlgebraicGeometry.Space

end
