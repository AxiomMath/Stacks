module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafInverseImageSectionsLimit

/-!
# Sections of the inverse image of a sheaf of sets over a limit of schemes: surjectivity

Let `X = lim X_i` be the limit of a cofiltered inverse system of schemes with affine transition
morphisms, let `H` be a sheaf of sets on the small étale site of a stage `X_i` and let `V₀` be a
quasi-compact and quasi-separated object of that site, with base changes `V_j = V₀ ×_{X_i} X_j`
and `V = V₀ ×_{X_i} X`. Then

`(f_i⁻¹H)(V) = colim_j (f_{ji}⁻¹H)(V_j)`,

the degree zero case of [Stacks, Tag 09YQ] for the system of inverse images of a single sheaf
([Stacks, Tag 09YN] in the étale setting). The injectivity half is
`Stacks.EtaleCohomology.exists_smallEtaleSheafPullbackUnitApp_eq_of_isLimit`; this file proves
the surjectivity half, `Stacks.EtaleCohomology.Sets.exists_pullbackSectionsMap_eq_of_isLimit`.

## Main results

* `Stacks.EtaleCohomology.Sets.exists_pullbackSectionsMap_eq_of_isLimit`: **the surjectivity
  half** of the degree zero colimit formula for sheaves of sets.

## Implementation notes

The proof is the one of `Stacks.EtaleCohomology.exists_pullbackSectionsMap_eq_of_isLimit` for
abelian sheaves, with the scheme-theoretic steps (descent of affine objects and of morphisms to a
stage, transport along the transition morphisms) shared with it. Where the abelian argument
compares two sections through the vanishing of their difference, the agreement of the two
sections is carried directly, as sheaves of sets require.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Sets

/-- Restricting a section of a presheaf of sets along two composable morphisms is restricting it
along the composite. -/
lemma presheaf_map_map_apply_types {C : Type*} [Category* C] (P : Cᵒᵖ ⥤ Type (u + 1))
    {U V W : C} (k : U ⟶ V) (k' : V ⟶ W) (x : P.obj (op W)) :
    P.map k.op (P.map k'.op x) = P.map (k ≫ k').op x := by
  rw [op_comp, Functor.map_comp_apply]

section Units

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (H : Sheaf (smallEtaleTopology Y) (Type (u + 1)))

/-- Restricting along two morphisms into a base change with the same first component gives the
same section. -/
lemma map_eq_map_of_left_fst {U : X.Etale} {W : Y.Etale}
    (k k' : U ⟶ (smallEtaleBaseChange f).obj W)
    (h : k.left ≫ pullback.fst W.hom f = k'.left ≫ pullback.fst W.hom f)
    (x : ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.obj
      (op ((smallEtaleBaseChange f).obj W))) :
    ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.map k.op x =
      ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.map k'.op x := by
  rw [smallEtaleBaseChange_hom_ext f h]

variable {X' : Scheme.{u}} (g : X' ⟶ X) (gf : X' ⟶ Y) (hgf : gf = g ≫ f)

/-- **The comparison of sections of iterated inverse images, on units.** The comparison
`(f⁻¹H)(U) ⟶ ((gf)⁻¹H)(U ×_X X')` carries the restriction of the image of a section `h` of `H`
under the unit along `k : U ⟶ W ×_Y X` to the restriction of the image of `h` under the unit of
`gf` along any morphism `U ×_X X' ⟶ W ×_Y X'` with the same first component. -/
lemma pullbackSectionsMap_map_unitApp {U : X.Etale} {W : Y.Etale}
    (k : U ⟶ (smallEtaleBaseChange f).obj W) (h : H.obj.obj (op W))
    (k' : (smallEtaleBaseChange g).obj U ⟶ (smallEtaleBaseChange gf).obj W)
    (hk' : k'.left ≫ pullback.fst W.hom gf =
      pullback.fst U.hom g ≫ k.left ≫ pullback.fst W.hom f) :
    smallEtaleSheafPullbackSectionsMap g f gf hgf H U
        (((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.map k.op
          (smallEtaleSheafPullbackUnitApp f H W h)) =
      ((smallEtaleSheafPullback (Type (u + 1)) gf).obj H).obj.map k'.op
        (smallEtaleSheafPullbackUnitApp gf H W h) := by
  rw [smallEtaleSheafPullbackSectionsMap_naturality]
  have hu' : smallEtaleSheafPullbackSectionsMap g f gf hgf H _
      (smallEtaleSheafPullbackUnitApp f H W h) =
      ((smallEtaleSheafPullback (Type (u + 1)) gf).obj H).obj.map
        ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).op
        (smallEtaleSheafPullbackUnitApp gf H W h) := by
    rw [← smallEtaleSheafPullbackSectionsMap_unitApp g f gf hgf H W h, presheaf_map_map_apply_types,
      Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rw [hu', presheaf_map_map_apply_types]
  refine map_eq_map_of_left_fst gf H _ _ ?_ _
  have h₂ : ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).left ≫
      ((smallEtaleBaseChangeComp' g f gf hgf).hom.app W).left = 𝟙 _ :=
    congrArg (fun φ => φ.left) ((smallEtaleBaseChangeComp' g f gf hgf).inv_hom_id_app W)
  change (((smallEtaleBaseChange g).map k).left ≫
      ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).left) ≫ pullback.fst W.hom gf =
    k'.left ≫ pullback.fst W.hom gf
  rw [hk', ← smallEtaleBaseChangeComp'_fst_fst g f gf hgf W, Category.assoc, reassoc_of% h₂]
  exact (Category.assoc _ _ _).symm.trans
    ((smallEtaleBaseChange_map_left_fst g k =≫ _).trans (Category.assoc _ _ _))

/-- Two sections with the same image under the unit have the same comparison to the inverse
image along the composite. -/
lemma pullbackSectionsMap_eq_of_unitApp_eq {U : X.Etale}
    (y y' : ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.obj (op U))
    (hy : smallEtaleSheafPullbackUnitApp g ((smallEtaleSheafPullback (Type (u + 1)) f).obj H) U y =
      smallEtaleSheafPullbackUnitApp g ((smallEtaleSheafPullback (Type (u + 1)) f).obj H) U y') :
    smallEtaleSheafPullbackSectionsMap g f gf hgf H U y =
      smallEtaleSheafPullbackSectionsMap g f gf hgf H U y' := by
  rw [smallEtaleSheafPullbackSectionsMap, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    hy]

include g hgf in
/-- **Agreement under a unit persists along a composite.** -/
lemma unitApp_eq_of_comp {U : Y.Etale} (h h' : H.obj.obj (op U))
    (hz : smallEtaleSheafPullbackUnitApp f H U h = smallEtaleSheafPullbackUnitApp f H U h') :
    smallEtaleSheafPullbackUnitApp gf H U h = smallEtaleSheafPullbackUnitApp gf H U h' := by
  rw [← smallEtaleSheafPullbackSectionsMap_unitApp g f gf hgf H U h,
    ← smallEtaleSheafPullbackSectionsMap_unitApp g f gf hgf H U h', hz]

end Units


section Descent

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- The restriction of the section given by a stage descent to the object of the limit is the
given restriction of the image of the section of `H` under the unit. -/
lemma StageDescent.map_pullbackSectionsMap {i : I}
    (H : Sheaf (smallEtaleTopology (D.obj i)) (Type (u + 1)))
    {A : c.pt.Etale} {W : (D.obj i).Etale} {gW : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W}
    {j : I} (e : j ⟶ i) {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left}
    (hθ : θ ≫ Z.hom = A.hom ≫ c.π.app j) (χ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj W)
    (hχ : θ ≫ χ.left ≫ pullback.fst W.hom (D.map e) = gW.left ≫ pullback.fst W.hom (c.π.app i))
    (h : H.obj.obj (op W)) :
    ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map
        (smallEtaleBaseChangeHomMk (c.π.app j) θ hθ).op
        (smallEtaleSheafPullbackSectionsMap (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H Z
          (((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H).obj.map χ.op
            (smallEtaleSheafPullbackUnitApp (D.map e) H W h))) =
      ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map gW.op
        (smallEtaleSheafPullbackUnitApp (c.π.app i) H W h) := by
  have hk : (pullback.fst Z.hom (c.π.app j) ≫ χ.left ≫ pullback.fst W.hom (D.map e)) ≫ W.hom =
      ((smallEtaleBaseChange (c.π.app j)).obj Z).hom ≫ c.π.app i := by
    rw [Category.assoc, smallEtaleBaseChange_left_fst_hom, ← Category.assoc, pullback.condition,
      Category.assoc, c.w]
    rfl
  rw [pullbackSectionsMap_map_unitApp (D.map e) H (c.π.app j) (c.π.app i) (c.w e).symm χ h
    (smallEtaleBaseChangeHomMk (c.π.app i) _ hk) (smallEtaleBaseChangeHomMk_left_fst _ _ _)]
  refine (presheaf_map_map_apply_types _ _ _ _).trans
    (map_eq_map_of_left_fst (c.π.app i) H _ _ ?_ _)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (smallEtaleBaseChangeHomMk_left_fst _ _ _)).trans
      ((smallEtaleBaseChangeHomMk_left_fst_assoc _ _ _ _).trans hχ))

end Descent

section TransportOverlap

variable {X' X Y : Scheme.{u}} (φ : X' ⟶ X) (e : X ⟶ Y) (e' : X' ⟶ Y) (he : e' = φ ≫ e)
  (H : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
  {Z₁ Z₂ : X.Etale} {V₀ : Y.Etale}
  {ψ₁ : Z₁ ⟶ (smallEtaleBaseChange e).obj V₀} {ψ₂ : Z₂ ⟶ (smallEtaleBaseChange e).obj V₀}
  {T₁ : (smallEtaleBaseChange φ).obj Z₁ ⟶ (smallEtaleBaseChange e').obj V₀}
  {T₂ : (smallEtaleBaseChange φ).obj Z₂ ⟶ (smallEtaleBaseChange e').obj V₀}

include he in
/-- **Agreement on overlaps moves to later stages.** Let `T_k : Z_k ×_X X' ⟶ V₀ ×_Y X'` have the
same first components as the base changes of `ψ_k : Z_k ⟶ V₀ ×_Y X`, and similarly `S_k` for
`χ_k`. If the difference of the restrictions to `Z₁ ×_{ψ} Z₂` of two sections given by units dies
under the unit of `φ`, then the corresponding sections over the `Z_k ×_X X'` agree on the fibre
product of the `T_k`. -/
lemma map_fst_eq_map_snd_of_unitApp_eq {W₁ W₂ : Y.Etale}
    (hT₁ : T₁.left ≫ pullback.fst V₀.hom e' = pullback.fst Z₁.hom φ ≫ ψ₁.left ≫
      pullback.fst V₀.hom e)
    (hT₂ : T₂.left ≫ pullback.fst V₀.hom e' = pullback.fst Z₂.hom φ ≫ ψ₂.left ≫
      pullback.fst V₀.hom e)
    (χ₁ : Z₁ ⟶ (smallEtaleBaseChange e).obj W₁) (χ₂ : Z₂ ⟶ (smallEtaleBaseChange e).obj W₂)
    (S₁ : (smallEtaleBaseChange φ).obj Z₁ ⟶ (smallEtaleBaseChange e').obj W₁)
    (S₂ : (smallEtaleBaseChange φ).obj Z₂ ⟶ (smallEtaleBaseChange e').obj W₂)
    (hS₁ : S₁.left ≫ pullback.fst W₁.hom e' = pullback.fst Z₁.hom φ ≫ χ₁.left ≫
      pullback.fst W₁.hom e)
    (hS₂ : S₂.left ≫ pullback.fst W₂.hom e' = pullback.fst Z₂.hom φ ≫ χ₂.left ≫
      pullback.fst W₂.hom e)
    (h₁ : H.obj.obj (op W₁)) (h₂ : H.obj.obj (op W₂))
    (hd : smallEtaleSheafPullbackUnitApp φ ((smallEtaleSheafPullback (Type (u + 1)) e).obj H)
      (pullback ψ₁ ψ₂)
      (((smallEtaleSheafPullback (Type (u + 1)) e).obj H).obj.map (pullback.fst ψ₁ ψ₂).op
          (((smallEtaleSheafPullback (Type (u + 1)) e).obj H).obj.map χ₁.op
            (smallEtaleSheafPullbackUnitApp e H W₁ h₁))) =
      smallEtaleSheafPullbackUnitApp φ ((smallEtaleSheafPullback (Type (u + 1)) e).obj H)
        (pullback ψ₁ ψ₂)
        (((smallEtaleSheafPullback (Type (u + 1)) e).obj H).obj.map (pullback.snd ψ₁ ψ₂).op
          (((smallEtaleSheafPullback (Type (u + 1)) e).obj H).obj.map χ₂.op
            (smallEtaleSheafPullbackUnitApp e H W₂ h₂)))) :
    ((smallEtaleSheafPullback (Type (u + 1)) e').obj H).obj.map (pullback.fst T₁ T₂).op
        (((smallEtaleSheafPullback (Type (u + 1)) e').obj H).obj.map S₁.op
          (smallEtaleSheafPullbackUnitApp e' H W₁ h₁)) =
      ((smallEtaleSheafPullback (Type (u + 1)) e').obj H).obj.map (pullback.snd T₁ T₂).op
        (((smallEtaleSheafPullback (Type (u + 1)) e').obj H).obj.map S₂.op
          (smallEtaleSheafPullbackUnitApp e' H W₂ h₂)) := by
  let F' := ((smallEtaleSheafPullback (Type (u + 1)) e').obj H).obj
  let F := ((smallEtaleSheafPullback (Type (u + 1)) e).obj H).obj
  let u := pullback.lift _ _ (pullback_condition_baseChange_map φ e e' hT₁ hT₂) ≫
    smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂
  have hu₁ : u ≫ (smallEtaleBaseChange φ).map (pullback.fst ψ₁ ψ₂) = pullback.fst T₁ T₂ := by
    rw [Category.assoc, smallEtaleBaseChangePullbackLift_fst, pullback.lift_fst]
  have hu₂ : u ≫ (smallEtaleBaseChange φ).map (pullback.snd ψ₁ ψ₂) = pullback.snd T₁ T₂ := by
    rw [Category.assoc, smallEtaleBaseChangePullbackLift_snd, pullback.lift_snd]
  have key : ∀ {Z : X.Etale} {W : Y.Etale} (k : pullback ψ₁ ψ₂ ⟶ Z)
      (χ : Z ⟶ (smallEtaleBaseChange e).obj W)
      (S : (smallEtaleBaseChange φ).obj Z ⟶ (smallEtaleBaseChange e').obj W)
      (_ : S.left ≫ pullback.fst W.hom e' = pullback.fst Z.hom φ ≫ χ.left ≫ pullback.fst W.hom e)
      (hh : H.obj.obj (op W)) (k' : pullback T₁ T₂ ⟶ (smallEtaleBaseChange φ).obj Z)
      (_ : u ≫ (smallEtaleBaseChange φ).map k = k'),
      F'.map k'.op (F'.map S.op (smallEtaleSheafPullbackUnitApp e' H W hh)) =
        F'.map u.op (smallEtaleSheafPullbackSectionsMap φ e e' he H (pullback ψ₁ ψ₂)
          (F.map k.op (F.map χ.op (smallEtaleSheafPullbackUnitApp e H W hh)))) := by
    intro Z W k χ S hS hh k' hk
    rw [smallEtaleSheafPullbackSectionsMap_naturality,
      pullbackSectionsMap_map_unitApp e H φ e' he χ hh S hS, presheaf_map_map_apply_types F' u, hk]
  rw [key (pullback.fst ψ₁ ψ₂) χ₁ S₁ hS₁ h₁ _ hu₁, key (pullback.snd ψ₁ ψ₂) χ₂ S₂ hS₂ h₂ _ hu₂,
    pullbackSectionsMap_eq_of_unitApp_eq e H φ e' he _ _ hd]

end TransportOverlap

section Surjectivity

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- **The comparison of the section given by a stage descent.** The image in the sections of
`f_i⁻¹H` over the base change of `Z` of the section of `f_{ji}⁻¹H` given by `χ : Z ⟶ W ×_{X_i} X_j`
is the restriction of the given section `s` along `Z ×_{X_j} X ≅ A ⟶ V`. -/
lemma pullbackSectionsMap_eq_map_of_isPullback {i j : I} (e : j ⟶ i)
    (H : Sheaf (smallEtaleTopology (D.obj i)) (Type (u + 1))) {V₀ W : (D.obj i).Etale}
    (s : ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i)).obj V₀)))
    {A : c.pt.Etale} (g : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (m : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W) (h : H.obj.obj (op W))
    (hm : ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map g.op s =
      ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map m.op
        (smallEtaleSheafPullbackUnitApp (c.π.app i) H W h))
    {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left} (hθ : IsPullback θ A.hom Z.hom (c.π.app j))
    (χ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj W)
    (hχ : θ ≫ χ.left ≫ pullback.fst W.hom (D.map e) = m.left ≫ pullback.fst W.hom (c.π.app i)) :
    smallEtaleSheafPullbackSectionsMap (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H Z
        (((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H).obj.map χ.op
          (smallEtaleSheafPullbackUnitApp (D.map e) H W h)) =
      ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map
        (smallEtaleIsPullbackInv hθ ≫ g).op s := by
  rw [← presheaf_map_map_apply_types, hm,
    ← StageDescent.map_pullbackSectionsMap (gW := m) H e hθ.w χ hχ h, presheaf_map_map_apply_types,
    smallEtaleIsPullbackInv_comp, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- Two sections with the same comparison to the inverse image along a composite already have
the same image under the unit: the comparison is the unit followed by an isomorphism. -/
lemma unitApp_eq_of_pullbackSectionsMap_eq {X' X Y : Scheme.{u}} (g : X' ⟶ X)
    (f : X ⟶ Y) (gf : X' ⟶ Y) (hgf : gf = g ≫ f) (H : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (U : X.Etale) (y y' : ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.obj (op U))
    (hy : smallEtaleSheafPullbackSectionsMap g f gf hgf H U y =
      smallEtaleSheafPullbackSectionsMap g f gf hgf H U y') :
    smallEtaleSheafPullbackUnitApp g ((smallEtaleSheafPullback (Type (u + 1)) f).obj H) U y =
      smallEtaleSheafPullbackUnitApp g ((smallEtaleSheafPullback (Type (u + 1)) f).obj H) U y' :=
  ((ConcreteCategory.isIso_iff_bijective
    (((smallEtaleSheafPullbackCompApp (Type (u + 1)) g f gf hgf H).hom).hom.app
      (op ((smallEtaleBaseChange g).obj U)))).mp inferInstance).1 hy

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- **Agreement on overlaps of the sections given by two stage descents.** Two sections given by
units over objects `Z₁, Z₂` of a stage, presenting objects `A₁, A₂` of the limit on which the
given section `s` is described by the same units, agree over the base change to the limit of the
fibre product `Z₁ ×_B Z₂`; hence their difference dies under the unit of the projection. -/
lemma unitApp_eq_of_isPullback {i j : I} (e : j ⟶ i)
    (H : Sheaf (smallEtaleTopology (D.obj i)) (Type (u + 1))) {V₀ : (D.obj i).Etale}
    (s : ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i)).obj V₀)))
    {A₁ A₂ : c.pt.Etale} (g₁ : A₁ ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (g₂ : A₂ ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀) {W₁ W₂ : (D.obj i).Etale}
    (m₁ : A₁ ⟶ (smallEtaleBaseChange (c.π.app i)).obj W₁)
    (m₂ : A₂ ⟶ (smallEtaleBaseChange (c.π.app i)).obj W₂) (h₁ : H.obj.obj (op W₁))
    (h₂ : H.obj.obj (op W₂))
    (hm₁ : ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map g₁.op s =
      ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map m₁.op
        (smallEtaleSheafPullbackUnitApp (c.π.app i) H W₁ h₁))
    (hm₂ : ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map g₂.op s =
      ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map m₂.op
        (smallEtaleSheafPullbackUnitApp (c.π.app i) H W₂ h₂))
    {Z₁ Z₂ : (D.obj j).Etale} {θ₁ : A₁.left ⟶ Z₁.left} {θ₂ : A₂.left ⟶ Z₂.left}
    (hθ₁ : IsPullback θ₁ A₁.hom Z₁.hom (c.π.app j)) (hθ₂ : IsPullback θ₂ A₂.hom Z₂.hom (c.π.app j))
    (ψ₁ : Z₁ ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (ψ₂ : Z₂ ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (hψ₁ : θ₁ ≫ ψ₁.left ≫ pullback.fst V₀.hom (D.map e) =
      g₁.left ≫ pullback.fst V₀.hom (c.π.app i))
    (hψ₂ : θ₂ ≫ ψ₂.left ≫ pullback.fst V₀.hom (D.map e) =
      g₂.left ≫ pullback.fst V₀.hom (c.π.app i))
    (χ₁ : Z₁ ⟶ (smallEtaleBaseChange (D.map e)).obj W₁)
    (χ₂ : Z₂ ⟶ (smallEtaleBaseChange (D.map e)).obj W₂)
    (hχ₁ : θ₁ ≫ χ₁.left ≫ pullback.fst W₁.hom (D.map e) =
      m₁.left ≫ pullback.fst W₁.hom (c.π.app i))
    (hχ₂ : θ₂ ≫ χ₂.left ≫ pullback.fst W₂.hom (D.map e) =
      m₂.left ≫ pullback.fst W₂.hom (c.π.app i)) :
    smallEtaleSheafPullbackUnitApp (c.π.app j)
        ((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H)
        (pullback ψ₁ ψ₂)
        (((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H).obj.map (pullback.fst ψ₁ ψ₂).op
            (((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H).obj.map χ₁.op
              (smallEtaleSheafPullbackUnitApp (D.map e) H W₁ h₁))) =
      smallEtaleSheafPullbackUnitApp (c.π.app j)
        ((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H) (pullback ψ₁ ψ₂)
          (((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H).obj.map
            (pullback.snd ψ₁ ψ₂).op
            (((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H).obj.map χ₂.op
              (smallEtaleSheafPullbackUnitApp (D.map e) H W₂ h₂))) := by
  refine unitApp_eq_of_pullbackSectionsMap_eq _ _ _ (c.w e).symm H _ _ _ ?_
  rw [smallEtaleSheafPullbackSectionsMap_naturality (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H
      (pullback.fst ψ₁ ψ₂),
    smallEtaleSheafPullbackSectionsMap_naturality (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H
      (pullback.snd ψ₁ ψ₂),
    pullbackSectionsMap_eq_map_of_isPullback e H s g₁ m₁ h₁ hm₁ hθ₁ χ₁ hχ₁,
    pullbackSectionsMap_eq_map_of_isPullback e H s g₂ m₂ h₂ hm₂ hθ₂ χ₂ hχ₂]
  refine (presheaf_map_map_apply_types _ _ _ _).trans
    (Eq.trans ?_ (presheaf_map_map_apply_types _ _ _ _).symm)
  refine congrArg (fun (k : (smallEtaleBaseChange (c.π.app j)).obj (pullback ψ₁ ψ₂) ⟶
    (smallEtaleBaseChange (c.π.app i)).obj V₀) =>
      ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map k.op s) ?_
  have key : ∀ {A : c.pt.Etale} {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left}
      (hθ : IsPullback θ A.hom Z.hom (c.π.app j))
      (g : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
      (ψ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
      (_ : θ ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) =
        g.left ≫ pullback.fst V₀.hom (c.π.app i)) (q : pullback ψ₁ ψ₂ ⟶ Z),
      ((smallEtaleBaseChange (c.π.app j)).map q ≫ smallEtaleIsPullbackInv hθ ≫ g).left ≫
          pullback.fst V₀.hom (c.π.app i) =
        pullback.fst (pullback ψ₁ ψ₂).hom (c.π.app j) ≫ (q ≫ ψ).left ≫
          pullback.fst V₀.hom (D.map e) := fun hθ g ψ hψ q =>
    (whisker_eq _ (whisker_eq _ hψ.symm)).trans ((whisker_eq _
      (hθ.isoPullback_inv_fst_assoc _)).trans
        ((Category.assoc _ _ _).symm.trans
          (smallEtaleBaseChange_map_left_fst (c.π.app j) q =≫ _)))
  refine smallEtaleBaseChange_hom_ext (c.π.app i) ?_
  refine (key hθ₁ g₁ ψ₁ hψ₁ _).trans (Eq.trans ?_ (key hθ₂ g₂ ψ₂ hψ₂ _).symm)
  rw [pullback.condition]

include hc in
/-- **The surjectivity half of the degree zero colimit formula for an inverse image** (Stacks
09YN). Let `X = lim X_i` be a cofiltered limit of schemes with affine transition morphisms, `H` an
abelian sheaf on the small étale site of a stage `X_i` and `V₀` a quasi-compact and quasi-separated
object of that site. Every section of `f_i⁻¹H` over the base change of `V₀` to `X` comes from a
section of `f_{ji}⁻¹H` over the base change of `V₀` to a later stage `X_j`, through the comparison
of sections of iterated inverse images. -/
theorem exists_pullbackSectionsMap_eq_of_isLimit {i : I}
    (H : Sheaf (smallEtaleTopology (D.obj i)) (Type (u + 1))) (V₀ : (D.obj i).Etale)
    [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left]
    (s : ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i)).obj V₀))) :
    ∃ (j : I) (e : j ⟶ i) (t : ((smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H).obj.obj
        (op ((smallEtaleBaseChange (D.map e)).obj V₀))),
      ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj.map
          ((smallEtaleBaseChangeComp' (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm).hom.app
            V₀).op
          (smallEtaleSheafPullbackSectionsMap (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H
            _ t) = s := by
  classical
  let FX := ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H).obj
  let V := (smallEtaleBaseChange (c.π.app i)).obj V₀
  have : QuasiCompact (c.π.app i) := by
    have := isAffineHom_π_app D c hc i
    infer_instance
  have hVc : CompactSpace V.left := compactSpace_smallEtaleBaseChange_obj (c.π.app i) V₀
    inferInstance
  -- Local descriptions by units over finitely many affine objects.
  obtain ⟨S, hS, hloc⟩ := exists_covering_smallEtaleSheafPullback_eq_unitApp (c.π.app i) H V s
  choose A g hA hgS hgx using fun x : V.left =>
    exists_isAffine_mem_range_of_mem_smallEtaleTopology S hS x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : V.left => Set.range (g x).left)
    (fun x => (g x).left.isOpenMap.isOpen_range) (fun x _ => Set.mem_iUnion.2 ⟨x, hgx x⟩)
  let T := {x : V.left // x ∈ t}
  have hT : ∀ y : V.left, ∃ x : T, y ∈ Set.range (g x.1).left := fun y =>
    let ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    ⟨⟨x, hx⟩, hy⟩
  choose W' m h hm using fun x : T => hloc (g x.1) (hgS x.1)
  -- A common stage where all of them descend.
  obtain ⟨a₁, ha₁⟩ := common_stage_of_finite i
    (fun (a : Over i) (x : T) => StageDescent D c (A x.1) V₀ (W' x) (g x.1) (m x) a.hom)
    (fun {a b} φ x hb => hb.of_le φ.left a.hom (Over.w φ)) (fun x => by
      have := hA x.1
      obtain ⟨j, e, hd⟩ := exists_stageDescent D c hc (A x.1) V₀ (W' x) (g x.1) (m x)
      exact ⟨Over.mk e, hd⟩)
  let j := a₁.left
  let e : j ⟶ i := a₁.hom
  choose Z θ ψ χ hZc hZs hθ hψ hχ using ha₁
  let FL := (smallEtaleSheafPullback (Type (u + 1)) (D.map e)).obj H
  let B := (smallEtaleBaseChange (D.map e)).obj V₀
  let d₁ : ∀ x x' : T, FL.obj.obj (op (pullback (ψ x) (ψ x'))) := fun x x' =>
    FL.obj.map (pullback.fst (ψ x) (ψ x')).op
        (FL.obj.map (χ x).op (smallEtaleSheafPullbackUnitApp (D.map e) H (W' x) (h x)))
  let d₂ : ∀ x x' : T, FL.obj.obj (op (pullback (ψ x) (ψ x'))) := fun x x' =>
      FL.obj.map (pullback.snd (ψ x) (ψ x')).op
        (FL.obj.map (χ x').op (smallEtaleSheafPullbackUnitApp (D.map e) H (W' x') (h x')))
  have hBc : CompactSpace B.left := compactSpace_smallEtaleBaseChange_obj (D.map e) V₀
    inferInstance
  have hBs : QuasiSeparatedSpace B.left := quasiSeparatedSpace_smallEtaleBaseChange_obj
    (D.map e) V₀ inferInstance
  -- The second round: covering and agreement on overlaps at a later stage.
  let P : Over j → Option (T × T) → Prop := fun a o => match o with
    | none => Set.range (pullback.snd (D.map a.hom) B.hom) ⊆ ⋃ x : T, Set.range (ψ x).left
    | some q => smallEtaleSheafPullbackUnitApp (D.map a.hom) FL (pullback (ψ q.1) (ψ q.2))
        (d₁ q.1 q.2) =
          smallEtaleSheafPullbackUnitApp (D.map a.hom) FL (pullback (ψ q.1) (ψ q.2)) (d₂ q.1 q.2)
  obtain ⟨a₂, ha₂⟩ := common_stage_of_finite j P (by
    rintro a b φ (_ | q) hb
    · exact (range_pullback_snd_subset_of_fac (D.map b.hom) (D.map a.hom) (D.map φ.left)
        (by rw [← D.map_comp, Over.w φ]) B.hom).trans hb
    · exact unitApp_eq_of_comp (D.map b.hom) FL (D.map φ.left) (D.map a.hom)
        (by rw [← D.map_comp, Over.w φ]) _ _ hb) (by
    rintro (_ | q)
    · have : CompactSpace ((𝟭 Scheme.{u}).obj B.left) := hBc
      obtain ⟨j', f, hf⟩ := exists_range_pullback_snd_subset_of_isLimit D c hc B.hom
        ⟨⋃ x : T, Set.range (ψ x).left, isOpen_iUnion fun x => (ψ x).left.isOpenMap.isOpen_range⟩
        (by
          rintro _ ⟨w, rfl⟩
          let ε := (smallEtaleBaseChangeComp' (c.π.app j) (D.map e) (c.π.app i)
            (c.w e).symm).app V₀
          obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom)
            (g := c.π.app j) (pullback.snd (c.π.app j) B.hom w) (pullback.fst (c.π.app j) B.hom w)
            (by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply])
          obtain ⟨x, z, hz⟩ := hT (ε.inv.left v)
          refine Set.mem_iUnion.2 ⟨x, θ x z, ?_⟩
          have e₁ := congrArg (fun k => k.left ≫ pullback.fst B.hom (c.π.app j))
            (StageDescent.comp_baseChangeComp e (hθ x).w (ψ x) (hψ x))
          have e₂ : (smallEtaleBaseChangeHomMk (c.π.app j) (θ x) (hθ x).w ≫
              (smallEtaleBaseChange (c.π.app j)).map (ψ x)).left ≫ pullback.fst B.hom (c.π.app j) =
              θ x ≫ (ψ x).left :=
            (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
              (smallEtaleBaseChange_map_left_fst (c.π.app j) (ψ x))).trans
              ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (ψ x).left)
                (smallEtaleBaseChangeHomMk_left_fst _ _ _))))
          have e₃ : ε.inv.left ≫ ε.hom.left = 𝟙 _ := congrArg (fun k => k.left) ε.inv_hom_id
          change ((θ x) ≫ (ψ x).left) z = _
          refine (congrArg (fun k => k z) (e₂.symm.trans e₁.symm)).trans ?_
          change (pullback.fst B.hom (c.π.app j)) (ε.hom.left ((g x.1).left z)) = _
          rw [hz]
          change ((ε.inv.left ≫ ε.hom.left) ≫ pullback.fst B.hom (c.π.app j)) v = _
          rw [e₃]
          exact hv)
      exact ⟨Over.mk f, hf⟩
    · have := hZc q.1
      have := hZc q.2
      have hPb := isPullback_smallEtale_pullback (ψ q.1) (ψ q.2)
      have : QuasiCompact (pullback.fst (ψ q.1) (ψ q.2)).left :=
        MorphismProperty.of_isPullback hPb.flip inferInstance
      have hPc : CompactSpace (pullback (ψ q.1) (ψ q.2)).left :=
        QuasiCompact.compactSpace_of_compactSpace (pullback.fst (ψ q.1) (ψ q.2)).left
      obtain ⟨j', f, hf⟩ := exists_smallEtaleSheafPullbackUnitApp_eq_of_isLimit D c hc FL
        (pullback (ψ q.1) (ψ q.2)) (d₁ q.1 q.2) (d₂ q.1 q.2)
        (unitApp_eq_of_isPullback e H s (g q.1.1) (g q.2.1) (m q.1) (m q.2) (h q.1)
          (h q.2) (hm q.1) (hm q.2) (hθ q.1) (hθ q.2) (ψ q.1) (ψ q.2) (hψ q.1) (hψ q.2)
          (χ q.1) (χ q.2) (hχ q.1) (hχ q.2))
      exact ⟨Over.mk f, hf⟩)
  let k := a₂.left
  let φ : k ⟶ j := a₂.hom
  let ef : k ⟶ i := φ ≫ e
  have hef : D.map ef = D.map φ ≫ D.map e := D.map_comp φ e
  have hcov : Set.range (pullback.snd (D.map φ) B.hom) ⊆ ⋃ x : T, Set.range (ψ x).left :=
    ha₂ none
  let Zk : T → (D.obj k).Etale := fun x => (smallEtaleBaseChange (D.map φ)).obj (Z x)
  let ψk : ∀ x, Zk x ⟶ (smallEtaleBaseChange (D.map ef)).obj V₀ := fun x =>
    smallEtaleBaseChangeTransport (D.map φ) (D.map e) (D.map ef) hef (ψ x)
  let χk : ∀ x, Zk x ⟶ (smallEtaleBaseChange (D.map ef)).obj (W' x) := fun x =>
    smallEtaleBaseChangeTransport (D.map φ) (D.map e) (D.map ef) hef (χ x)
  let FK := (smallEtaleSheafPullback (Type (u + 1)) (D.map ef)).obj H
  let tk : ∀ x, FK.obj.obj (op (Zk x)) := fun x =>
    FK.obj.map (χk x).op (smallEtaleSheafPullbackUnitApp (D.map ef) H (W' x) (h x))
  -- The transported objects cover.
  have hcovk : ⋃ x, Set.range (ψk x).left = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    let r : ((smallEtaleBaseChange (D.map ef)).obj V₀).left ⟶ B.left :=
      pullback.lift (pullback.fst V₀.hom (D.map ef)) (pullback.snd V₀.hom (D.map ef) ≫ D.map φ)
        ((pullback.condition).trans ((congrArg (_ ≫ ·) hef).trans (Category.assoc _ _ _).symm))
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.map φ) (g := B.hom)
      (pullback.snd V₀.hom (D.map ef) y) (r y)
      (congrArg (fun k => k y) (pullback.lift_snd (pullback.fst V₀.hom (D.map ef))
        (pullback.snd V₀.hom (D.map ef) ≫ D.map φ) _)).symm
    obtain ⟨x, z, hz⟩ := Set.mem_iUnion.1 (hcov ⟨w, hw⟩)
    have hsq : IsPullback (pullback.fst (Z x).hom (D.map φ)) (ψk x).left (ψ x).left r := by
      have hψl : (ψ x).left = pullback.lift ((ψ x).left ≫ pullback.fst V₀.hom (D.map e))
          (Z x).hom (smallEtaleBaseChange_left_fst_hom (D.map e) (ψ x)) :=
        pullback.hom_ext (pullback.lift_fst _ _ _).symm
          ((smallEtaleBaseChange_w (D.map e) (ψ x)).trans (pullback.lift_snd _ _ _).symm)
      rw [hψl]
      exact isPullback_pullback_lift_of_comp (Z x).hom V₀.hom (D.map e) (D.map φ) (D.map ef)
        hef.symm _ _
    obtain ⟨y', -, hy'⟩ := AlgebraicGeometry.IsPullback.exists_preimage_scheme hsq z y hz
    exact Set.mem_iUnion.2 ⟨x, y', hy'⟩
  -- The local sections glue.
  obtain ⟨tg, htg⟩ := exists_glue_smallEtale FK (fun x => Zk x) ψk hcovk tk fun x x' =>
    map_fst_eq_map_snd_of_unitApp_eq (D.map φ) (D.map e) (D.map ef) hef H
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (ψ x))
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (ψ x')) (χ x) (χ x') (χk x) (χk x')
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (χ x))
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (χ x')) (h x) (h x') (ha₂ (some (x, x')))
  refine ⟨k, ef, tg, ?_⟩
  -- The glued section restricts to the given one.
  refine smallEtale_section_ext ((smallEtaleSheafPullback (Type (u + 1)) (c.π.app i)).obj H)
    (Sieve.ofArrows (fun x : T => A x.1) (fun x => g x.1)) ?_ _ _ ?_
  · exact (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (hT y))
  rintro U' g' hg'
  obtain ⟨x, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg'
  rw [← presheaf_map_map_apply_types FX a (g x.1), ← presheaf_map_map_apply_types FX a (g x.1)]
  refine congrArg (FX.map a.op) ?_
  let θk : (A x.1).left ⟶ (Zk x).left :=
    pullback.lift (θ x) ((A x.1).hom ≫ c.π.app k) (by rw [(hθ x).w, Category.assoc, c.w])
  have hθk : IsPullback θk (A x.1).hom (Zk x).hom (c.π.app k) :=
    isPullback_lift_of_isPullback D c (hθ x) φ
  have hψk : θk ≫ (ψk x).left ≫ pullback.fst V₀.hom (D.map ef) =
      (g x.1).left ≫ pullback.fst V₀.hom (c.π.app i) :=
    (congrArg (θk ≫ ·) (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (ψ x))).trans
      ((pullback.lift_fst_assoc _ _ _ _).trans (hψ x))
  have hχk : θk ≫ (χk x).left ≫ pullback.fst (W' x).hom (D.map ef) =
      (m x).left ≫ pullback.fst (W' x).hom (c.π.app i) :=
    (congrArg (θk ≫ ·) (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (χ x))).trans
      ((pullback.lift_fst_assoc _ _ _ _).trans (hχ x))
  rw [presheaf_map_map_apply_types FX (g x.1),
    StageDescent.comp_baseChangeComp ef hθk.w (ψk x) hψk, ← presheaf_map_map_apply_types FX,
    ← smallEtaleSheafPullbackSectionsMap_naturality, htg x, hm x]
  exact StageDescent.map_pullbackSectionsMap H ef hθk.w (χk x) hχk (h x)

end Surjectivity

end Stacks.EtaleCohomology.Sets

end
