module

public import StacksFrontier.CategoryTheory.Adjunction.InternalHomTrace
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBaseChange

/-!
# The trace map of Stacks 0E57 and base change, for abstract tensor–Hom data

Consider a square of categories with left adjoints `Lf ⊣ Rf : T ⥤ S`, `Lf' ⊣ Rf' : T' ⥤ S'`,
functors `Lg : S ⥤ S'`, `Lg' : T ⥤ T'` and an identification of the two composites around the
square, tensor bifunctors with internal Homs at the four corners and comparisons of tensor
products along the four left adjoints, compatible around the square. Let `ε : Rf Z ⟶ K`, and let
`α : Lg' Z ⟶ Z'` and `ε' : Rf' Z' ⟶ Lg K` satisfy `β_Z ≫ Rf' α ≫ ε' = Lg ε`, with `β` the base
change map. For `M` in `T`, the composite

`Lg Rf H(M, Z) ⟶ Rf' Lg' H(M, Z) ⟶ Rf' H(Lg' M, Lg' Z) ⟶ Rf' H(Lg' M, Z') ⟶ H(Rf' Lg' M, Lg K)`

of the base change map, `Rf'` of the map of Stacks 08JF, `Rf' H(Lg' M, α)` and the trace map of
Stacks 0E57, read in `H(Lg Rf M, Lg K)` along `β_M`, is `Lg` of the trace map followed by the
map of Stacks 08JF along `Lg`.

## Main definitions

* `CategoryTheory.InternalHomTrace.internalHomPrecompIso`: `H(Q, -) ≅ H(P, -)` along `P ≅ Q`.

## Main results

* `CategoryTheory.InternalHomTrace.pushforwardTrace_baseChange`: the trace map of Stacks 0E57
  commutes with base change.
* `CategoryTheory.InternalHomTrace.bijective_comp_of_isIso_map`: postcomposition with a morphism
  inverted by a right adjoint is bijective on morphisms out of the image of the left adjoint.
-/

@[expose] public noncomputable section

namespace CategoryTheory.InternalHomTrace

open Opposite Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open scoped CategoryTheory.Prod

section Precomp

variable {S' : Type*} [Category S'] (TS' : S' ⥤ S' ⥤ S') (HS' : S'ᵒᵖ ⥤ S' ⥤ S')
  (adjS' : ∀ P : S', TS'.flip.obj P ⊣ HS'.obj (op P))

/-- Precomposition on internal Homs along an isomorphism, `H(Q, -) ≅ H(P, -)` for `P ≅ Q`: the
conjugate of `- ⊗ P ≅ - ⊗ Q`. -/
def internalHomPrecompIso {P Q : S'} (b : P ≅ Q) :
    HS'.obj (op Q) ≅ HS'.obj (op P) :=
  conjugateIsoEquiv (adjS' Q) (adjS' P)
    (NatIso.ofComponents (fun N => (TS'.obj N).mapIso b) fun u => by simp)

/-- The adjunct of a map followed by `internalHomPrecompIso` is the adjunct of the map,
precomposed with `N ⊗ b`. -/
theorem homEquiv_symm_comp_internalHomPrecompIso {P Q : S'} (b : P ≅ Q) {N W : S'}
    (x : N ⟶ (HS'.obj (op Q)).obj W) :
    ((adjS' P).homEquiv N W).symm (x ≫ (internalHomPrecompIso TS' HS' adjS' b).hom.app W) =
      (TS'.obj N).map b.hom ≫ ((adjS' Q).homEquiv N W).symm x := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, internalHomPrecompIso, conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  simp only [Functor.flip_obj_obj, Functor.flip_obj_map, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom]
  rw [NatTrans.naturality_assoc]

end Precomp

section Square

variable {S T S' T' : Type*} [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TS : S ⥤ S ⥤ S) (TT : T ⥤ T ⥤ T) (TS' : S' ⥤ S' ⥤ S') (TT' : T' ⥤ T' ⥤ T')
  (αf : Functor.uncurry.obj TS ⋙ Lf ⟶ Lf.prod Lf ⋙ Functor.uncurry.obj TT)
  (αf' : Functor.uncurry.obj TS' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ Functor.uncurry.obj TT')
  (μg : Functor.uncurry.obj TS ⋙ Lg ≅ Lg.prod Lg ⋙ Functor.uncurry.obj TS')
  (μg' : Functor.uncurry.obj TT ⋙ Lg' ≅ Lg'.prod Lg' ⋙ Functor.uncurry.obj TT')
  (HS : Sᵒᵖ ⥤ S ⥤ S) (HT : Tᵒᵖ ⥤ T ⥤ T) (HS' : S'ᵒᵖ ⥤ S' ⥤ S') (HT' : T'ᵒᵖ ⥤ T' ⥤ T')
  (adjS : ∀ P : S, TS.flip.obj P ⊣ HS.obj (op P))
  (adjT : ∀ P : T, TT.flip.obj P ⊣ HT.obj (op P))
  (adjS' : ∀ P : S', TS'.flip.obj P ⊣ HS'.obj (op P))
  (adjT' : ∀ P : T', TT'.flip.obj P ⊣ HT'.obj (op P))

/-- The trace map of Stacks 0E57 under base change: if `β_Z ≫ Rf' α ≫ ε' = Lg ε`, then the base
change map at `H(M, Z)`, `Rf'` of the map of Stacks 08JF followed by `H(Lg' M, α)`, the trace map
for `ε'` and the precomposition with `β_M` is `Lg` of the trace map for `ε` followed by the map of
Stacks 08JF along `Lg`. -/
theorem pushforwardTrace_baseChange (M Z : T) {K : S} {Z' : T'} (ε : Rf.obj Z ⟶ K)
    (α : Lg'.obj Z ⟶ Z') (ε' : Rf'.obj Z' ⟶ Lg.obj K)
    (hL : Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef Z ≫ Rf'.map α ≫ ε' = Lg.map ε)
    (b : Lg.obj (Rf.obj M) ≅ Rf'.obj (Lg'.obj M))
    (hb : b.hom = Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef M)
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') αf αf' μg.hom μg'.hom
      (Rf.obj ((HT.obj (op M)).obj Z)) (Rf.obj M)) :
    Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef ((HT.obj (op M)).obj Z) ≫
        Rf'.map (PullbackInternalHom.pullbackHomMap TT TT' μg' HT HT' adjT adjT' M Z) ≫
        Rf'.map ((HT'.obj (op (Lg'.obj M))).map α) ≫
        pushforwardTrace adjf' TT' TS' αf' HT' HS' adjT' adjS' (Lg'.obj M) ε' ≫
        (internalHomPrecompIso TS' HS' adjS' b).hom.app (Lg.obj K) =
      Lg.map (pushforwardTrace adjf TT TS αf HT HS adjT adjS M ε) ≫
        PullbackInternalHom.pullbackHomMap TS TS' μg HS HS' adjS adjS' (Rf.obj M) K := by
  have hρ' : (TT'.map (PullbackInternalHom.pullbackHomMap TT TT' μg' HT HT' adjT adjT' M Z)).app
        (Lg'.obj M) ≫ (adjT' (Lg'.obj M)).counit.app (Lg'.obj Z) =
      μg'.inv.app ((HT.obj (op M)).obj Z, M) ≫ Lg'.map ((adjT M).counit.app Z) := by
    have e := ((adjT' (Lg'.obj M)).homEquiv_counit (X := Lg'.obj ((HT.obj (op M)).obj Z))
      (Y := Lg'.obj Z) (g := PullbackInternalHom.pullbackHomMap TT TT' μg' HT HT' adjT adjT' M Z))
    rw [← Functor.flip_obj_map, ← e]
    unfold PullbackInternalHom.pullbackHomMap
    exact Equiv.symm_apply_apply _ _
  have hρ : ((adjS' (Lg.obj (Rf.obj M))).homEquiv _ _).symm
      (PullbackInternalHom.pullbackHomMap TS TS' μg HS HS' adjS adjS' (Rf.obj M) K) =
      μg.inv.app ((HS.obj (op (Rf.obj M))).obj K, Rf.obj M) ≫
        Lg.map ((adjS (Rf.obj M)).counit.app K) := by
    unfold PullbackInternalHom.pullbackHomMap
    exact Equiv.symm_apply_apply _ _
  have htr : (TS.map (pushforwardTrace adjf TT TS αf HT HS adjT adjS M ε)).app (Rf.obj M) ≫
      (adjS (Rf.obj M)).counit.app K =
      adjunctionCupProduct adjf (Functor.uncurry.obj TS) (Functor.uncurry.obj TT) αf
        ((HT.obj (op M)).obj Z) M ≫ Rf.map ((adjT M).counit.app Z) ≫ ε := by
    have e := homEquiv_symm_comp_pushforwardTrace adjf TT TS αf HT HS adjT adjS M ε
      (𝟙 (Rf.obj ((HT.obj (op M)).obj Z)))
    rw [Category.id_comp, Adjunction.homEquiv_counit] at e
    simpa using e
  have h0H9A := adjunctionCupProduct_baseChange_square adjf adjf' eg ef
    (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
    (Functor.uncurry.obj TT') αf αf' μg.hom μg'.hom ((HT.obj (op M)).obj Z) M hsq
  have hnat := Stacks.CategoryTheory.BaseChange.map_naturality adjf adjf' eg ef
    ((adjT M).counit.app Z)
  have hR := μg.inv.naturality
    (X := ((HT.obj (op M)).obj Z |> Rf.obj, Rf.obj M))
    (Y := ((HS.obj (op (Rf.obj M))).obj K, Rf.obj M))
    (pushforwardTrace adjf TT TS αf HT HS adjT adjS M ε ×ₘ 𝟙 (Rf.obj M))
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj, Functor.comp_map,
    Functor.prod_map, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id]
    at hR
  have hcup := adjunctionCupProduct_natural adjf' (Functor.uncurry.obj TS')
    (Functor.uncurry.obj TT') αf'
    (PullbackInternalHom.pullbackHomMap TT TT' μg' HT HT' adjT adjT' M Z ≫
      (HT'.obj (op (Lg'.obj M))).map α) (𝟙 (Lg'.obj M))
  simp only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj, CategoryTheory.Functor.map_id,
    Category.comp_id] at hcup
  have hev := (adjT' (Lg'.obj M)).counit.naturality α
  simp only [Functor.comp_map, Functor.flip_obj_map, Functor.id_map] at hev
  have h0 : (TS'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef
        ((HT.obj (op M)).obj Z))).app (Lg.obj (Rf.obj M)) ≫
      (TS'.obj (Rf'.obj (Lg'.obj ((HT.obj (op M)).obj Z)))).map
        (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef M) ≫
      adjunctionCupProduct adjf' (Functor.uncurry.obj TS') (Functor.uncurry.obj TT') αf'
        (Lg'.obj ((HT.obj (op M)).obj Z)) (Lg'.obj M) =
      μg.inv.app (Rf.obj ((HT.obj (op M)).obj Z), Rf.obj M) ≫
        Lg.map (adjunctionCupProduct adjf (Functor.uncurry.obj TS) (Functor.uncurry.obj TT) αf
          ((HT.obj (op M)).obj Z) M) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef
          ((TT.obj ((HT.obj (op M)).obj Z)).obj M) ≫
        Rf'.map (μg'.hom.app ((HT.obj (op M)).obj Z, M)) := by
    simp only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Category.assoc] at h0H9A
    rw [← cancel_epi (μg.hom.app (Rf.obj ((HT.obj (op M)).obj Z), Rf.obj M)),
      Iso.hom_inv_id_app_assoc]
    exact h0H9A
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.flip_obj_obj] at hnat
  have hX : Rf'.map ((TT'.map (PullbackInternalHom.pullbackHomMap TT TT' μg' HT HT' adjT adjT' M Z ≫
        (HT'.obj (op (Lg'.obj M))).map α)).app (Lg'.obj M)) ≫
      Rf'.map ((adjT' (Lg'.obj M)).counit.app Z') =
      Rf'.map (μg'.inv.app ((HT.obj (op M)).obj Z, M) ≫ Lg'.map ((adjT M).counit.app Z) ≫ α) := by
    rw [← Functor.map_comp]
    congr 1
    rw [Functor.map_comp TT', NatTrans.comp_app, Category.assoc, hev, reassoc_of% hρ']
  rw [← Functor.map_comp_assoc]
  apply ((adjS' (Lg.obj (Rf.obj M))).homEquiv _ _).symm.injective
  simp only [← Category.assoc]
  rw [homEquiv_symm_comp_internalHomPrecompIso, homEquiv_symm_comp_pushforwardTrace,
    Adjunction.homEquiv_naturality_left_symm, hρ, Functor.flip_obj_map, reassoc_of% hR,
    ← Functor.map_comp, htr]
  rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc,
    reassoc_of% hcup, reassoc_of% hX, hb, reassoc_of% h0, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app_assoc, Functor.map_comp, Functor.map_comp, Functor.map_comp Lg, ← hL,
    reassoc_of% hnat]
  simp only [Category.assoc]

end Square


section Adjunction

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {R : D ⥤ C}

/-- Postcomposition with a morphism inverted by a right adjoint is bijective on morphisms out of
the image of the left adjoint. -/
theorem bijective_comp_of_isIso_map (adj : F ⊣ R) {A B : D} (φ : A ⟶ B) (hφ : IsIso (R.map φ))
    (N : C) : Function.Bijective fun u : F.obj N ⟶ A => u ≫ φ := by
  have key : (fun u : F.obj N ⟶ A => u ≫ φ) =
      (adj.homEquiv N B).symm ∘ (fun v : N ⟶ R.obj A => v ≫ R.map φ) ∘ adj.homEquiv N A := by
    funext u
    simp only [Function.comp_apply, ← Adjunction.homEquiv_naturality_right, Equiv.symm_apply_apply]
  rw [key]
  let e : (N ⟶ R.obj A) ≃ (N ⟶ R.obj B) :=
    { toFun := fun v => v ≫ R.map φ
      invFun := fun v => v ≫ inv (R.map φ)
      left_inv := fun v => by simp
      right_inv := fun v => by simp }
  exact (adj.homEquiv N B).symm.bijective.comp (e.bijective.comp (adj.homEquiv N A).bijective)

end Adjunction

end CategoryTheory.InternalHomTrace

end
