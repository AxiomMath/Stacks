module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StandardAffineFamily

/-!
# The comparison isomorphism of the family-to-singleton reduction

Let `b : Z ⟶ S` be a morphism of schemes, `u k : X k ⟶ Z` a Zariski open covering of `Z` and
`g k = u k ≫ b`.  For a descent datum `D` for the family `g`, the descent datum
`Stacks.Descent.transitionDescentData` for `b` is carried by `Stacks.Descent.familyPullFunctor`
to a descent datum isomorphic to `D`.  Hence `Stacks.Descent.familyPullFunctor` is essentially
surjective, and descent along `b` alone gives descent along the family.

## Main definitions

* `Stacks.Descent.mapOpIdIso`: the canonical isomorphism `(𝟙 X)^* M ≅ M`.
* `Stacks.Descent.abstractFamilyPullFunctor`: `Stacks.Descent.familyPullFunctor` over an arbitrary
  pseudofunctor.
* `Stacks.Descent.comparisonApp`: the component at `k` of the comparison isomorphism, namely the
  component `CategoryTheory.Pseudofunctor.DescentData.objIso` of the gluing isomorphism `eN`
  followed by `Stacks.Descent.mapOpIdIso`.
* `Stacks.Descent.comparisonIso`: the comparison isomorphism over an arbitrary pseudofunctor.
* `Stacks.Descent.familyPullFunctorObjIso`: the comparison isomorphism for
  `Stacks.Descent.qcohPseudofunctor`.

## Main results

* `Stacks.Descent.comparisonApp_comm`: the compatibility condition of
  `Stacks.Descent.comparisonIso`.
* `Stacks.Descent.essSurj_familyPullFunctor`: `Stacks.Descent.familyPullFunctor` is essentially
  surjective for a Zariski open covering `u` of `Z`.
* `Stacks.Descent.essSurj_qcohToDescentData_of_essSurj_single` and
  `Stacks.Descent.isEquivalence_qcohToDescentData_of_essSurj_single`: descent along `b` alone
  gives descent along the family.
* `Stacks.Descent.essSurj_familyPullFunctor_specMap`,
  `Stacks.Descent.essSurj_qcohToDescentData_specMap` and
  `Stacks.Descent.isEquivalence_qcohToDescentData_specMap`: the specialisations to a finite family
  of ring maps `ρ k : R ⟶ A k`, with hypotheses only on the single morphism
  `Spec (∏ₖ A k) ⟶ Spec R` (and, for the equivalence, the fpqc prestack condition).

## Implementation notes

* The comparison isomorphism and its compatibility condition are proved for an abstract
  pseudofunctor `F` and then instantiated: the compatibility crosses between
  `CategoryTheory.Pseudofunctor.DescentData.Hom.hom` and `CategoryTheory.Cat.Hom₂.toNatTrans`,
  which are definitionally equal and cheap to compare only while `F` is a variable.
* In `Stacks.Descent.comparisonApp_comm` the goal is not type-correct under `implicit`
  transparency, so after the local normal form is substituted no `rw` succeeds; the last steps
  are applications of `Stacks.Descent.comp_eq_of_eq_of_comp_eq_id`,
  `Stacks.Descent.comp_comp_eq_of_comp_eq` and `Stacks.Descent.map_comp3_eq_id`, which take the
  factor identities as hypotheses.  The lemma is stated at the base `f₁ ≫ g k₁`, which is the
  base `CategoryTheory.Pseudofunctor.DescentData.pullFunctorObj` carries.
* `Stacks.Descent.mapComp'_opId_comp_inv_app` and `Stacks.Descent.mapComp'_opId_comp_hom_app`
  restate `CategoryTheory.Pseudofunctor.mapComp'_id_comp_inv_app` and
  `CategoryTheory.Pseudofunctor.mapComp'_id_comp_hom_app` with the identity spelled
  `(𝟙 X).op.toLoc`, the form `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`
  produces, so that `rw` can use them.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite
  TopologicalSpace
open Pseudofunctor.LocallyDiscreteOpToCat

universe t v' v u' u

namespace Stacks.Descent

section AbstractComparison

section Composites

variable {Dc : Type u} [Category.{v} Dc]

/-- A composite with a head that splits in two and a tail that composes to the identity. -/
theorem comp_eq_of_eq_of_comp_eq_id {P Q R T W₁ W₂ : Dc} {a : P ⟶ R} {b : P ⟶ Q} {c : Q ⟶ R}
    (d : R ⟶ T) {t₁ : T ⟶ W₁} {t₂ : W₁ ⟶ W₂} {a₂ : W₂ ⟶ T} (h : a = b ≫ c)
    (ht : t₁ ≫ t₂ ≫ a₂ = 𝟙 T) :
    a ≫ d = b ≫ c ≫ d ≫ t₁ ≫ t₂ ≫ a₂ := by
  rw [h, ht, Category.comp_id, Category.assoc]

/-- A threefold composite whose first two factors compose to a given morphism `i`. -/
theorem comp_comp_eq_of_comp_eq {P Q R T : Dc} {a : P ⟶ Q} {b : Q ⟶ R} {i : P ⟶ R} (c : R ⟶ T)
    {j : P ⟶ T} (hi : i = a ≫ b) (hj : i ≫ c = j) : a ≫ b ≫ c = j := by
  rw [← Category.assoc, ← hi, hj]

variable {Dd : Type u'} [Category.{v'} Dd]

/-- A functor carries a threefold composite which is the identity to the identity. -/
theorem map_comp3_eq_id (G : Dc ⥤ Dd) {P Q R : Dc} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ P)
    (h : a ≫ b ≫ c = 𝟙 P) : G.map a ≫ G.map b ≫ G.map c = 𝟙 (G.obj P) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_id]

end Composites

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

variable {X₁ Y₁ : C}

/-- `CategoryTheory.Pseudofunctor.mapComp'_id_comp_inv_app` in the spelling that
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` produces, namely with the identity
of `CategoryTheory.LocallyDiscrete.mk (Opposite.op X₁)` written as `(𝟙 X₁).op.toLoc`. -/
theorem mapComp'_opId_comp_inv_app (h : Y₁ ⟶ X₁) (M : F.obj (.mk (op X₁)))
    (hh : (𝟙 X₁).op.toLoc ≫ h.op.toLoc = h.op.toLoc) :
    (F.mapComp' (𝟙 X₁).op.toLoc h.op.toLoc h.op.toLoc hh).inv.toNatTrans.app M =
      (F.map h.op.toLoc).toFunctor.map ((F.mapId (.mk (op X₁))).hom.toNatTrans.app M) :=
  F.mapComp'_id_comp_inv_app h.op.toLoc M

/-- The `hom` counterpart of `Stacks.Descent.mapComp'_opId_comp_inv_app`. -/
theorem mapComp'_opId_comp_hom_app (h : Y₁ ⟶ X₁) (M : F.obj (.mk (op X₁)))
    (hh : (𝟙 X₁).op.toLoc ≫ h.op.toLoc = h.op.toLoc) :
    (F.mapComp' (𝟙 X₁).op.toLoc h.op.toLoc h.op.toLoc hh).hom.toNatTrans.app M =
      (F.map h.op.toLoc).toFunctor.map ((F.mapId (.mk (op X₁))).inv.toNatTrans.app M) :=
  F.mapComp'_id_comp_hom_app h.op.toLoc M

/-- The canonical isomorphism between the pullback of `M` along the identity and `M` itself. -/
def mapOpIdIso (M : F.obj (.mk (op X₁))) : (F.map (𝟙 X₁).op.toLoc).toFunctor.obj M ≅ M where
  hom := (F.mapId (.mk (op X₁))).hom.toNatTrans.app M
  inv := (F.mapId (.mk (op X₁))).inv.toNatTrans.app M
  hom_inv_id := Cat.Hom.hom_inv_id_toNatTrans_app _ _
  inv_hom_id := Cat.Hom.inv_hom_id_toNatTrans_app _ _

variable {Sb Z : C} {bm : Z ⟶ Sb} {K : Type t} {Xk : K → C} {u : ∀ k, Xk k ⟶ Z}
  {g : ∀ k, Xk k ⟶ Sb}

/-- **The family-to-singleton comparison functor, over an arbitrary pseudofunctor.**  This is
`CategoryTheory.Pseudofunctor.DescentData.pullFunctor` at `p = 𝟙` and `p' = u`, of which
`Stacks.Descent.familyPullFunctor` is the instance at
`Stacks.Descent.qcohPseudofunctor`. -/
def abstractFamilyPullFunctor (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (w₀ : ∀ k, u k ≫ bm = g k ≫ 𝟙 Sb) :
    F.DescentData (fun _ : Unit ↦ bm) ⥤ F.DescentData g :=
  Pseudofunctor.DescentData.pullFunctor F (p := 𝟙 Sb) (α := fun _ ↦ (default : Unit)) (p' := u) w₀

variable (restrictW : ∀ k, 𝟙 (Xk k) ≫ g k = u k ≫ bm)

/-- **The components of the comparison isomorphism.**  The isomorphism `eN` identifies the
restriction of `N` to the member `u k` of the covering with the `k`-th object of the descent
datum, up to the pullback along the identity; `Stacks.Descent.mapOpIdIso` removes the latter. -/
def comparisonApp {N : F.obj (.mk (op Z))} {D : F.DescentData g}
    (eN : (F.toDescentData u).obj N ≅ (Pseudofunctor.DescentData.pullFunctor F restrictW).obj D)
    (k : K) : (F.map (u k).op.toLoc).toFunctor.obj N ≅ D.obj k :=
  Pseudofunctor.DescentData.objIso eN k ≪≫ mapOpIdIso (D.obj k)

/-- The forward component of `Stacks.Descent.comparisonApp`. -/
theorem comparisonApp_hom {N : F.obj (.mk (op Z))} {D : F.DescentData g}
    (eN : (F.toDescentData u).obj N ≅ (Pseudofunctor.DescentData.pullFunctor F restrictW).obj D)
    (k : K) : (comparisonApp restrictW eN k).hom =
      eN.hom.hom k ≫ (F.mapId (.mk (op (Xk k)))).hom.toNatTrans.app (D.obj k) := rfl

variable (hg : ∀ k, u k ≫ bm = g k)

/-- **The compatibility condition of the comparison isomorphism.**  If the transition morphisms
of a descent datum `E` for the single morphism `bm` are given by the local normal form `hE` in
terms of `D` and `eN`, then the components `Stacks.Descent.comparisonApp` commute with the
transition morphisms of `D` and of the pullback of `E` along the family. -/
theorem comparisonApp_comm (w₀ : ∀ k, u k ≫ bm = g k ≫ 𝟙 Sb)
    {D : F.DescentData g} (E : F.DescentData (fun _ : Unit ↦ bm))
    (eN : (F.toDescentData u).obj (E.obj default) ≅
      (Pseudofunctor.DescentData.pullFunctor F restrictW).obj D)
    (hE : ∀ ⦃V : C⦄ (q : V ⟶ Sb) ⦃k₁ k₂ : K⦄ (w₁ : V ⟶ Xk k₁) (w₂ : V ⟶ Xk k₂)
      (c₁ c₂ : V ⟶ Z) (hw₁ : w₁ ≫ g k₁ = q) (hw₂ : w₂ ≫ g k₂ = q)
      (hc₁ : w₁ ≫ u k₁ = c₁) (hc₂ : w₂ ≫ u k₂ = c₂),
      E.hom q (i₁ := default) (i₂ := default) c₁ c₂
          (by rw [← hc₁, Category.assoc, hg, hw₁]) (by rw [← hc₂, Category.assoc, hg, hw₂]) =
        pullHom (eN.hom.hom k₁) w₁ c₁ w₁ hc₁ (Category.comp_id _) ≫
          D.hom q w₁ w₂ hw₁ hw₂ ≫
          pullHom (eN.inv.hom k₂) w₂ w₂ c₂ (Category.comp_id _) hc₂)
    ⦃Y : C⦄ (q : Y ⟶ Sb) ⦃k₁ k₂ : K⦄ (f₁ : Y ⟶ Xk k₁) (f₂ : Y ⟶ Xk k₂)
    (hf₁ : f₁ ≫ g k₁ = q) (hf₂ : f₂ ≫ g k₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (comparisonApp restrictW eN k₁).hom ≫
        D.hom q f₁ f₂ hf₁ hf₂ =
      Pseudofunctor.DescentData.pullFunctorObjHom (α := fun _ ↦ (default : Unit)) (p' := u)
          w₀ E (f₁ ≫ g k₁) f₁ f₂ rfl (hf₂.trans hf₁.symm) ≫
        (F.map f₂.op.toLoc).toFunctor.map (comparisonApp restrictW eN k₂).hom := by
  subst hf₁
  rw [Pseudofunctor.DescentData.pullFunctorObjHom_eq (α := fun _ ↦ (default : Unit)) (p' := u)
      w₀ E (f₁ ≫ g k₁) f₁ f₂ (f₁ ≫ g k₁) (f₁ ≫ u k₁) (f₂ ≫ u k₂) rfl hf₂
      (Category.comp_id _) rfl rfl,
    hE (f₁ ≫ g k₁) f₁ f₂ (f₁ ≫ u k₁) (f₂ ≫ u k₂) rfl hf₂ rfl rfl]
  have hinv : (comparisonApp restrictW eN k₂).inv =
      (F.mapId (.mk (op (Xk k₂)))).inv.toNatTrans.app (D.obj k₂) ≫ eN.inv.hom k₂ := rfl
  have hABC := comp_comp_eq_of_comp_eq (comparisonApp restrictW eN k₂).hom hinv
    (comparisonApp restrictW eN k₂).inv_hom_id
  have htail := map_comp3_eq_id (F.map f₂.op.toLoc).toFunctor _ _ _ hABC
  have hhead : (F.map f₁.op.toLoc).toFunctor.map (comparisonApp restrictW eN k₁).hom =
      (F.map f₁.op.toLoc).toFunctor.map (eN.hom.hom k₁) ≫
        (F.map f₁.op.toLoc).toFunctor.map
          ((F.mapId (.mk (op (Xk k₁)))).hom.toNatTrans.app (D.obj k₁)) :=
    CategoryTheory.Functor.map_comp _ _ _
  dsimp only [pullHom]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  rw [mapComp'_opId_comp_inv_app, mapComp'_opId_comp_hom_app]
  exact comp_eq_of_eq_of_comp_eq_id _ hhead htail

/-- **The comparison isomorphism, over an arbitrary pseudofunctor.**  A descent datum `E` for the
single morphism `bm` whose transition morphisms are the local normal form `hE` built from a
descent datum `D` for the family and a gluing isomorphism `eN` is carried by
`Stacks.Descent.abstractFamilyPullFunctor` to a descent datum isomorphic to `D`, the components
being `Stacks.Descent.comparisonApp`. -/
def comparisonIso (w₀ : ∀ k, u k ≫ bm = g k ≫ 𝟙 Sb)
    {D : F.DescentData g} (E : F.DescentData (fun _ : Unit ↦ bm))
    (eN : (F.toDescentData u).obj (E.obj default) ≅
      (Pseudofunctor.DescentData.pullFunctor F restrictW).obj D)
    (hE : ∀ ⦃V : C⦄ (q : V ⟶ Sb) ⦃k₁ k₂ : K⦄ (w₁ : V ⟶ Xk k₁) (w₂ : V ⟶ Xk k₂)
      (c₁ c₂ : V ⟶ Z) (hw₁ : w₁ ≫ g k₁ = q) (hw₂ : w₂ ≫ g k₂ = q)
      (hc₁ : w₁ ≫ u k₁ = c₁) (hc₂ : w₂ ≫ u k₂ = c₂),
      E.hom q (i₁ := default) (i₂ := default) c₁ c₂
          (by rw [← hc₁, Category.assoc, hg, hw₁]) (by rw [← hc₂, Category.assoc, hg, hw₂]) =
        pullHom (eN.hom.hom k₁) w₁ c₁ w₁ hc₁ (Category.comp_id _) ≫
          D.hom q w₁ w₂ hw₁ hw₂ ≫
          pullHom (eN.inv.hom k₂) w₂ w₂ c₂ (Category.comp_id _) hc₂) :
    (abstractFamilyPullFunctor F w₀).obj E ≅ D :=
  Pseudofunctor.DescentData.isoMk (comparisonApp restrictW eN)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ comparisonApp_comm restrictW hg w₀ E eN hE q f₁ f₂ hf₁ hf₂)

end AbstractComparison

section SchemeComparison

variable {S Z : Scheme.{u}} {K : Type v} {X : K → Scheme.{u}} {b : Z ⟶ S}
  (u : ∀ k, X k ⟶ Z) [∀ k, IsOpenImmersion (u k)] (sqb : ChosenPullback b b)
  {g : ∀ k, X k ⟶ S} (hg : ∀ k, u k ≫ b = g k)
  (N : qcohPseudofunctor.{u}.obj (.mk (op Z)))
  (D : qcohPseudofunctor.{u}.DescentData g)
  (eN : (qcohPseudofunctor.toDescentData u).obj N ≅ (restrictFamilyFunctor b u g hg).obj D)

/-- **The comparison isomorphism of the family-to-singleton reduction.**  The descent datum
`Stacks.Descent.transitionDescentData` for the single morphism `b`, read back along the family,
is isomorphic to the descent datum `D` one started from. -/
def familyPullFunctorObjIso (hu : ⨆ k, (u k).opensRange = ⊤)
    (sq₃ : ChosenPullback₃ sqb sqb sqb) :
    (familyPullFunctor b u g hg).obj (transitionDescentData u sqb hg N D eN hu sq₃) ≅ D :=
  comparisonIso (restrictFamilyW u hg) hg (fun k ↦ by simpa using hg k) _ eN
    (fun _ q _ _ w₁ w₂ c₁ c₂ hw₁ hw₂ hc₁ hc₂ ↦
      transitionDescentData_hom u sqb hg N D eN hu sq₃ q w₁ w₂ c₁ c₂ hw₁ hw₂ hc₁ hc₂)

end SchemeComparison

section EssSurj

variable {S Z : Scheme.{u}} {K : Type v} {X : K → Scheme.{u}} {b : Z ⟶ S}
  {u : ∀ k, X k ⟶ Z} [∀ k, IsOpenImmersion (u k)]
  {g : ∀ k, X k ⟶ S} (hg : ∀ k, u k ≫ b = g k)

/-- **Essential surjectivity of the family-to-singleton comparison functor.**  Every descent
datum for a family `g` which is a Zariski open covering of an intermediate `Z` extends to a
descent datum for the single morphism `Z ⟶ S`. -/
theorem essSurj_familyPullFunctor (hu : ⨆ k, (u k).opensRange = ⊤) :
    (familyPullFunctor b u g hg).EssSurj where
  mem_essImage D := by
    obtain ⟨N, ⟨eN⟩⟩ := exists_iso_toDescentData_restrictFamilyFunctor hg hu D
    exact ⟨_, ⟨familyPullFunctorObjIso u (chosenPullbackOfHasPullback b b) hg N D eN hu
      (chosenPullback₃OfHasPullback _ _ _)⟩⟩

include hg in
/-- **The family-to-singleton reduction, essential surjectivity, with the comparison hypothesis
discharged.**  If the `u k` form a Zariski open covering of `Z` and every descent datum for the
single morphism `b` is effective, then every descent datum for the family `g` is effective. -/
theorem essSurj_qcohToDescentData_of_essSurj_single (hu : ⨆ k, (u k).opensRange = ⊤)
    (hb : (qcohPseudofunctor.toDescentData (fun _ : Unit ↦ b)).EssSurj) :
    (qcohPseudofunctor.toDescentData g).EssSurj :=
  essSurj_qcohToDescentData_of_essSurj_familyPullFunctor hg hb (essSurj_familyPullFunctor hg hu)

include hg in
/-- **The family-to-singleton reduction, with the comparison hypothesis discharged.**  For a
topology for which quasi-coherent modules form a prestack and for which the family is covering,
descent along the single morphism `b` alone gives descent along the family. -/
theorem isEquivalence_qcohToDescentData_of_essSurj_single
    {J : GrothendieckTopology Scheme.{u}} [qcohPseudofunctor.{u}.IsPrestack J]
    (hgJ : Sieve.ofArrows X g ∈ J S) (hu : ⨆ k, (u k).opensRange = ⊤)
    (hb : (qcohPseudofunctor.toDescentData (fun _ : Unit ↦ b)).EssSurj) :
    (qcohPseudofunctor.toDescentData g).IsEquivalence :=
  isEquivalence_qcohToDescentData_of_essSurj_familyPullFunctor hg hgJ hb
    (essSurj_familyPullFunctor hg hu)

end EssSurj

section Affine

variable {R : CommRingCat.{u}} {K : Type u} {A : K → CommRingCat.{u}}

/-- **The family-to-singleton comparison functor is essentially surjective for a finite family of
ring maps.** -/
theorem essSurj_familyPullFunctor_specMap [Finite K] (ρ : ∀ k, R ⟶ A k) :
    (familyPullFunctor (Spec.map (CommRingCat.ofHom (RingHom.pi fun k ↦ (ρ k).hom)))
      (fun k ↦ Spec.map (piComponent A k)) (fun k ↦ Spec.map (ρ k))
      (specMap_piComponent_comp ρ)).EssSurj :=
  essSurj_familyPullFunctor _ (iSup_opensRange_specMap_piComponent A)

/-- **The essential-surjectivity half of Stacks 023S, reduced to the single morphism
`Spec (∏ₖ A k) ⟶ Spec R`.**  If every descent datum for that one morphism is effective, then
every descent datum for the family `Spec (A k) ⟶ Spec R` is effective. -/
theorem essSurj_qcohToDescentData_specMap [Finite K] (ρ : ∀ k, R ⟶ A k)
    (hb : (qcohPseudofunctor.toDescentData
      (fun _ : Unit ↦ Spec.map (CommRingCat.ofHom (RingHom.pi fun k ↦ (ρ k).hom)))).EssSurj) :
    (qcohPseudofunctor.toDescentData (fun k ↦ Spec.map (ρ k))).EssSurj :=
  essSurj_qcohToDescentData_specMap_of_essSurj_familyPullFunctor ρ hb
    (essSurj_familyPullFunctor_specMap ρ)

/-- **Stacks 023S over `Spec R`, reduced to descent along the single morphism
`Spec (∏ₖ A k) ⟶ Spec R`.**  If quasi-coherent modules form an fpqc prestack, the family
`Spec (A k) ⟶ Spec R` is an fpqc covering and every descent datum for that one morphism is
effective, then pullback along the family is an equivalence onto descent data. -/
theorem isEquivalence_qcohToDescentData_specMap
    [qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u}] [Finite K] (ρ : ∀ k, R ⟶ A k)
    (hmem : Presieve.ofArrows (fun k ↦ Spec (A k)) (fun k ↦ Spec.map (ρ k)) ∈
      Scheme.fpqcPrecoverage.{u} (Spec R))
    (hb : (qcohPseudofunctor.toDescentData
      (fun _ : Unit ↦ Spec.map (CommRingCat.ofHom (RingHom.pi fun k ↦ (ρ k).hom)))).EssSurj) :
    (qcohPseudofunctor.toDescentData (fun k ↦ Spec.map (ρ k))).IsEquivalence :=
  isEquivalence_qcohToDescentData_specMap_of_essSurj_familyPullFunctor ρ hmem hb
    (essSurj_familyPullFunctor_specMap ρ)

end Affine

end Stacks.Descent

end

end
