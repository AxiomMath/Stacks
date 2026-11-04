module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitFirstVariableSequence
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitRepresentable
public import StacksFrontier.Homology.Ext.MapExactFunctorTransport

/-!
# Morphisms, short exact sequences and splittings of pullback first variables

Let `D` be an inverse system of sites with finite coverings with colimit site `C`. A morphism
`g : P ⟶ P'` of abelian sheaves on the level `i` induces a morphism of the pullback first
variables; a short exact sequence of abelian sheaves on the level `i` induces a short exact
sequence of pullback first variables, the inverse images being exact; and a splitting of a sheaf
as a direct sum of two splits its pullback first variable. An isomorphism of sheaves on the level
transfers the `Ext` colimit property.

Corepresenting sections transport along an isomorphism of objects and along a functor inducing an
equivalence of sheaf categories.

## Main definitions

* `Stacks.WeakSites.ExtColimit.pullbackFirstVariableHom`: The morphism of pullback first variables
  induced by a morphism of abelian sheaves on a level.
* `Stacks.WeakSites.ExtColimit.pullbackFirstVariableShortExact`: The short exact sequence of
  pullback first variables induced by a short exact sequence of abelian sheaves on a level.
* `Stacks.WeakSites.ExtColimit.pullbackFirstVariableSplit`: The splitting of a pullback first
  variable induced by a splitting of an abelian sheaf on a level as a direct sum.

## Main results

* `Stacks.WeakSites.ExtColimit.IsCorepresentingSection.ofIso`: Corepresenting sections transport
  along an isomorphism of objects.
* `Stacks.WeakSites.ExtColimit.IsCorepresentingSection.pushforward_of_isEquivalence`: Restriction
  along a functor inducing an equivalence of sheaf categories preserves corepresenting sections.
* `Stacks.WeakSites.ExtColimit.nonempty_isColimit_of_iso`: An isomorphism of abelian sheaves on a
  level transfers the `Ext` colimit property of their pullback first variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w w₁ w₂ w₃ w₄ w₅ jv ju tv tu y z

namespace CategoryTheory.PushforwardCocone

variable {J : Type ju} [Category.{jv} J] {T : J → Type tu} [∀ i, Category.{tv} (T i)]
  {S : Type y} [Category.{z} S]

/-- Transposing the unit followed by a comparison `ε` is natural in the object. -/
private theorem homEquiv_symm_unit_comp_naturality {X Y Z : Type*} [Category X] [Category Y]
    [Category Z] {L : X ⥤ Y} {R : Y ⥤ X} {L₁ : X ⥤ Z} {R₁ : Z ⥤ X} {Q : Z ⥤ Y} (adj : L ⊣ R)
    (adj₁ : L₁ ⊣ R₁) (ε : R₁ ⟶ Q ⋙ R) {F F' : X} (g : F ⟶ F') :
    L.map g ≫ (adj.homEquiv F' _).symm (adj₁.unit.app F' ≫ ε.app (L₁.obj F')) =
      (adj.homEquiv F _).symm (adj₁.unit.app F ≫ ε.app (L₁.obj F)) ≫ Q.map (L₁.map g) := by
  apply (adj.homEquiv F _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.assoc]
  have h₁ := ε.naturality (L₁.map g)
  dsimp only [Functor.comp_map] at h₁
  rw [← h₁, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (adj₁.unit_naturality g).symm

/-- **The transition map of the system of inverse images is natural** in the sheaf. -/
theorem transitionPushforward_naturality {P : ∀ {i j : J}, (i ⟶ j) → (T i ⥤ T j)}
    {L : ∀ i, S ⥤ T i} {R : ∀ i, T i ⥤ S} (adj : ∀ i, L i ⊣ R i)
    (e : ∀ {i j : J} (a : i ⟶ j), P a ⋙ R j ≅ R i) {F F' : S} (g : F ⟶ F') {i j : J}
    (a : i ⟶ j) :
    (L j).map g ≫ transitionPushforward adj e F' a =
      transitionPushforward adj e F a ≫ (P a).map ((L i).map g) :=
  homEquiv_symm_unit_comp_naturality (adj j) (adj i) (e a).inv g

end CategoryTheory.PushforwardCocone

namespace Stacks.WeakSites.ExtColimit

open InverseSystemOfFiniteSites Stacks.Homology Stacks.WeakSites.ColimitSiteCohomology

section Corepresenting

/-- **Corepresenting sections transport along an isomorphism of objects.** -/
theorem IsCorepresentingSection.ofIso {𝒞 : Type w₁} [Category.{w₂} 𝒞] {J : GrothendieckTopology 𝒞}
    {P : Sheaf J AddCommGrpCat.{w₃}} {X X' : 𝒞} {s : P.obj.obj (op X)}
    (hs : IsCorepresentingSection P X s) (e : X ≅ X') :
    IsCorepresentingSection P X' (P.obj.map e.inv.op s) := by
  intro M
  have h : (fun h : P ⟶ M => h.hom.app (op X') (P.obj.map e.inv.op s)) =
      (M.obj.map e.inv.op) ∘ (fun h : P ⟶ M => h.hom.app (op X) s) := by
    funext h
    exact ConcreteCategory.congr_hom (h.hom.naturality e.inv.op) s
  rw [h]
  refine Function.Bijective.comp ?_ (hs M)
  refine ⟨fun a b hab => ?_, fun b => ⟨M.obj.map e.hom.op b, ?_⟩⟩
  · have := congrArg (M.obj.map e.hom.op) hab
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e.hom_inv_id,
      op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using this
  · simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e.inv_hom_id,
      op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- **Restriction along a functor which induces an equivalence of sheaf categories carries a
sheaf corepresenting the sections over the image of an object to a sheaf corepresenting the
sections over the object**, with the same section. -/
theorem IsCorepresentingSection.pushforward_of_isEquivalence {𝒜 : Type w₁} {ℬ : Type w₄}
    [Category.{w₂} 𝒜] [Category.{w₅} ℬ] {JA : GrothendieckTopology 𝒜}
    {JB : GrothendieckTopology ℬ} (G : 𝒜 ⥤ ℬ) [G.IsContinuous JA JB]
    [(G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB).IsEquivalence]
    {P : Sheaf JB AddCommGrpCat.{w₃}} {X : 𝒜} {s : P.obj.obj (op (G.obj X))}
    (hs : IsCorepresentingSection P (G.obj X) s) :
    IsCorepresentingSection ((G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB).obj P) X
      s := by
  intro M
  let Φ := G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB
  let e : Φ.obj (Φ.objPreimage M) ≅ M := Φ.objObjPreimageIso M
  let s' : (Φ.obj P).obj.obj (op X) := s
  have hiso : IsIso (e.hom.hom.app (op X)) := by
    have : IsIso e.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf JA _).map e.hom))
    infer_instance
  have h : (fun h : Φ.obj P ⟶ M => h.hom.app (op X) s') =
      (e.hom.hom.app (op X)) ∘ (fun g : P ⟶ Φ.objPreimage M => g.hom.app (op (G.obj X)) s) ∘
        (fun h : Φ.obj P ⟶ M => Φ.preimage (h ≫ e.inv)) := by
    funext h
    simp only [Function.comp_apply]
    change _ = (e.hom.hom.app (op X)) ((Φ.map (Φ.preimage (h ≫ e.inv))).hom.app (op X) s')
    rw [Functor.map_preimage, ← sheafHom_comp_apply, Category.assoc, e.inv_hom_id,
      Category.comp_id]
  change Function.Bijective (fun h : Φ.obj P ⟶ M => h.hom.app (op X) s')
  rw [h]
  refine Function.Bijective.comp (ConcreteCategory.bijective_of_isIso _)
    (Function.Bijective.comp (hs _) ?_)
  refine ⟨fun a b hab => ?_, fun g => ⟨Φ.map g ≫ e.hom, ?_⟩⟩
  · have := congrArg (fun k => Φ.map k ≫ e.hom) hab
    simpa only [Functor.map_preimage, Category.assoc, e.inv_hom_id, Category.comp_id] using this
  · simp only [Category.assoc, e.hom_inv_id, Category.comp_id, Functor.preimage_map]

/-- The morphism out of a corepresenting sheaf sending its section to a given section. -/
def IsCorepresentingSection.desc {𝒞 : Type w₁} [Category.{w₂} 𝒞] {J : GrothendieckTopology 𝒞}
    {P : Sheaf J AddCommGrpCat.{w₃}} {X : 𝒞} {s : P.obj.obj (op X)}
    (hs : IsCorepresentingSection P X s) {M : Sheaf J AddCommGrpCat.{w₃}} (t : M.obj.obj (op X)) :
    P ⟶ M :=
  ((Equiv.ofBijective _ (hs M)).symm t)

/-- The morphism `hs.desc t` sends the corepresenting section `s` to `t`. -/
theorem IsCorepresentingSection.desc_apply {𝒞 : Type w₁} [Category.{w₂} 𝒞]
    {J : GrothendieckTopology 𝒞} {P : Sheaf J AddCommGrpCat.{w₃}} {X : 𝒞} {s : P.obj.obj (op X)}
    (hs : IsCorepresentingSection P X s) {M : Sheaf J AddCommGrpCat.{w₃}} (t : M.obj.obj (op X)) :
    (hs.desc t).hom.app (op X) s = t :=
  (Equiv.ofBijective _ (hs M)).apply_symm_apply t

/-- **Morphisms out of a corepresenting sheaf are determined by the image of the section.** -/
theorem IsCorepresentingSection.hom_ext {𝒞 : Type w₁} [Category.{w₂} 𝒞]
    {J : GrothendieckTopology 𝒞} {P : Sheaf J AddCommGrpCat.{w₃}} {X : 𝒞} {s : P.obj.obj (op X)}
    (hs : IsCorepresentingSection P X s) {M : Sheaf J AddCommGrpCat.{w₃}} {φ ψ : P ⟶ M}
    (h : φ.hom.app (op X) s = ψ.hom.app (op X) s) : φ = ψ :=
  (hs M).1 h

/-- **The isomorphism of two sheaves corepresenting the sections over one object**, matching
their sections. -/
def IsCorepresentingSection.isoOfCorep {𝒞 : Type w₁} [Category.{w₂} 𝒞]
    {J : GrothendieckTopology 𝒞} {P Q : Sheaf J AddCommGrpCat.{w₃}} {X : 𝒞}
    {s : P.obj.obj (op X)} {t : Q.obj.obj (op X)} (hs : IsCorepresentingSection P X s)
    (ht : IsCorepresentingSection Q X t) : P ≅ Q where
  hom := hs.desc t
  inv := ht.desc s
  hom_inv_id := hs.hom_ext (by
    rw [sheafHom_comp_apply, hs.desc_apply, ht.desc_apply]
    rfl)
  inv_hom_id := ht.hom_ext (by
    rw [sheafHom_comp_apply, ht.desc_apply, hs.desc_apply]
    rfl)

/-- The isomorphism `hs.isoOfCorep ht` sends the section `s` to the section `t`. -/
theorem IsCorepresentingSection.isoOfCorep_hom_apply {𝒞 : Type w₁} [Category.{w₂} 𝒞]
    {J : GrothendieckTopology 𝒞} {P Q : Sheaf J AddCommGrpCat.{w₃}} {X : 𝒞}
    {s : P.obj.obj (op X)} {t : Q.obj.obj (op X)} (hs : IsCorepresentingSection P X s)
    (ht : IsCorepresentingSection Q X t) :
    (hs.isoOfCorep ht).hom.hom.app (op X) s = t :=
  hs.desc_apply t

/-- **The inverse transpose under an inverse image, on the image of a section under the unit.** -/
theorem homEquiv_symm_hom_app_unit_apply {𝒜 : Type w₁} {ℬ : Type w₄} [Category.{w₂} 𝒜]
    [Category.{w₅} ℬ] {JA : GrothendieckTopology 𝒜} {JB : GrothendieckTopology ℬ} (G : 𝒜 ⥤ ℬ)
    [G.IsContinuous JA JB] {L : Sheaf JA AddCommGrpCat.{w₃} ⥤ Sheaf JB AddCommGrpCat.{w₃}}
    (adj : L ⊣ G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB)
    {P : Sheaf JA AddCommGrpCat.{w₃}} {M : Sheaf JB AddCommGrpCat.{w₃}}
    (ψ : P ⟶ (G.sheafPushforwardContinuous AddCommGrpCat.{w₃} JA JB).obj M) {X : 𝒜}
    (x : P.obj.obj (op X)) :
    ((adj.homEquiv P M).symm ψ).hom.app (op (G.obj X)) ((adj.unit.app P).hom.app (op X) x) =
      ψ.hom.app (op X) x := by
  rw [← homEquiv_hom_app_apply G adj, Equiv.apply_symm_apply]

end Corepresenting

variable {D : InverseSystemOfFiniteSites.{v, u, max u v w}}
  {C : Type (max u v w)} [SmallCategory C]
  {uC : ∀ i, D.C i ⥤ C} {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
  {K : Precoverage C} [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]

section PullbackHom

variable [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  {i : D.I} {P P' : Sheaf (D.J i) Ab.{max u v w}} (g : P ⟶ P')

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] in
/-- The transition of the pullback first variable is natural in the sheaf. -/
theorem overTransition_naturality {A B : Over i} (f : A ⟶ B) :
    (pb.{v, u, w} D B.hom).map g ≫ overTransition D P' f =
      overTransition D P f ≫ (abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left).map
        ((pb.{v, u, w} D A.hom).map g) :=
  CategoryTheory.PushforwardCocone.transitionPushforward_naturality
    (P := fun {A B : Over i} (f : A ⟶ B) =>
      abelianSheafPushforward.{v, u, max u v w, max u v w} D f.left)
    (fun A => abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)
    (fun f => overPushforwardIso D f) g f

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] in
/-- The leg of the pullback first variable is natural in the sheaf. -/
theorem overLeg_naturality (A : Over i) :
    (pb.{v, u, w} D A.hom).map g ≫ overLeg D uC hu K P' A =
      overLeg D uC hu K P A ≫ (colimitPushforward.{v, u, w} D uC K A.left).map
        ((colimitPullback.{v, u, w} D uC K i).map g) :=
  CategoryTheory.PushforwardCocone.homEquiv_symm_unit_comp_naturality
    (abelianSheafAdjunction.{v, u, max u v w, max u v w} D A.hom)
    (colimitAdj.{v, u, w} D uC K i)
    (colimitPushforwardCompIso.{v, u, w} D uC hu K A.hom).inv g

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] in
/-- The transition isomorphism `ψ` of the pullback first variable is natural in the sheaf. -/
theorem ψ_pullbackFirstVariable_naturality {A B : Over i} (f : A ⟶ B) :
    (pullbackFirstVariable D uC hu K P).ψ f ≫ (pb.{v, u, w} D A.hom).map g =
      (pb.{v, u, w} D f.left).map ((pb.{v, u, w} D B.hom).map g) ≫
        (pullbackFirstVariable D uC hu K P').ψ f :=
  (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans
    ((congrArg ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left).homEquiv _ _).symm
      (overTransition_naturality g f).symm).trans
      (Adjunction.homEquiv_naturality_left_symm _ _ _))

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] in
/-- The inverse leg `legInv` of the pullback first variable is natural in the sheaf. -/
theorem legInv_pullbackFirstVariable_naturality (A : Over i) :
    (colimitPullback.{v, u, w} D uC K A.left).map ((pb.{v, u, w} D A.hom).map g) ≫
        (pullbackFirstVariable D uC hu K P').legInv A =
      (pullbackFirstVariable D uC hu K P).legInv A ≫ (colimitPullback.{v, u, w} D uC K i).map g :=
  (Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans
    ((congrArg ((colimitAdj.{v, u, w} D uC K A.left).homEquiv _ _).symm
      (overLeg_naturality (uC := uC) (hu := hu) (K := K) g A)).trans
      (Adjunction.homEquiv_naturality_right_symm _ _ _))

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] in
/-- If `ψ ≫ a = b ≫ ψ'` with `ψ` and `ψ'` isomorphisms, then `a ≫ inv ψ' = inv ψ ≫ b`. -/
theorem comp_inv_eq_inv_comp_of {𝒞 : Type*} [Category 𝒞] {X Y X' Y' : 𝒞} (ψ : X ⟶ Y)
    (ψ' : X' ⟶ Y') [IsIso ψ] [IsIso ψ'] (a : Y ⟶ Y') (b : X ⟶ X') (h : ψ ≫ a = b ≫ ψ') :
    a ≫ inv ψ' = inv ψ ≫ b := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The morphism of pullback first variables** induced by a morphism of abelian sheaves on the
level. -/
def pullbackFirstVariableHom :
    FirstVariable.Hom (pullbackFirstVariable D uC hu K P) (pullbackFirstVariable D uC hu K P') where
  app A := (pb.{v, u, w} D A.hom).map g
  top := (colimitPullback.{v, u, w} D uC K i).map g
  comm f := comp_inv_eq_inv_comp_of _ _ _ _ (ψ_pullbackFirstVariable_naturality g f)
  top_comm A := comp_inv_eq_inv_comp_of _ _ _ _
    (legInv_pullbackFirstVariable_naturality g A).symm

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] in
/-- The component of `pullbackFirstVariableHom g` at `A` is the inverse image of `g`. -/
@[simp]
theorem pullbackFirstVariableHom_app (A : Over i) :
    (pullbackFirstVariableHom (uC := uC) (hu := hu) (K := K) g).app A =
      (pb.{v, u, w} D A.hom).map g := rfl

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] in
/-- The top component of `pullbackFirstVariableHom g` is the inverse image of `g` to the colimit
site. -/
@[simp]
theorem pullbackFirstVariableHom_top :
    (pullbackFirstVariableHom (uC := uC) (hu := hu) (K := K) g).top =
      (colimitPullback.{v, u, w} D uC K i).map g := rfl

end PullbackHom

section Sequences

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
/-- A functor carries a pair of morphisms with `a ≫ b = 𝟙 X` to a pair with the same property. -/
theorem map_comp_eq_id' {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞}
    (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) : F.map a ≫ F.map b = 𝟙 (F.obj X) := by
  rw [← F.map_comp, h, F.map_id]

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
/-- An additive functor carries a pair of morphisms with zero composite to a pair with zero
composite. -/
theorem map_comp_eq_zero' {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒞]
    [Preadditive 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive] {X Y Z : 𝒞} (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : a ≫ b = 0) : F.map a ≫ F.map b = 0 := by
  rw [← F.map_comp, h, F.map_zero]

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
/-- An additive functor preserves the identity `p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 X`. -/
theorem map_total_eq' {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒞] [Preadditive 𝒟]
    (F : 𝒞 ⥤ 𝒟) [F.Additive] {X Y₁ Y₂ : 𝒞} (p₁ : X ⟶ Y₁) (i₁ : Y₁ ⟶ X) (p₂ : X ⟶ Y₂)
    (i₂ : Y₂ ⟶ X) (ht : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 X) :
    F.map p₁ ≫ F.map i₁ + F.map p₂ ≫ F.map i₂ = 𝟙 (F.obj X) := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, ht, F.map_id]

variable [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)] {i : D.I}

/-- **A short exact sequence of abelian sheaves on a level gives a short exact sequence of pullback
first variables**: the inverse images to the levels below and to the colimit site are exact. -/
def pullbackFirstVariableShortExact (S : ShortComplex (Sheaf (D.J i) Ab.{max u v w}))
    (hS : S.ShortExact) :
    FirstVariable.ShortExact (pullbackFirstVariable D uC hu K S.X₁)
      (pullbackFirstVariable D uC hu K S.X₂) (pullbackFirstVariable D uC hu K S.X₃) where
  φ := pullbackFirstVariableHom S.f
  π := pullbackFirstVariableHom S.g
  w A := by
    change (pb.{v, u, w} D A.hom).map S.f ≫ (pb.{v, u, w} D A.hom).map S.g = 0
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  w_top := by
    change (colimitPullback.{v, u, w} D uC K i).map S.f ≫
      (colimitPullback.{v, u, w} D uC K i).map S.g = 0
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  shortExact A := hS.map_of_exact (pb.{v, u, w} D A.hom)
  shortExact_top := hS.map_of_exact (colimitPullback.{v, u, w} D uC K i)

/-- **A splitting of an abelian sheaf on a level as a direct sum of two splits its pullback first
variable.** The splitting is given in the bicone sense, by four morphisms and five identities. -/
def pullbackFirstVariableSplit {P₁ P₂ P : Sheaf (D.J i) Ab.{max u v w}} (i₁ : P₁ ⟶ P)
    (i₂ : P₂ ⟶ P) (p₁ : P ⟶ P₁) (p₂ : P ⟶ P₂) (h₁ : i₁ ≫ p₁ = 𝟙 _) (h₂ : i₂ ≫ p₂ = 𝟙 _)
    (h₁₂ : i₁ ≫ p₂ = 0) (h₂₁ : i₂ ≫ p₁ = 0) (ht : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 _) :
    FirstVariable.Split (pullbackFirstVariable D uC hu K P₁) (pullbackFirstVariable D uC hu K P₂)
      (pullbackFirstVariable D uC hu K P) where
  inl := pullbackFirstVariableHom i₁
  inr := pullbackFirstVariableHom i₂
  fst := pullbackFirstVariableHom p₁
  snd := pullbackFirstVariableHom p₂
  inl_fst _ := map_comp_eq_id' _ _ _ h₁
  inr_snd _ := map_comp_eq_id' _ _ _ h₂
  inl_snd _ := map_comp_eq_zero' _ _ _ h₁₂
  inr_fst _ := map_comp_eq_zero' _ _ _ h₂₁
  total _ := map_total_eq' _ _ _ _ _ ht
  inl_fst_top := map_comp_eq_id' _ _ _ h₁
  inr_snd_top := map_comp_eq_id' _ _ _ h₂
  inl_snd_top := map_comp_eq_zero' _ _ _ h₁₂
  inr_fst_top := map_comp_eq_zero' _ _ _ h₂₁
  total_top := map_total_eq' _ _ _ _ _ ht

end Sequences

section Transfer

open FirstVariable.ShortExact

variable [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]

variable {i : D.I} {𝒜 𝒜' : FirstVariable.{v, u, w} D uC hu K i}
  (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
  {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (n : ℕ) (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι)

/-- **Mutually inverse morphisms of first variables transfer the `Ext` colimit property.** -/
theorem FirstVariable.Hom.nonempty_isColimit_of_inverse (h : FirstVariable.Hom 𝒜 𝒜')
    (h' : FirstVariable.Hom 𝒜' 𝒜) (e₁ : ∀ A, h.app A ≫ h'.app A = 𝟙 _)
    (e₂ : ∀ A, h'.app A ≫ h.app A = 𝟙 _) (t₁ : h.top ≫ h'.top = 𝟙 _)
    (t₂ : h'.top ≫ h.top = 𝟙 _)
    (H : Nonempty (IsColimit (extCocone 𝒜 F ι n @hι))) :
    Nonempty (IsColimit (extCocone 𝒜' F ι n @hι)) := by
  obtain ⟨H⟩ := H
  let α : extDiagram 𝒜' F n ≅ extDiagram 𝒜 F n :=
    { hom := precompNat F n h
      inv := precompNat F n h'
      hom_inv_id := precompNat_comp_eq_id F n h' h e₂
      inv_hom_id := precompNat_comp_eq_id F n h h' e₁ }
  have key : ∀ (A : Over i) (x : Ext.{max u v w} (𝒜'.obj A) (F.obj A.left) n),
      (Ext.mk₀ h'.top).comp (extLeg 𝒜 F ι n A ((Ext.mk₀ (h.app A)).comp x (zero_add n)))
        (zero_add n) = extLeg 𝒜' F ι n A x := by
    intro A x
    rw [extLeg_precomp F ι n h A x, mk₀_comp_mk₀_comp n _ _ _ t₂, Ext.mk₀_id_comp]
  let β : AddCommGrpCat.of (Ext.{max u v w} 𝒜.top 𝒢 n) ≅
      AddCommGrpCat.of (Ext.{max u v w} 𝒜'.top 𝒢 n) :=
    { hom := precompTop (𝒢 := 𝒢) n h'
      inv := precompTop (𝒢 := 𝒢) n h
      hom_inv_id := by
        ext x
        exact (mk₀_comp_mk₀_comp n _ _ _ t₁ x).trans (Ext.mk₀_id_comp x)
      inv_hom_id := by
        ext x
        exact (mk₀_comp_mk₀_comp n _ _ _ t₂ x).trans (Ext.mk₀_id_comp x) }
  refine ⟨IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α _).symm H)
    (Cocones.ext β (fun A => ?_))⟩
  ext x
  exact key A.unop x

/-- A zero vertex of the `Ext` cocone is a vanishing `Ext` group. -/
theorem subsingleton_ext_of_isZero_extCocone_pt (h : IsZero (extCocone 𝒜 F ι n @hι).pt) :
    Subsingleton (Ext.{max u v w} 𝒜.top 𝒢 n) :=
  AddCommGrpCat.isZero_iff_subsingleton.1 h

/-- **A zero vertex of the `Ext` cocone, read through an equivalence.** If the vertex
`Ext^n(𝒜_∞, 𝒢)` of the `Ext` cocone is zero and `R` is an equivalence onto the abelian sheaves of
the colimit site carrying `Z` to `𝒜_∞` and `G` to `𝒢`, then `Ext^n(Z, G) = 0`. -/
theorem subsingleton_ext_of_isZero_extCocone_pt_of_equivalence
    (h : IsZero (extCocone 𝒜 F ι n @hι).pt) {𝒞' : Type w₁} [Category.{w₂} 𝒞'] {_ : Abelian 𝒞'}
    {_ : HasExt.{w₃} 𝒞'} [EnoughInjectives 𝒞']
    [EnoughInjectives (Sheaf K.toGrothendieck Ab.{max u v w})]
    (R : 𝒞' ⥤ Sheaf K.toGrothendieck Ab.{max u v w}) (hR : R.IsEquivalence) {Z G : 𝒞'}
    (eZ : R.obj Z ≅ 𝒜.top) (eG : R.obj G ≅ 𝒢) : Subsingleton (Ext.{w₃} Z G n) :=
  (subsingleton_ext_iff_of_isEquivalence R hR Z G n).2
    (subsingleton_ext_of_iso eZ eG (subsingleton_ext_of_isZero_extCocone_pt F ι n hι h))

/-- **An isomorphism of abelian sheaves on a level transfers the `Ext` colimit property of their
pullback first variables.** -/
theorem nonempty_isColimit_of_iso {P P' : Sheaf (D.J i) Ab.{max u v w}} (e : P ≅ P')
    (H : Nonempty (IsColimit (extCocone (pullbackFirstVariable D uC hu K P) F ι n @hι))) :
    Nonempty (IsColimit (extCocone (pullbackFirstVariable D uC hu K P') F ι n @hι)) :=
  FirstVariable.Hom.nonempty_isColimit_of_inverse F ι n hι (pullbackFirstVariableHom e.hom)
    (pullbackFirstVariableHom e.inv)
    (fun _ => map_comp_eq_id' _ _ _ e.hom_inv_id)
    (fun _ => map_comp_eq_id' _ _ _ e.inv_hom_id)
    (map_comp_eq_id' _ _ _ e.hom_inv_id) (map_comp_eq_id' _ _ _ e.inv_hom_id) H

end Transfer

end Stacks.WeakSites.ExtColimit

end
