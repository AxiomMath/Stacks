module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact

/-!
# Exactness of the Picard sequence at `Pic(X_T)`

Let `f : X ⟶ S` be a morphism of a big fppf site whose comparison map `𝒪_T ⟶ f_{T,*}𝒪_{X_T}`
is an isomorphism for every `S`-scheme `T` of the site. A Picard class of `X_T` that dies in
`Pic_{X/S}(T)` is then pulled back from `Pic(T)`: the sequence

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T)`

is exact at `Pic(X_T)`. Together with
`Stacks.PicardFunctor.injective_schemePullbackClass_baseChangeProj` this is the whole of Tag 0B9M.

## Main results

* `Stacks.Picard.nonempty_iso_of_normalizedDatum` — a family of trivialisations of an object `N`
  over `P.obj T` along a natural transformation `s : P ⟶ Q` determines a descent datum downstairs,
  and an object whose canonical descent datum is isomorphic to it pulls back to `N`.
* `Stacks.PicardFunctor.exists_schemePullbackClass_baseChangeProj_eq` — a Picard class of `X_T`
  trivial on the base changes of a covering family of `T` is pulled back from `Pic(T)`.
* `Stacks.PicardFunctor.exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom_of_isIso_c`
  — exactness at `Pic(X_T)` of the Picard sequence.

## References

* [Stacks Project, Tag 0B9M](https://stacks.math.columbia.edu/tag/0B9M)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Picard

/-- Bijectivity of the action of a functor on the endomorphisms of an object extends to the
homomorphisms between any two objects isomorphic to it. -/
theorem bijective_map_of_iso_pair {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B L : C} (e₁ : A ≅ L) (e₂ : B ≅ L)
    (h : Function.Bijective (F.map : (L ⟶ L) → (F.obj L ⟶ F.obj L))) :
    Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B)) := by
  have key : (Iso.homCongr (F.mapIso e₁) (F.mapIso e₂)) ∘ (F.map : (A ⟶ B) → _) =
      (F.map : (L ⟶ L) → _) ∘ (Iso.homCongr e₁ e₂) := by
    funext a
    simp [Iso.homCongr_apply]
  have hb : Function.Bijective
      ((Iso.homCongr (F.mapIso e₁) (F.mapIso e₂)) ∘ (F.map : (A ⟶ B) → _)) := by
    rw [key]
    exact h.comp (Iso.homCongr e₁ e₂).bijective
  exact ((Iso.homCongr (F.mapIso e₁) (F.mapIso e₂)).bijective.of_comp_iff' _).mp hb

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- **Restriction along a morphism with invariant structure sheaf is bijective on the homomorphisms
between two pullbacks of structure sheaves.** -/
theorem bijective_pullHom_proj {V Z₁ Z₂ Y : Scheme.{u}} (a : V ⟶ Z₁) (b : V ⟶ Z₂)
    (p : Y ⟶ V) (hp : IsIso p.toLRSHom.toHom.c) :
    Function.Bijective (fun φ :
      (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj
          (SheafOfModules.unit Z₁.ringCatSheaf) ⟶
        (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.obj
          (SheafOfModules.unit Z₂.ringCatSheaf) =>
      pullHom φ p (p ≫ a) (p ≫ b) rfl rfl) := by
  have := hp
  refine bijective_pullHom (F := modulePullbackPseudofunctor) p (p ≫ a) (p ≫ b) rfl rfl ?_
  exact bijective_map_of_iso_pair (Scheme.Modules.pullback p)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso a)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso b)
    (bijective_modulePullback_map_unit p)

/-- The components of an isomorphism of descent data. -/
def descentDataIsoApp {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {ι : Type*} {S : C} {Z : ι → C}
    {u : ∀ i, Z i ⟶ S} {D₁ D₂ : F.DescentData u} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by
    rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id, Pseudofunctor.DescentData.id_hom]
  inv_hom_id := by
    rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id, Pseudofunctor.DescentData.id_hom]

/-- **An isomorphism of the associated descent data is an isomorphism**, as soon as pulling
morphisms back to the family is bijective on the four relevant hom-sets. -/
theorem nonempty_iso_of_toDescentData_iso {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {ι : Type*} {S : C} {Z : ι → C}
    (u : ∀ i, Z i ⟶ S) {M M' : F.obj (.mk (Opposite.op S))}
    (hMN : Function.Bijective ((F.toDescentData u).map : (M ⟶ M') → _))
    (hNM : Function.Bijective ((F.toDescentData u).map : (M' ⟶ M) → _))
    (hMM : Function.Bijective ((F.toDescentData u).map : (M ⟶ M) → _))
    (hNN : Function.Bijective ((F.toDescentData u).map : (M' ⟶ M') → _))
    (e : (F.toDescentData u).obj M ≅ (F.toDescentData u).obj M') :
    Nonempty (M ≅ M') := by
  obtain ⟨φ, hφ⟩ := hMN.surjective e.hom
  obtain ⟨φ', hφ'⟩ := hNM.surjective e.inv
  refine ⟨⟨φ, φ', hMM.injective ?_, hNN.injective ?_⟩⟩
  · rw [CategoryTheory.Functor.map_comp, hφ, hφ', e.hom_inv_id,
      CategoryTheory.Functor.map_id]
  · rw [CategoryTheory.Functor.map_comp, hφ, hφ', e.inv_hom_id,
      CategoryTheory.Functor.map_id]

section Normalized

open Pseudofunctor.LocallyDiscreteOpToCat

universe v' u' w z v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {D : Type w} [Category.{z} D] (P Q : D ⥤ C) (s : P ⟶ Q)
  {I : Type*} {T : D} {U : I → D} {g : ∀ i, U i ⟶ T}
  (sq : ∀ i j, ChosenPullback (g i) (g j))
  (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
  (hQ : ∀ i j, IsPullback (Q.map (sq i j).p₁) (Q.map (sq i j).p₂)
    (Q.map (g i)) (Q.map (g j)))
  (hQ₃ : ∀ i j k, IsPullback (Q.map (sq₃ i j k).p₁₂) (Q.map (sq₃ i j k).p₂₃)
    (Q.map (sq i j).p₂) (Q.map (sq j k).p₁))
  (L : ∀ i, F.obj (.mk (.op (Q.obj (U i)))))
  (N : F.obj (.mk (.op (P.obj T))))
  (α : ∀ i, (F.map (s.app (U i)).op.toLoc).toFunctor.obj (L i) ≅
    (F.map (P.map (g i)).op.toLoc).toFunctor.obj N)
  (β : ∀ {V : D} (q : V ⟶ T) {i j : I} (a : V ⟶ U i) (b : V ⟶ U j),
    a ≫ g i = q → b ≫ g j = q →
    Function.Bijective (fun φ :
      (F.map (Q.map a).op.toLoc).toFunctor.obj (L i) ⟶
        (F.map (Q.map b).op.toLoc).toFunctor.obj (L j) =>
      pullHom φ (s.app V) (s.app V ≫ Q.map a) (s.app V ≫ Q.map b) rfl rfl))

/-- **The descent datum of a normalised family of trivialisations**, in the presentation by
transition morphisms over chosen fibre products: the components are the `L i` and the
transition over `U i ×_T U j` is the normalised comparison of the trivialisations `α` of the
object `N` upstairs. -/
@[reducible] noncomputable def normalizedDatum' :
    F.DescentData' (fun i j => mapChosenPullback Q (sq i j) (hQ i j))
      (mapChosenPullback₃ Q sq sq₃ hQ hQ₃) where
  obj := L
  hom i j := normalizedHom P Q s g L N α β (sq i j).p (sq i j).p₁ (sq i j).p₂
    (sq i j).hp₁ (sq i j).hp₂
  pullHom'_hom_self i :=
    (diagramDescentData Q sq sq₃ hQ hQ₃ L
      (fun {_} q {_ _} a b ha hb => normalizedHom P Q s g L N α β q a b ha hb)
      (fun {_} q {_} a ha => normalizedHom_self P Q s g L N α β q a ha)
      (fun {_} q {_ _ _} a b c ha hb hc => normalizedHom_comp P Q s g L N α β q a b c ha hb hc)
      (fun {_ _} r q {_ _} a b ha hb =>
        normalizedHom_pull P Q s g L N α β r q a b ha hb)).pullHom'_hom_self i
  pullHom'_hom_comp i j k :=
    (diagramDescentData Q sq sq₃ hQ hQ₃ L
      (fun {_} q {_ _} a b ha hb => normalizedHom P Q s g L N α β q a b ha hb)
      (fun {_} q {_} a ha => normalizedHom_self P Q s g L N α β q a ha)
      (fun {_} q {_ _ _} a b c ha hb hc => normalizedHom_comp P Q s g L N α β q a b c ha hb hc)
      (fun {_ _} r q {_ _} a b ha hb =>
        normalizedHom_pull P Q s g L N α β r q a b ha hb)).pullHom'_hom_comp i j k

/-- The transition morphisms of that datum are the normalised comparisons. -/
theorem normalizedDatum'_hom (i j : I) :
    (normalizedDatum' P Q s sq sq₃ hQ hQ₃ L N α β).hom i j =
      normalizedHom P Q s g L N α β (sq i j).p (sq i j).p₁ (sq i j).p₂
        (sq i j).hp₁ (sq i j).hp₂ := rfl

/-- **The descent datum of a normalised family of trivialisations**, in the fibre-product-free
presentation. -/
@[reducible] noncomputable def normalizedDatum : F.DescentData (fun i => Q.map (g i)) where
  obj := L
  hom _ q _ _ f₁ f₂ h₁ h₂ :=
    (Pseudofunctor.DescentData'.descentData
      (normalizedDatum' P Q s sq sq₃ hQ hQ₃ L N α β)).hom q f₁ f₂ h₁ h₂
  pullHom_hom _ _ r q q' hq _ _ f₁ f₂ h₁ h₂ k₁ k₂ e₁ e₂ :=
    (Pseudofunctor.DescentData'.descentData
      (normalizedDatum' P Q s sq sq₃ hQ hQ₃ L N α β)).pullHom_hom r q q' hq f₁ f₂ h₁ h₂ k₁ k₂
      e₁ e₂
  hom_self _ q _ a ha :=
    (Pseudofunctor.DescentData'.descentData
      (normalizedDatum' P Q s sq sq₃ hQ hQ₃ L N α β)).hom_self q a ha
  hom_comp _ q _ _ _ f₁ f₂ f₃ h₁ h₂ h₃ :=
    (Pseudofunctor.DescentData'.descentData
      (normalizedDatum' P Q s sq sq₃ hQ hQ₃ L N α β)).hom_comp q f₁ f₂ f₃ h₁ h₂ h₃

/-- The components of the descent datum are the prescribed objects. -/
theorem normalizedDatum_obj (i : I) :
    (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).obj i = L i := rfl

/-- The transition of the descent datum is the one of its fibre-product presentation. -/
theorem normalizedDatum_hom {Y : C} (q : Y ⟶ Q.obj T) {i j : I}
    (f₁ : Y ⟶ Q.obj (U i)) (f₂ : Y ⟶ Q.obj (U j))
    (h₁ : f₁ ≫ Q.map (g i) = q) (h₂ : f₂ ≫ Q.map (g j) = q) :
    (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).hom q f₁ f₂ h₁ h₂ =
      Pseudofunctor.DescentData'.pullHom'
        (normalizedDatum' P Q s sq sq₃ hQ hQ₃ L N α β).hom q f₁ f₂ h₁ h₂ := rfl

/-- Over an object coming from `D`, the transition of the descent datum is the normalised
comparison there. -/
theorem normalizedDatum_hom_map {V : D} (q : V ⟶ T) {i j : I} (a : V ⟶ U i) (b : V ⟶ U j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).hom (Q.map q) (Q.map a) (Q.map b)
        (by rw [← Q.map_comp, ha]) (by rw [← Q.map_comp, hb]) =
      normalizedHom P Q s g L N α β q a b ha hb := by
  obtain ⟨l, hl₁, hl₂⟩ := (sq i j).isPullback.exists_lift a b (ha.trans hb.symm)
  have hq : l ≫ (sq i j).p = q := by
    rw [← (sq i j).hp₁, ← Category.assoc, hl₁, ha]
  rw [normalizedDatum_hom,
    Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ (Q.map l) _ _
    (by rw [← Q.map_comp, hl₁]) (by rw [← Q.map_comp, hl₂]), normalizedDatum'_hom]
  exact diagramHom_pull Q L _
    (fun {V W} r q {i j} a b ha hb => normalizedHom_pull P Q s g L N α β r q a b ha hb)
    l (sq i j).p q (sq i j).p₁ (sq i j).p₂ a b (sq i j).hp₁ (sq i j).hp₂ hq hl₁ hl₂

/-- **The trivialisations are compatible with the descent datum, over an object of `D`.** -/
theorem pullHom_alpha_hom_map {V : D} (q : V ⟶ T) {i j : I} (a : V ⟶ U i) (b : V ⟶ U j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    pullHom (α i).hom (P.map a) (s.app V ≫ Q.map a) (P.map q) (s.naturality a)
        (by rw [← P.map_comp, ha]) =
      (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).hom (s.app V ≫ Q.map q)
          (s.app V ≫ Q.map a) (s.app V ≫ Q.map b)
          (by rw [Category.assoc, ← Q.map_comp, ha]) (by rw [Category.assoc, ← Q.map_comp, hb]) ≫
        pullHom (α j).hom (P.map b) (s.app V ≫ Q.map b) (P.map q) (s.naturality b)
          (by rw [← P.map_comp, hb]) := by
  have h1 : (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).hom (s.app V ≫ Q.map q)
        (s.app V ≫ Q.map a) (s.app V ≫ Q.map b)
        (by rw [Category.assoc, ← Q.map_comp, ha]) (by rw [Category.assoc, ← Q.map_comp, hb]) =
      normalizedHomOnBase P Q s g L N α q a b ha hb := by
    rw [← (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).pullHom_hom (s.app V) (Q.map q)
      (s.app V ≫ Q.map q) rfl (Q.map a) (Q.map b) (by rw [← Q.map_comp, ha])
      (by rw [← Q.map_comp, hb]) (s.app V ≫ Q.map a) (s.app V ≫ Q.map b) rfl rfl,
      normalizedDatum_hom_map P Q s sq sq₃ hQ hQ₃ L N α β q a b ha hb]
    exact normalizedHom_spec P Q s g L N α β q a b ha hb
  have h2 : normalizedHomOnBase P Q s g L N α q a b ha hb ≫
      pullHom (α j).hom (P.map b) (s.app V ≫ Q.map b) (P.map q) (s.naturality b)
        (by rw [← P.map_comp, hb]) =
      pullHom (α i).hom (P.map a) (s.app V ≫ Q.map a) (P.map q) (s.naturality a)
        (by rw [← P.map_comp, ha]) := by
    unfold normalizedHomOnBase
    rw [Category.assoc, pullHom_inv_comp_pullHom_hom (α j) (P.map b) (s.app V ≫ Q.map b)
      (P.map q) (s.naturality b) (by rw [← P.map_comp, hb]), Category.comp_id]
  rw [h1]
  exact h2.symm

variable (hP : ∀ i j, IsPullback (P.map (sq i j).p₁) (P.map (sq i j).p₂)
  (P.map (g i)) (P.map (g j)))

include hP in
/-- **The trivialisations are compatible with the descent datum, over an arbitrary object of
`C`.** -/
theorem pullHom_alpha_hom {Y : C} (q : Y ⟶ P.obj T) {i j : I} (a₁ : Y ⟶ P.obj (U i))
    (a₂ : Y ⟶ P.obj (U j)) (h₁ : a₁ ≫ P.map (g i) = q) (h₂ : a₂ ≫ P.map (g j) = q) :
    pullHom (α i).hom a₁ (a₁ ≫ s.app (U i)) q rfl h₁ =
      (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).hom (q ≫ s.app T)
          (a₁ ≫ s.app (U i)) (a₂ ≫ s.app (U j))
          (by rw [Category.assoc, ← s.naturality, ← Category.assoc, h₁])
          (by rw [Category.assoc, ← s.naturality, ← Category.assoc, h₂]) ≫
        pullHom (α j).hom a₂ (a₂ ≫ s.app (U j)) q rfl h₂ := by
  obtain ⟨l, hl₁, hl₂⟩ := (hP i j).exists_lift a₁ a₂ (by rw [h₁, h₂])
  have hlq : l ≫ P.map (sq i j).p = q := by
    rw [← (sq i j).hp₁, P.map_comp, ← Category.assoc, hl₁, h₁]
  have e₁ : l ≫ (s.app (sq i j).pullback ≫ Q.map (sq i j).p₁) = a₁ ≫ s.app (U i) := by
    rw [← s.naturality, ← Category.assoc, hl₁]
  have e₂ : l ≫ (s.app (sq i j).pullback ≫ Q.map (sq i j).p₂) = a₂ ≫ s.app (U j) := by
    rw [← s.naturality, ← Category.assoc, hl₂]
  have hkey := pullHom_alpha_hom_map P Q s sq sq₃ hQ hQ₃ L N α β (sq i j).p
    (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂
  have hside : ∀ {k : I} (m : (sq i j).pullback ⟶ U k) (a : Y ⟶ P.obj (U k))
      (hm : m ≫ g k = (sq i j).p) (hl : l ≫ P.map m = a) (h : a ≫ P.map (g k) = q)
      (e : l ≫ (s.app (sq i j).pullback ≫ Q.map m) = a ≫ s.app (U k)),
      pullHom (pullHom (α k).hom (P.map m) (s.app (sq i j).pullback ≫ Q.map m)
        (P.map (sq i j).p) (s.naturality m) (by rw [← P.map_comp, hm])) l
        (a ≫ s.app (U k)) q e hlq = pullHom (α k).hom a (a ≫ s.app (U k)) q rfl h :=
    fun m a hm hl h e => pullHom_pullHom_of_eq _ _ _ _ _ _ _ _ hl _ _ e hlq rfl h
  have hC := (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β).pullHom_hom l
    (s.app (sq i j).pullback ≫ Q.map (sq i j).p) (q ≫ s.app T)
    (by rw [← s.naturality, ← Category.assoc, hlq])
    (s.app (sq i j).pullback ≫ Q.map (sq i j).p₁)
    (s.app (sq i j).pullback ≫ Q.map (sq i j).p₂)
    (by rw [Category.assoc, ← Q.map_comp, (sq i j).hp₁])
    (by rw [Category.assoc, ← Q.map_comp, (sq i j).hp₂])
    (a₁ ≫ s.app (U i)) (a₂ ≫ s.app (U j)) e₁ e₂
  rw [← hside _ a₁ (sq i j).hp₁ hl₁ h₁ e₁, hkey,
    pullHom_comp' _ _ l (a₁ ≫ s.app (U i)) (a₂ ≫ s.app (U j)) q e₁ e₂ hlq,
    hside _ a₂ (sq i j).hp₂ hl₂ h₂ e₂, hC]

/-- A trivialisation restricted along a morphism into the base change of a member. -/
noncomputable def alphaMap {Y : C} {i : I} (k : Y ⟶ P.obj (U i)) :
    (F.map k.op.toLoc).toFunctor.obj
        ((F.map (s.app (U i)).op.toLoc).toFunctor.obj (L i)) ⟶
      (F.map k.op.toLoc).toFunctor.obj
        ((F.map (P.map (g i)).op.toLoc).toFunctor.obj N) :=
  (F.map k.op.toLoc).toFunctor.map (α i).hom

/-- The restricted trivialisation is the functor applied to the trivialisation. -/
theorem alphaMap_def {Y : C} {i : I} (k : Y ⟶ P.obj (U i)) :
    alphaMap P Q s L N α k = (F.map k.op.toLoc).toFunctor.map (α i).hom := rfl

/-- The transition of the canonical descent datum of `N`. -/
noncomputable def canonTrans {Y : C} (q : Y ⟶ P.obj T) {i₁ i₂ : I}
    (f₁ : Y ⟶ P.obj (U i₁)) (f₂ : Y ⟶ P.obj (U i₂))
    (h₁ : f₁ ≫ P.map (g i₁) = q) (h₂ : f₂ ≫ P.map (g i₂) = q) :
    (F.map f₁.op.toLoc).toFunctor.obj
        ((F.map (P.map (g i₁)).op.toLoc).toFunctor.obj N) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj
        ((F.map (P.map (g i₂)).op.toLoc).toFunctor.obj N) :=
  ((F.toDescentData (fun i => P.map (g i))).obj N).hom q f₁ f₂ h₁ h₂

/-- The transition of the pulled-back descent datum. -/
noncomputable def pulledTrans {Y : C} (q : Y ⟶ P.obj T) {i₁ i₂ : I}
    (f₁ : Y ⟶ P.obj (U i₁)) (f₂ : Y ⟶ P.obj (U i₂))
    (h₁ : f₁ ≫ P.map (g i₁) = q) (h₂ : f₂ ≫ P.map (g i₂) = q) :
    (F.map f₁.op.toLoc).toFunctor.obj
        ((F.map (s.app (U i₁)).op.toLoc).toFunctor.obj (L i₁)) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj
        ((F.map (s.app (U i₂)).op.toLoc).toFunctor.obj (L i₂)) :=
  ((Pseudofunctor.DescentData.pullFunctor F (f := fun i => Q.map (g i)) (p := s.app T)
    (f' := fun i => P.map (g i)) (α := fun i => i) (p' := fun i => s.app (U i))
    (fun i => (s.naturality (g i)).symm)).obj
    (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β)).hom q f₁ f₂ h₁ h₂

include hP in
/-- **The trivialisations commute with the transitions of the two descent data upstairs**: the
canonical one of `N` and the pullback along `s` of the descent datum downstairs. -/
theorem alphaMap_comp_canonTrans {Y : C} (q : Y ⟶ P.obj T) {i₁ i₂ : I} (f₁ : Y ⟶ P.obj (U i₁))
    (f₂ : Y ⟶ P.obj (U i₂)) (hf₁ : f₁ ≫ P.map (g i₁) = q) (hf₂ : f₂ ≫ P.map (g i₂) = q) :
    alphaMap P Q s L N α f₁ ≫ canonTrans (P := P) (N := N) q f₁ f₂ hf₁ hf₂ =
      pulledTrans P Q s sq sq₃ hQ hQ₃ L N α β q f₁ f₂ hf₁ hf₂ ≫ alphaMap P Q s L N α f₂ := by
  have key := pullHom_alpha_hom P Q s sq sq₃ hQ hQ₃ L N α β hP q f₁ f₂ hf₁ hf₂
  have hof : canonTrans (P := P) (N := N) q f₁ f₂ hf₁ hf₂ =
      (Pseudofunctor.DescentData.ofObj (f := fun i => P.map (g i)) N).hom q f₁ f₂ hf₁ hf₂ := rfl
  have hpf : pulledTrans P Q s sq sq₃ hQ hQ₃ L N α β q f₁ f₂ hf₁ hf₂ =
      Pseudofunctor.DescentData.pullFunctorObjHom (f := fun i => Q.map (g i)) (p := s.app T)
        (f' := fun i => P.map (g i)) (α := fun i => i) (p' := fun i => s.app (U i))
        (fun i => (s.naturality (g i)).symm)
        (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β) q f₁ f₂ hf₁ hf₂ := rfl
  rw [alphaMap_def, alphaMap_def, hof, hpf, Pseudofunctor.DescentData.ofObj_hom,
    map_eq_pullHom_assoc (α i₁).hom f₁ (f₁ ≫ s.app (U i₁)) q rfl hf₁,
    Pseudofunctor.DescentData.pullFunctorObjHom_eq_assoc (f := fun i => Q.map (g i))
      (p := s.app T) (f' := fun i => P.map (g i)) (α := fun i => i)
      (p' := fun i => s.app (U i)) (fun i => (s.naturality (g i)).symm)
      (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β) q f₁ f₂ (q ≫ s.app T)
      (f₁ ≫ s.app (U i₁)) (f₂ ≫ s.app (U i₂)) hf₁ hf₂ rfl rfl rfl,
    map_eq_pullHom (α i₂).hom f₂ (f₂ ≫ s.app (U i₂)) q rfl hf₂,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, key]
  exact congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)

include hP in
/-- **The pullback along `s` of the descent datum downstairs is the canonical descent datum of
`N`.** -/
noncomputable def normalizedDatumPullIso :
    (Pseudofunctor.DescentData.pullFunctor F (f := fun i => Q.map (g i)) (p := s.app T)
        (f' := fun i => P.map (g i)) (α := fun i => i) (p' := fun i => s.app (U i))
        (fun i => (s.naturality (g i)).symm)).obj
        (normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β) ≅
      (F.toDescentData (fun i => P.map (g i))).obj N :=
  Pseudofunctor.DescentData.isoMk (fun i => α i)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ =>
      alphaMap_comp_canonTrans P Q s sq sq₃ hQ hQ₃ L N α β hP q f₁ f₂ hf₁ hf₂)

include hP in
/-- **Descent of a normalised family of trivialisations.** An object `M₀` downstairs whose
canonical descent datum is isomorphic to the normalised one has `s.app T`-pullback isomorphic
to `N`. -/
theorem nonempty_iso_of_normalizedDatum (M₀ : F.obj (.mk (.op (Q.obj T))))
    (ε : (F.toDescentData (fun i => Q.map (g i))).obj M₀ ≅
      normalizedDatum P Q s sq sq₃ hQ hQ₃ L N α β)
    (h₁ : Function.Bijective ((F.toDescentData (fun i => P.map (g i))).map :
      ((F.map (s.app T).op.toLoc).toFunctor.obj M₀ ⟶ N) → _))
    (h₂ : Function.Bijective ((F.toDescentData (fun i => P.map (g i))).map :
      (N ⟶ (F.map (s.app T).op.toLoc).toFunctor.obj M₀) → _))
    (h₃ : Function.Bijective ((F.toDescentData (fun i => P.map (g i))).map :
      ((F.map (s.app T).op.toLoc).toFunctor.obj M₀ ⟶
        (F.map (s.app T).op.toLoc).toFunctor.obj M₀) → _))
    (h₄ : Function.Bijective ((F.toDescentData (fun i => P.map (g i))).map : (N ⟶ N) → _)) :
    Nonempty ((F.map (s.app T).op.toLoc).toFunctor.obj M₀ ≅ N) :=
  nonempty_iso_of_toDescentData_iso _ h₁ h₂ h₃ h₄
    (((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
        (f := fun i => Q.map (g i)) (p := s.app T) (f' := fun i => P.map (g i))
        (α := fun i => i) (p' := fun i => s.app (U i))
        (fun i => (s.naturality (g i)).symm)).app M₀).symm ≪≫
      (Pseudofunctor.DescentData.pullFunctor F (f := fun i => Q.map (g i)) (p := s.app T)
        (f' := fun i => P.map (g i)) (α := fun i => i) (p' := fun i => s.app (U i))
        (fun i => (s.naturality (g i)).symm)).mapIso ε ≪≫
      normalizedDatumPullIso P Q s sq sq₃ hQ hQ₃ L N α β hP)

end Normalized

end Stacks.Picard


namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- The base-change projections, as a natural transformation from the base change functor to
the forgetful functor on test schemes. -/
def baseChangeProjNatTrans :
    baseChangeFunctor B hX hS f ⟶ BigFppfOver.toScheme B S hS where
  app T := baseChangeProj B hX hS f T
  naturality _ _ a := (baseChangeMap_isPullback_proj B hX hS f a).w

/-- A covering family of test schemes, read as a zero-hypercover of the underlying scheme. -/
def schemeHypercover (T : BigFppfOver B S hS) (E : PreZeroHypercover.{u + 1} T) :
    PreZeroHypercover.{u + 1} ((BigFppfOver.toScheme B S hS).obj T) where
  I₀ := E.I₀
  X i := (BigFppfOver.toScheme B S hS).obj (E.X i)
  f i := (BigFppfOver.toScheme B S hS).map (E.f i)

/-- A covering family of test schemes is an fpqc covering family of the underlying scheme. -/
theorem schemeHypercover_presieve_mem_fpqcPrecoverage (T : BigFppfOver B S hS)
    (E : PreZeroHypercover.{u + 1} T) (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩) :
    (schemeHypercover B hS T E).presieve₀ ∈
      Scheme.fpqcPrecoverage.{u} ((BigFppfOver.toScheme B S hS).obj T) := by
  have hfppf : Presieve.ofArrows
      (fun i : E.I₀ => B.inclusion.obj (E.X i).left)
      (fun i : E.I₀ => B.inclusion.map (E.f i).left) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T.left) := by
    simpa only [IsFppfCovering, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      PreZeroHypercover.map, Over.forget_obj, Over.forget_map] using hE.1
  exact Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hfppf

/-- The chosen fibre product of two morphisms of test schemes is a fibre product of the
underlying schemes. -/
theorem isPullback_toScheme_chosenPullback {U V T : BigFppfOver B S hS} (a : U ⟶ T)
    (b : V ⟶ T) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (bigFppfOverChosenPullback B hS a b).p₁)
      ((BigFppfOver.toScheme B S hS).map (bigFppfOverChosenPullback B hS a b).p₂)
      ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) :=
  IsPullback.of_hasPullback (B.inclusion.map a.left) (B.inclusion.map b.left)

/-- The chosen wide fibre product of three morphisms of test schemes is a fibre product of the
underlying schemes. -/
theorem isPullback_toScheme_chosenPullback₃ {U V W T : BigFppfOver B S hS} (a : U ⟶ T)
    (b : V ⟶ T) (c : W ⟶ T) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map (bigFppfOverChosenPullback₃ B hS a b c).p₁₂)
      ((BigFppfOver.toScheme B S hS).map (bigFppfOverChosenPullback₃ B hS a b c).p₂₃)
      ((BigFppfOver.toScheme B S hS).map (bigFppfOverChosenPullback B hS a b).p₂)
      ((BigFppfOver.toScheme B S hS).map (bigFppfOverChosenPullback B hS b c).p₁) :=
  isPullback_toScheme_chosenPullback B hS (bigFppfOverChosenPullback B hS a b).p₂
    (bigFppfOverChosenPullback B hS b c).p₁

/-- The structure sheaf of the underlying scheme of a test scheme. -/
abbrev testUnit (V : BigFppfOver B S hS) : ((BigFppfOver.toScheme B S hS).obj V).Modules :=
  SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- **Pulling back along the base-change projection is bijective on the homomorphisms between the
pullbacks of the structure sheaves of two members of a covering family.** -/
theorem bijective_pullHom_baseChangeProj {T : BigFppfOver B S hS}
    (E : PreZeroHypercover.{u + 1} T)
    (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    {V : BigFppfOver B S hS} (q : V ⟶ T) {i j : E.I₀} (a : V ⟶ E.X i) (b : V ⟶ E.X j)
    (_ha : a ≫ E.f i = q) (_hb : b ≫ E.f j = q) :
    Function.Bijective (fun φ :
        (modulePullbackPseudofunctor.map
            ((BigFppfOver.toScheme B S hS).map a).op.toLoc).toFunctor.obj
            (testUnit B hS (E.X i)) ⟶
          (modulePullbackPseudofunctor.map
            ((BigFppfOver.toScheme B S hS).map b).op.toLoc).toFunctor.obj
            (testUnit B hS (E.X j)) =>
      pullHom φ ((baseChangeProjNatTrans B hX hS f).app V)
        ((baseChangeProjNatTrans B hX hS f).app V ≫ (BigFppfOver.toScheme B S hS).map a)
        ((baseChangeProjNatTrans B hX hS f).app V ≫ (BigFppfOver.toScheme B S hS).map b)
        rfl rfl) :=
  Stacks.Picard.bijective_pullHom_proj ((BigFppfOver.toScheme B S hS).map a)
    ((BigFppfOver.toScheme B S hS).map b) (baseChangeProj B hX hS f V) (hOiso V)

/-! ### The descent datum of a locally trivial invertible module -/

section

variable (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
  {T : BigFppfOver B S hS} (E : PreZeroHypercover.{u + 1} T)
  (N : (baseChange B hX hS f T).Modules)
  (α : ∀ i : E.I₀,
    (modulePullbackPseudofunctor.map
        (baseChangeProj B hX hS f (E.X i)).op.toLoc).toFunctor.obj (testUnit B hS (E.X i)) ≅
      (modulePullbackPseudofunctor.map
        (baseChangeMap B hX hS f (E.f i)).op.toLoc).toFunctor.obj N)

/-- The chosen fibre product of two members of a covering family of test schemes. -/
noncomputable def chosenSq (i j : E.I₀) : ChosenPullback (E.f i) (E.f j) :=
  bigFppfOverChosenPullback B hS (E.f i) (E.f j)

/-- The chosen wide fibre product of three members of a covering family of test schemes. -/
noncomputable def chosenSq₃ (i j k : E.I₀) :
    ChosenPullback₃ (chosenSq B hS E i j) (chosenSq B hS E j k) (chosenSq B hS E i k) :=
  bigFppfOverChosenPullback₃ B hS (E.f i) (E.f j) (E.f k)

/-- The chosen fibre product of two members is a fibre product of the underlying schemes. -/
theorem isPullback_toScheme_chosenSq (i j : E.I₀) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (chosenSq B hS E i j).p₁)
      ((BigFppfOver.toScheme B S hS).map (chosenSq B hS E i j).p₂)
      ((BigFppfOver.toScheme B S hS).map (E.f i))
      ((BigFppfOver.toScheme B S hS).map (E.f j)) :=
  isPullback_toScheme_chosenPullback B hS (E.f i) (E.f j)

/-- The chosen wide fibre product of three members is a fibre product of the underlying
schemes. -/
theorem isPullback_toScheme_chosenSq₃ (i j k : E.I₀) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (chosenSq₃ B hS E i j k).p₁₂)
      ((BigFppfOver.toScheme B S hS).map (chosenSq₃ B hS E i j k).p₂₃)
      ((BigFppfOver.toScheme B S hS).map (chosenSq B hS E i j).p₂)
      ((BigFppfOver.toScheme B S hS).map (chosenSq B hS E j k).p₁) :=
  isPullback_toScheme_chosenPullback₃ B hS (E.f i) (E.f j) (E.f k)

/-- The base changes of the projections of the chosen fibre product of two members form a
fibre-product square. -/
theorem isPullback_baseChangeMap_chosenSq (i j : E.I₀) :
    IsPullback (baseChangeMap B hX hS f (chosenSq B hS E i j).p₁)
      (baseChangeMap B hX hS f (chosenSq B hS E i j).p₂)
      (baseChangeMap B hX hS f (E.f i)) (baseChangeMap B hX hS f (E.f j)) :=
  (baseChangeChosenPullback B hX hS f (E.f i) (E.f j)).isPullback

/-- **The descent datum on the members of a covering family of `T`** attached to
trivialisations of a module on `X_T` over their base changes: its components are the structure
sheaves of the members, and its transitions are the normalised comparisons of the
trivialisations. -/
@[reducible] noncomputable def middleDatum :
    modulePullbackPseudofunctor.DescentData (schemeHypercover B hS T E).f :=
  Stacks.Picard.normalizedDatum (baseChangeFunctor B hX hS f) (BigFppfOver.toScheme B S hS)
    (baseChangeProjNatTrans B hX hS f)
    (chosenSq B hS E) (chosenSq₃ B hS E) (isPullback_toScheme_chosenSq B hS E)
    (isPullback_toScheme_chosenSq₃ B hS E)
    (fun i => testUnit B hS (E.X i)) N α
    (fun {_} q {_ _} a b ha hb =>
      bijective_pullHom_baseChangeProj B hX hS f E hOiso q a b ha hb)

/-- The same descent datum, with the quasi-coherence of its components recorded. -/
noncomputable def middleQcDatum :
    AlgebraicGeometry.QuasicoherentDescentData (schemeHypercover B hS T E).f :=
  ⟨middleDatum B hX hS f hOiso E N α, fun i => inferInstanceAs
    (SheafOfModules.unit
      ((BigFppfOver.toScheme B S hS).obj (E.X i)).ringCatSheaf).IsQuasicoherent⟩

include hOiso α in
/-- **Effectivity of the descent datum**: there is a quasi-coherent module on `T` whose canonical
descent datum for the covering family is the one built from the trivialisations. -/
theorem exists_descentModule (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩) :
    ∃ M₀ : (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory,
      Nonempty ((modulePullbackPseudofunctor.toDescentData
          (schemeHypercover B hS T E).f).obj M₀.obj ≅
        middleDatum B hX hS f hOiso E N α) := by
  obtain ⟨M₀, ⟨e⟩⟩ := AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage
    (schemeHypercover B hS T E) (schemeHypercover_presieve_mem_fpqcPrecoverage B hS T E hE)
    (middleQcDatum B hX hS f hOiso E N α)
  exact ⟨M₀, ⟨(ObjectProperty.ι _).mapIso e⟩⟩

include hOiso α in
/-- **The descended module is invertible.** -/
theorem isInvertible_of_descentIso (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩)
    (M₀ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory)
    (ε : (modulePullbackPseudofunctor.toDescentData
        (schemeHypercover B hS T E).f).obj M₀.obj ≅ middleDatum B hX hS f hOiso E N α) :
    Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj T).presheaf
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 M₀.obj := by
  refine Stacks.Picard.isInvertible_of_pullback_fpqcCover M₀.obj M₀.property
    ⟨schemeHypercover B hS T E,
      schemeHypercover_presieve_mem_fpqcPrecoverage B hS T E hE⟩ fun i => ?_
  exact Stacks.Picard.isInvertible_of_iso (Stacks.Picard.descentDataIsoApp ε i).symm
    (Stacks.SheafOfModules.isInvertible_unit _ _)

include hOiso α in
/-- **The pullback of the descended module to `X_T` is the module we started from.** -/
theorem nonempty_iso_baseChangeProj (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩)
    (hNqc : N.IsQuasicoherent)
    (M₀ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory)
    (ε : (modulePullbackPseudofunctor.toDescentData
        (schemeHypercover B hS T E).f).obj M₀.obj ≅ middleDatum B hX hS f hOiso E N α) :
    Nonempty ((modulePullbackPseudofunctor.map
        (baseChangeProj B hX hS f T).op.toLoc).toFunctor.obj M₀.obj ≅ N) := by
  have hfpqcX : Presieve.ofArrows
      (fun i : E.I₀ => (baseChangeFunctor B hX hS f).obj (E.X i))
      (fun i : E.I₀ => (baseChangeFunctor B hX hS f).map (E.f i)) ∈
      Scheme.fpqcPrecoverage.{u} ((baseChangeFunctor B hX hS f).obj T) :=
    baseChange_presieve_mem_fpqcPrecoverage B hX hS f T E hE
  have hqcP : ((modulePullbackPseudofunctor.map
      ((baseChangeProjNatTrans B hX hS f).app T).op.toLoc).toFunctor.obj
        M₀.obj).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (baseChangeProj B hX hS f T) M₀.obj M₀.property
  exact Stacks.Picard.nonempty_iso_of_normalizedDatum
    (baseChangeFunctor B hX hS f) (BigFppfOver.toScheme B S hS)
    (baseChangeProjNatTrans B hX hS f)
    (chosenSq B hS E) (chosenSq₃ B hS E) (isPullback_toScheme_chosenSq B hS E)
    (isPullback_toScheme_chosenSq₃ B hS E)
    (fun i => testUnit B hS (E.X i)) N α
    (fun {V} q {i j} a b ha hb =>
      bijective_pullHom_baseChangeProj B hX hS f E hOiso q a b ha hb)
    (isPullback_baseChangeMap_chosenSq B hX hS f E)
    M₀.obj ε
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqcX _ _ hqcP hNqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqcX _ _ hNqc hqcP)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqcX _ _ hqcP hqcP)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqcX _ _ hNqc hNqc)

include hOiso α in
/-- **An invertible module on `X_T` trivial on the base changes of a covering family of `T` is
pulled back from `Pic(T)`.** -/
theorem exists_schemePullbackClass_baseChangeProj_eq
    (hE : BigFppfOver.IsCovering B S hS ⟨T, E⟩)
    (hNinv : Stacks.SheafOfModules.IsInvertible (baseChange B hX hS f T).presheaf
      (baseChange B hX hS f T).ringCatSheaf.2 N) :
    ∃ P : Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj T),
      Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T) P =
        Stacks.SheafOfModules.picardClass (baseChange B hX hS f T).presheaf
          (baseChange B hX hS f T).ringCatSheaf.2 N hNinv := by
  obtain ⟨M₀, ⟨ε⟩⟩ := exists_descentModule B hX hS f hOiso E N α hE
  obtain ⟨iso⟩ := nonempty_iso_baseChangeProj B hX hS f hOiso E N α hE
    (Stacks.Picard.isQuasicoherent_of_isInvertible N hNinv) M₀ ε
  have hMinv := isInvertible_of_descentIso B hX hS f hOiso E N α hE M₀ ε
  refine ⟨Stacks.SheafOfModules.picardClass ((BigFppfOver.toScheme B S hS).obj T).presheaf
    ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 M₀.obj hMinv, ?_⟩
  exact (Stacks.Picard.pullbackClass_classOf (baseChangeProj B hX hS f T).toLRSHom.toShHom
      M₀.obj hMinv).trans
    ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨iso⟩)

end

/-! ### Exactness at `Pic(X_T)` -/

/-- If the comparison map `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every `S`-scheme `T` of the
site, then a Picard class of `X_T` dies in `Pic_{X/S}(T)` exactly when it is pulled back along the
projection `X_T ⟶ T`; this is exactness at `Pic(X_T)` of `0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T)`. -/
@[stacks 0B9M "exactness at Pic(X_T)"]
theorem exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom_of_isIso_c
    (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)
    (T : BigFppfOver B S hS) :
    Function.Exact (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T))
      (toPicardFunctorHom B hX hS f T) := by
  intro c
  refine ⟨fun hc => ?_, ?_⟩
  · obtain ⟨E, hE, hloc⟩ := exists_isCovering_picardMap_eq_zero B hX hS f T c hc
    obtain ⟨P, hP⟩ := exists_schemePullbackClass_baseChangeProj_eq B hX hS f hOiso E
      (Stacks.Picard.picardRepresentative (baseChange B hX hS f T).toRingedSpace c).obj
      (fun i => ((Stacks.Picard.nonempty_pullHomIso_of_schemePullbackClass_eq_zero
          (baseChangeMap B hX hS f (E.f i)) c (hloc i)).map fun e =>
        AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
            (baseChangeProj B hX hS f (E.X i)) ≪≫
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
            (baseChangeMap B hX hS f (E.f i))).symm ≪≫ e.symm).some)
      hE (Stacks.Picard.picardRepresentative (baseChange B hX hS f T).toRingedSpace c).property
    exact ⟨P, hP.trans (Stacks.Picard.classOf_picardRepresentative
      (baseChange B hX hS f T).toRingedSpace c)⟩
  · rintro ⟨N, rfl⟩
    exact toPicardFunctorHom_schemePullbackClass_baseChangeProj B hX hS f T N

end Stacks.PicardFunctor

end
