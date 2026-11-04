module

public import StacksFrontier.CategoryTheory.Sites.Descent.EffectiveDescentOfCoverBaseChange
public import StacksFrontier.CategoryTheory.Sites.Descent.DescentCounitLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Abstract

/-!
# Transitivity of effective descent

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a prestack for a Grothendieck topology `J` on a category
`C` with fibre products, let `f i : X i ⟶ X` and `r j : Y j ⟶ X` be covering families of `X`, and
suppose that descent is effective along `r` and along each base change of `f` to `Y j`. Then
descent is effective along `f`.

## Main results

* `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_isEquivalence_pullback`: the
  transitivity of effective descent.

## Implementation notes

A descent datum `D` relative to `f` is restricted to each `Y j`, where it is effective; a
*solution* of `D` over `g : Y ⟶ X` (`CategoryTheory.Pseudofunctor.StackTransitivity.Sol`) is an
object over `Y` with an identification of its canonical descent datum with the restriction of
`D`. Any two solutions over `a : Z ⟶ Y₁` and `b : Z ⟶ Y₂` are compared by a canonical isomorphism
(`CategoryTheory.Pseudofunctor.StackTransitivity.cmp`), glued along the base change of `f` from
the local comparisons through the members of `f`; these comparisons are compatible with base
change and satisfy the cocycle condition, so the local solutions glue along `r` to an object of
the fibre over `X`, and the comparison of that object with the canonical solutions `D.obj i`
over the members of `f` is the required isomorphism of descent data. Every morphism is written
as a base change `pullHom`, and every identity between them is checked after base change along
a covering family, which is where the prestack hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t t' v' u' v u

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  [HasPullbacks C]

/-- The base change of a covering family generates a covering sieve. -/
lemma ofArrows_pullback_mem {J : GrothendieckTopology C} {X Y : C} {ι : Type t} {Xi : ι → C}
    {f : ∀ i, Xi i ⟶ X} (hf : Sieve.ofArrows Xi f ∈ J X) (g : Y ⟶ X) :
    Sieve.ofArrows (fun i ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g) ∈ J Y := by
  have h := J.pullback_stable g hf
  rwa [Sieve.ofArrows, ← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback] at h

/-- Two morphisms between pullbacks are equal if their base changes to each member of the base
change of a covering family along `q` are equal. -/
private lemma eq_of_pullHom_snd_eq {J : GrothendieckTopology C} [F.IsPrestack J] {X Z : C}
    {ι : Type t} {Xi : ι → C} {f : ∀ i, Xi i ⟶ X} (hf : Sieve.ofArrows Xi f ∈ J X) (q : Z ⟶ X)
    ⦃X₁ X₂ : C⦄ {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {f₁ : Z ⟶ X₁}
    {f₂ : Z ⟶ X₂}
    (s s' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (h : ∀ i, pullHom s (pullback.snd (f i) q) _ _ rfl rfl =
      pullHom s' (pullback.snd (f i) q) _ _ rfl rfl) : s = s' := by
  have := (F.fullyFaithfulToDescentData _ (ofArrows_pullback_mem hf q)).faithful
  exact eq_of_pullHom_eq_of_faithful (fun i ↦ pullback.snd (f i) q) s s' h

/-- If the base change of `φ` along `pullback.snd p q` is `t`, then the base change of `φ` along
`w = u ≫ pullback.snd p q` is the base change of `t` along `u`. -/
private lemma pullHom_eq_pullHom_of_snd {X Z A W : C} {p : A ⟶ X} {q : Z ⟶ X} ⦃X₁ X₂ : C⦄
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {f₁ : Z ⟶ X₁} {f₂ : Z ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {t : (F.map (pullback.snd p q ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (pullback.snd p q ≫ f₂).op.toLoc).toFunctor.obj M₂}
    (ht : pullHom φ (pullback.snd p q) _ _ rfl rfl = t) (u : W ⟶ pullback p q) (w : W ⟶ Z)
    (hu : u ≫ pullback.snd p q = w) (wa : W ⟶ X₁) (wb : W ⟶ X₂) (hwa : w ≫ f₁ = wa)
    (hwb : w ≫ f₂ = wb) :
    pullHom φ w wa wb hwa hwb =
      pullHom t u wa wb (by rw [← hwa, ← hu, Category.assoc])
        (by rw [← hwb, ← hu, Category.assoc]) := by
  subst hu hwa hwb
  rw [← ht, pullHom_pullHom]

namespace StackTransitivity

/-- A morphism out of a pullback, pulled back further and written as a morphism between
pullbacks. -/
def θ {X' Y' : C} {h : Y' ⟶ X'} {M : F.obj (.mk (op X'))} {N : F.obj (.mk (op Y'))}
    (ζ : (F.map h.op.toLoc).toFunctor.obj M ⟶ N) {Z : C} (a : Z ⟶ Y') (c : Z ⟶ X')
    (hc : a ≫ h = c) :
    (F.map c.op.toLoc).toFunctor.obj M ⟶ (F.map a.op.toLoc).toFunctor.obj N :=
  (F.mapComp' h.op.toLoc a.op.toLoc c.op.toLoc (by rw [← hc]; rfl)).hom.toNatTrans.app M ≫
    (F.map a.op.toLoc).toFunctor.map ζ

omit [HasPullbacks C] in
/-- The base change of `θ ζ a c hc` along `w` is `θ ζ` at the composites with `w`. -/
lemma pullHom_θ {X' Y' : C} {h : Y' ⟶ X'} {M : F.obj (.mk (op X'))} {N : F.obj (.mk (op Y'))}
    (ζ : (F.map h.op.toLoc).toFunctor.obj M ⟶ N) {Z : C} (a : Z ⟶ Y') (c : Z ⟶ X')
    (hc : a ≫ h = c) {W : C} (w : W ⟶ Z) (wc : W ⟶ X') (wa : W ⟶ Y') (hwc : w ≫ c = wc)
    (hwa : w ≫ a = wa) :
    pullHom (θ ζ a c hc) w wc wa hwc hwa =
      θ ζ wa wc (by rw [← hwa, ← hwc, Category.assoc, hc]) := by
  subst hc hwc hwa
  simp only [pullHom, θ, Functor.map_comp, Category.assoc]
  rw [F.mapComp'_inv_naturality a.op.toLoc w.op.toLoc (w ≫ a).op.toLoc rfl ζ,
    F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc h.op.toLoc a.op.toLoc w.op.toLoc
      (a ≫ h).op.toLoc (w ≫ a).op.toLoc (w ≫ a ≫ h).op.toLoc rfl rfl (by simp)]
  simp

variable {X : C} {ι : Type t} {Xi : ι → C} (f : ∀ i, Xi i ⟶ X)

/-- The restriction of a descent datum relative to `f` along `g : Y ⟶ X`, relative to the base
change of `f` along `g`. -/
abbrev res (D : F.DescentData f) {Y : C} (g : Y ⟶ X) :
    F.DescentData (fun i ↦ pullback.snd (f i) g) :=
  (DescentData.pullFunctor F (p := g) (α := fun i ↦ i) (p' := fun i ↦ pullback.fst (f i) g)
    (fun _ ↦ pullback.condition)).obj D

/-- The gluing morphisms of the restricted descent datum. -/
lemma res_hom (D : F.DescentData f) {Y : C} (g : Y ⟶ X) {W : C} (v : W ⟶ Y) {i₁ i₂ : ι}
    (x : W ⟶ pullback (f i₁) g) (y : W ⟶ pullback (f i₂) g) (hx : x ≫ pullback.snd _ _ = v)
    (hy : y ≫ pullback.snd _ _ = v) (xf : W ⟶ Xi i₁) (yf : W ⟶ Xi i₂)
    (hxf : x ≫ pullback.fst _ _ = xf) (hyf : y ≫ pullback.fst _ _ = yf) :
    (res f D g).hom v x y hx hy =
      (F.mapComp' (pullback.fst (f i₁) g).op.toLoc x.op.toLoc xf.op.toLoc
          (by rw [← hxf]; rfl)).inv.toNatTrans.app _ ≫
        D.hom (v ≫ g) xf yf (by rw [← hxf, ← hx, Category.assoc, Category.assoc,
          pullback.condition]) (by rw [← hyf, ← hy, Category.assoc, Category.assoc,
          pullback.condition]) ≫
        (F.mapComp' (pullback.fst (f i₂) g).op.toLoc y.op.toLoc yf.op.toLoc
          (by rw [← hyf]; rfl)).hom.toNatTrans.app _ := by
  subst hx
  exact DescentData.pullFunctorObjHom_eq (p := g) (α := fun i ↦ i)
    (p' := fun i ↦ pullback.fst (f i) g) (fun i ↦ pullback.condition) D
    (x ≫ pullback.snd _ _) (j₁ := i₁) (j₂ := i₂) x y ((x ≫ pullback.snd _ _) ≫ g) xf yf rfl hy
    rfl hxf hyf

/-- The pullback of a descent datum along the identity. -/
abbrev resId (D : F.DescentData f) : F.DescentData f :=
  (DescentData.pullFunctor F (p := 𝟙 X) (α := fun i ↦ i) (p' := fun i ↦ 𝟙 (Xi i))
    (fun i ↦ by simp)).obj D

omit [HasPullbacks C] in
/-- The gluing morphisms of the pullback of a descent datum along the identity. -/
lemma resId_hom (D : F.DescentData f) {W : C} (q : W ⟶ X) {i₁ i₂ : ι} (x₁ : W ⟶ Xi i₁)
    (x₂ : W ⟶ Xi i₂) (hx₁ : x₁ ≫ f i₁ = q) (hx₂ : x₂ ≫ f i₂ = q) :
    (resId f D).hom q x₁ x₂ hx₁ hx₂ =
      (F.mapComp' (𝟙 (Xi i₁)).op.toLoc x₁.op.toLoc x₁.op.toLoc
          (by simp)).inv.toNatTrans.app (D.obj i₁) ≫
        D.hom q x₁ x₂ hx₁ hx₂ ≫
        (F.mapComp' (𝟙 (Xi i₂)).op.toLoc x₂.op.toLoc x₂.op.toLoc
          (by simp)).hom.toNatTrans.app (D.obj i₂) := by
  subst hx₁
  exact DescentData.pullFunctorObjHom_eq (p := 𝟙 X) (α := fun i ↦ i)
    (p' := fun i ↦ 𝟙 (Xi i)) (fun i ↦ by simp) D (x₁ ≫ f i₁) (j₁ := i₁) (j₂ := i₂) x₁ x₂
    (x₁ ≫ f i₁) x₁ x₂ rfl hx₂ (Category.comp_id _) (Category.comp_id _) (Category.comp_id _)

/-- A solution of a descent datum `D` relative to `f` over `g : Y ⟶ X`: an object over `Y`
together with an isomorphism of its canonical descent datum relative to the base change of `f`
with the restriction of `D`. -/
structure Sol (D : F.DescentData f) {Y : C} (g : Y ⟶ X) where
  /-- The object over `Y`. -/
  obj : F.obj (.mk (op Y))
  /-- The identification with the restricted descent datum. -/
  iso : (F.toDescentData (fun i ↦ pullback.snd (f i) g)).obj obj ≅ res f D g

variable {f} {D : F.DescentData f} {Y : C} {g : Y ⟶ X}

namespace Sol

variable (s : Sol f D g)

/-- The component of a solution at `i`. -/
def eH (i : ι) : (F.map (pullback.snd (f i) g).op.toLoc).toFunctor.obj s.obj ⟶
    (F.map (pullback.fst (f i) g).op.toLoc).toFunctor.obj (D.obj i) :=
  s.iso.hom.hom i

/-- The inverse of the component of a solution at `i`. -/
def eI (i : ι) : (F.map (pullback.fst (f i) g).op.toLoc).toFunctor.obj (D.obj i) ⟶
    (F.map (pullback.snd (f i) g).op.toLoc).toFunctor.obj s.obj :=
  s.iso.inv.hom i

/-- The component `eI i` is a right inverse of `eH i`. -/
@[reassoc (attr := simp)]
lemma eH_eI (i : ι) : s.eH i ≫ s.eI i = 𝟙 _ :=
  congrArg (fun φ ↦ DescentData.Hom.hom φ i) s.iso.hom_inv_id

/-- The component `eI i` is a left inverse of `eH i`. -/
@[reassoc (attr := simp)]
lemma eI_eH (i : ι) : s.eI i ≫ s.eH i = 𝟙 _ :=
  congrArg (fun φ ↦ DescentData.Hom.hom φ i) s.iso.inv_hom_id

/-- The base change of `eI i` is a right inverse of the base change of `eH i`. -/
@[reassoc (attr := simp)]
lemma pullHom_eH_eI (i : ι) {W : C} (x : W ⟶ pullback (f i) g) (v : W ⟶ Y) (xf : W ⟶ Xi i)
    (hx : x ≫ pullback.snd _ _ = v) (hxf : x ≫ pullback.fst _ _ = xf) :
    pullHom (s.eH i) x v xf hx hxf ≫ pullHom (s.eI i) x xf v hxf hx = 𝟙 _ := by
  rw [pullHom_comp, eH_eI, pullHom_id_self]

/-- The base change of `eI i` is a left inverse of the base change of `eH i`. -/
@[reassoc (attr := simp)]
lemma pullHom_eI_eH (i : ι) {W : C} (x : W ⟶ pullback (f i) g) (v : W ⟶ Y) (xf : W ⟶ Xi i)
    (hx : x ≫ pullback.snd _ _ = v) (hxf : x ≫ pullback.fst _ _ = xf) :
    pullHom (s.eI i) x xf v hxf hx ≫ pullHom (s.eH i) x v xf hx hxf = 𝟙 _ := by
  rw [pullHom_comp, eI_eH, pullHom_id_self]

/-- The base change of the component `eH i` of a solution is an isomorphism. -/
instance isIso_pullHom_eH (i : ι) {W : C} (x : W ⟶ pullback (f i) g) (v : W ⟶ Y)
    (xf : W ⟶ Xi i) (hx : x ≫ pullback.snd _ _ = v) (hxf : x ≫ pullback.fst _ _ = xf) :
    IsIso (pullHom (s.eH i) x v xf hx hxf) :=
  ⟨_, s.pullHom_eH_eI i x v xf hx hxf, s.pullHom_eI_eH i x v xf hx hxf⟩

/-- The compatibility of the components of a solution with the two descent data. -/
lemma eH_comm {W : C} (v : W ⟶ Y) {i₁ i₂ : ι}
    (x : W ⟶ pullback (f i₁) g) (y : W ⟶ pullback (f i₂) g) (hx : x ≫ pullback.snd _ _ = v)
    (hy : y ≫ pullback.snd _ _ = v) (xf : W ⟶ Xi i₁) (yf : W ⟶ Xi i₂)
    (hxf : x ≫ pullback.fst _ _ = xf) (hyf : y ≫ pullback.fst _ _ = yf) :
    (F.map x.op.toLoc).toFunctor.map (s.eH i₁) ≫
        (F.mapComp' (pullback.fst (f i₁) g).op.toLoc x.op.toLoc xf.op.toLoc
          (by rw [← hxf]; rfl)).inv.toNatTrans.app _ ≫
        D.hom (v ≫ g) xf yf (by rw [← hxf, ← hx, Category.assoc, Category.assoc,
          pullback.condition]) (by rw [← hyf, ← hy, Category.assoc, Category.assoc,
          pullback.condition]) ≫
        (F.mapComp' (pullback.fst (f i₂) g).op.toLoc y.op.toLoc yf.op.toLoc
          (by rw [← hyf]; rfl)).hom.toNatTrans.app _ =
      ((F.mapComp' (pullback.snd (f i₁) g).op.toLoc x.op.toLoc v.op.toLoc
          (by rw [← hx]; rfl)).inv.toNatTrans.app s.obj ≫
        (F.mapComp' (pullback.snd (f i₂) g).op.toLoc y.op.toLoc v.op.toLoc
          (by rw [← hy]; rfl)).hom.toNatTrans.app s.obj) ≫
        (F.map y.op.toLoc).toFunctor.map (s.eH i₂) := by
  have h := s.iso.hom.comm v x y hx hy
  rw [res_hom f D g v x y hx hy xf yf hxf hyf, toDescentData_obj_hom] at h
  exact h

/-- **The components of a solution intertwine the descent datum.** -/
lemma pullHom_eH_comp_hom {W : C} (v : W ⟶ Y) {i₁ i₂ : ι}
    (x : W ⟶ pullback (f i₁) g) (y : W ⟶ pullback (f i₂) g) (hx : x ≫ pullback.snd _ _ = v)
    (hy : y ≫ pullback.snd _ _ = v) (xf : W ⟶ Xi i₁) (yf : W ⟶ Xi i₂)
    (hxf : x ≫ pullback.fst _ _ = xf) (hyf : y ≫ pullback.fst _ _ = yf) (q : W ⟶ X)
    (hq : v ≫ g = q) :
    pullHom (s.eH i₁) x v xf hx hxf ≫
        D.hom q xf yf (by rw [← hxf, ← hq, ← hx, Category.assoc, Category.assoc,
          pullback.condition]) (by rw [← hyf, ← hq, ← hy, Category.assoc, Category.assoc,
          pullback.condition]) =
      pullHom (s.eH i₂) y v yf hy hyf := by
  subst hq
  have h := s.eH_comm v x y hx hy xf yf hxf hyf
  simp only [pullHom]
  rw [← cancel_mono ((F.mapComp' (pullback.fst (f i₂) g).op.toLoc y.op.toLoc yf.op.toLoc
    (by rw [← hyf]; rfl)).hom.toNatTrans.app _)]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  rw [h]
  simp

/-- The inverse components of a solution intertwine the descent datum. -/
lemma hom_comp_pullHom_eI {W : C} (v : W ⟶ Y) {i₁ i₂ : ι}
    (x : W ⟶ pullback (f i₁) g) (y : W ⟶ pullback (f i₂) g) (hx : x ≫ pullback.snd _ _ = v)
    (hy : y ≫ pullback.snd _ _ = v) (xf : W ⟶ Xi i₁) (yf : W ⟶ Xi i₂)
    (hxf : x ≫ pullback.fst _ _ = xf) (hyf : y ≫ pullback.fst _ _ = yf) (q : W ⟶ X)
    (hq : v ≫ g = q) :
    D.hom q xf yf (by rw [← hxf, ← hq, ← hx, Category.assoc, Category.assoc,
          pullback.condition]) (by rw [← hyf, ← hq, ← hy, Category.assoc, Category.assoc,
          pullback.condition]) ≫ pullHom (s.eI i₂) y yf v hyf hy =
      pullHom (s.eI i₁) x xf v hxf hx := by
  rw [← cancel_epi (pullHom (s.eH i₁) x v xf hx hxf),
    reassoc_of% (s.pullHom_eH_comp_hom v x y hx hy xf yf hxf hyf q hq),
    pullHom_eH_eI, pullHom_eH_eI]

end Sol

/-! ### The comparison of two solutions -/

section Cmp

variable {Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ X} {g₂ : Y₂ ⟶ X} {g₃ : Y₃ ⟶ X}

/-- The local comparison of two solutions through the member `i` of the family. -/
def σ (s₁ : Sol f D g₁) (s₂ : Sol f D g₂) {W : C} {i : ι} (x : W ⟶ pullback (f i) g₁)
    (y : W ⟶ pullback (f i) g₂) (a : W ⟶ Y₁) (b : W ⟶ Y₂) (e : W ⟶ Xi i)
    (hxa : x ≫ pullback.snd _ _ = a) (hxe : x ≫ pullback.fst _ _ = e)
    (hyb : y ≫ pullback.snd _ _ = b) (hye : y ≫ pullback.fst _ _ = e) :
    (F.map a.op.toLoc).toFunctor.obj s₁.obj ⟶ (F.map b.op.toLoc).toFunctor.obj s₂.obj :=
  pullHom (s₁.eH i) x a e hxa hxe ≫ pullHom (s₂.eI i) y e b hye hyb

variable (s₁ : Sol f D g₁) (s₂ : Sol f D g₂) (s₃ : Sol f D g₃)

/-- The local comparison `σ` depends only on the morphisms `x`, `y` and `e`, not on the proofs of
their compatibilities. -/
lemma σ_congr {W : C} {i : ι} {x x' : W ⟶ pullback (f i) g₁} {y y' : W ⟶ pullback (f i) g₂}
    (hx : x = x') (hy : y = y') (a : W ⟶ Y₁) (b : W ⟶ Y₂) {e e' : W ⟶ Xi i} (he : e = e')
    (hxa : x ≫ pullback.snd _ _ = a) (hxe : x ≫ pullback.fst _ _ = e)
    (hyb : y ≫ pullback.snd _ _ = b) (hye : y ≫ pullback.fst _ _ = e)
    (hxa' : x' ≫ pullback.snd _ _ = a) (hxe' : x' ≫ pullback.fst _ _ = e')
    (hyb' : y' ≫ pullback.snd _ _ = b) (hye' : y' ≫ pullback.fst _ _ = e') :
    σ s₁ s₂ x y a b e hxa hxe hyb hye = σ s₁ s₂ x' y' a b e' hxa' hxe' hyb' hye' := by
  subst hx hy he
  rfl

/-- The base change of a local comparison along `w` is the local comparison at the composites with
`w`. -/
lemma pullHom_σ {W : C} {i : ι} (x : W ⟶ pullback (f i) g₁)
    (y : W ⟶ pullback (f i) g₂) (a : W ⟶ Y₁) (b : W ⟶ Y₂) (e : W ⟶ Xi i)
    (hxa : x ≫ pullback.snd _ _ = a) (hxe : x ≫ pullback.fst _ _ = e)
    (hyb : y ≫ pullback.snd _ _ = b) (hye : y ≫ pullback.fst _ _ = e) {W' : C} (w : W' ⟶ W)
    (wa : W' ⟶ Y₁) (wb : W' ⟶ Y₂) (hwa : w ≫ a = wa) (hwb : w ≫ b = wb) :
    pullHom (σ s₁ s₂ x y a b e hxa hxe hyb hye) w wa wb hwa hwb =
      σ s₁ s₂ (w ≫ x) (w ≫ y) wa wb (w ≫ e) (by rw [Category.assoc, hxa, hwa])
        (by rw [Category.assoc, hxe]) (by rw [Category.assoc, hyb, hwb])
        (by rw [Category.assoc, hye]) := by
  rw [σ, ← pullHom_comp _ _ w wa (w ≫ e) wb hwa rfl hwb, pullHom_pullHom,
    pullHom_pullHom]
  rfl

/-- The local comparisons through two members of the family agree. -/
lemma σ_indep {W : C} {i i' : ι} (x : W ⟶ pullback (f i) g₁) (y : W ⟶ pullback (f i) g₂)
    (x' : W ⟶ pullback (f i') g₁) (y' : W ⟶ pullback (f i') g₂) (a : W ⟶ Y₁) (b : W ⟶ Y₂)
    (hab : a ≫ g₁ = b ≫ g₂) (e : W ⟶ Xi i) (e' : W ⟶ Xi i')
    (hxa : x ≫ pullback.snd _ _ = a) (hxe : x ≫ pullback.fst _ _ = e)
    (hyb : y ≫ pullback.snd _ _ = b) (hye : y ≫ pullback.fst _ _ = e)
    (hxa' : x' ≫ pullback.snd _ _ = a) (hxe' : x' ≫ pullback.fst _ _ = e')
    (hyb' : y' ≫ pullback.snd _ _ = b) (hye' : y' ≫ pullback.fst _ _ = e') :
    σ s₁ s₂ x y a b e hxa hxe hyb hye = σ s₁ s₂ x' y' a b e' hxa' hxe' hyb' hye' := by
  rw [σ, σ, ← s₁.pullHom_eH_comp_hom a x x' hxa hxa' e e' hxe hxe' (a ≫ g₁) rfl,
    Category.assoc, s₂.hom_comp_pullHom_eI b y y' hyb hyb' e e' hye hye' (a ≫ g₁) hab.symm]

/-- The composite of the local comparisons of `s₁` with `s₂` and of `s₂` with `s₃` is the local
comparison of `s₁` with `s₃`. -/
lemma σ_trans {W : C} {i : ι} (x : W ⟶ pullback (f i) g₁) (y : W ⟶ pullback (f i) g₂)
    (z : W ⟶ pullback (f i) g₃) (a : W ⟶ Y₁) (b : W ⟶ Y₂) (c : W ⟶ Y₃) (e : W ⟶ Xi i)
    (hxa : x ≫ pullback.snd _ _ = a) (hxe : x ≫ pullback.fst _ _ = e)
    (hyb : y ≫ pullback.snd _ _ = b) (hye : y ≫ pullback.fst _ _ = e)
    (hzc : z ≫ pullback.snd _ _ = c) (hze : z ≫ pullback.fst _ _ = e) :
    σ s₁ s₂ x y a b e hxa hxe hyb hye ≫ σ s₂ s₃ y z b c e hyb hye hzc hze =
      σ s₁ s₃ x z a c e hxa hxe hzc hze := by
  simp only [σ, Category.assoc, Sol.pullHom_eI_eH_assoc]

/-- The local comparison of a solution with itself is the identity. -/
lemma σ_self {W : C} {i : ι} (x : W ⟶ pullback (f i) g₁) (a : W ⟶ Y₁) (e : W ⟶ Xi i)
    (hxa : x ≫ pullback.snd _ _ = a) (hxe : x ≫ pullback.fst _ _ = e) :
    σ s₁ s₁ x x a a e hxa hxe hxa hxe = 𝟙 _ := by
  simp only [σ, Sol.pullHom_eH_eI]

variable {J : GrothendieckTopology C} [F.IsPrestack J] (hf : Sieve.ofArrows Xi f ∈ J X)

/-- The first leg into the base change of `f` along `g₁`. -/
abbrev legA {Z : C} (a : Z ⟶ Y₁) (i : ι) :
    pullback (f i) (a ≫ g₁) ⟶ pullback (f i) g₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by rw [pullback.condition,
    Category.assoc])

/-- The second leg into the base change of `f` along `g₂`. -/
abbrev legB {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂) (i : ι) :
    pullback (f i) (a ≫ g₁) ⟶ pullback (f i) g₂ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b) (by
    rw [pullback.condition, Category.assoc]
    exact congrArg (fun t ↦ pullback.snd (f i) (a ≫ g₁) ≫ t) hab)

include hf in
/-- There is a morphism between the pullbacks of two solutions along `a` and `b` whose base change
through each member of the base change of `f` is the local comparison `σ`. -/
lemma exists_cmp {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂) :
    ∃ φ : (F.map a.op.toLoc).toFunctor.obj s₁.obj ⟶ (F.map b.op.toLoc).toFunctor.obj s₂.obj,
      ∀ i, pullHom φ (pullback.snd (f i) (a ≫ g₁)) (pullback.snd _ _ ≫ a)
        (pullback.snd _ _ ≫ b) rfl rfl =
        σ s₁ s₂ (legA a i) (legB a b hab i) (pullback.snd _ _ ≫ a) (pullback.snd _ _ ≫ b)
          (pullback.fst _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
          (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) := by
  refine exists_pullHom_eq_of_fullyFaithful (fun i ↦ pullback.snd (f i) (a ≫ g₁))
    (F.fullyFaithfulToDescentData _ (ofArrows_pullback_mem hf (a ≫ g₁))) s₁.obj s₂.obj a b
    _ ?_
  intro W q i j u₁ u₂ hu₁ hu₂
  rw [pullHom_σ, pullHom_σ]
  exact σ_indep s₁ s₂ _ _ _ _ (q ≫ a) (q ≫ b) (by rw [Category.assoc, hab, Category.assoc])
    _ _ _ _ _ _ _ _ _ _

/-- **The comparison of two solutions** over `a : Z ⟶ Y₁` and `b : Z ⟶ Y₂`. -/
def cmp {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂) :
    (F.map a.op.toLoc).toFunctor.obj s₁.obj ⟶ (F.map b.op.toLoc).toFunctor.obj s₂.obj :=
  (exists_cmp s₁ s₂ hf a b hab).choose

/-- The comparison of two solutions, read through any member of the family. -/
lemma pullHom_cmp {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂) {W : C}
    (w : W ⟶ Z) (wa : W ⟶ Y₁) (wb : W ⟶ Y₂) (hwa : w ≫ a = wa) (hwb : w ≫ b = wb) {i : ι}
    (x : W ⟶ pullback (f i) g₁) (y : W ⟶ pullback (f i) g₂) (e : W ⟶ Xi i)
    (hxa : x ≫ pullback.snd _ _ = wa) (hxe : x ≫ pullback.fst _ _ = e)
    (hyb : y ≫ pullback.snd _ _ = wb) (hye : y ≫ pullback.fst _ _ = e) :
    pullHom (cmp s₁ s₂ hf a b hab) w wa wb hwa hwb = σ s₁ s₂ x y wa wb e hxa hxe hyb hye := by
  have hu : e ≫ f i = w ≫ a ≫ g₁ := by
    rw [← hxe, Category.assoc, pullback.condition, ← Category.assoc, hxa, ← hwa,
      Category.assoc]
  let u : W ⟶ pullback (f i) (a ≫ g₁) := pullback.lift e w hu
  have hu₁ : u ≫ legA a i = x := by
    apply pullback.hom_ext
    · dsimp only [u, legA]
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hxe]
    · dsimp only [u, legA]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hxa, hwa]
  have hu₂ : u ≫ legB a b hab i = y := by
    apply pullback.hom_ext
    · dsimp only [u, legB]
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hye]
    · dsimp only [u, legB]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hyb, hwb]
  rw [pullHom_eq_pullHom_of_snd (cmp s₁ s₂ hf a b hab)
    ((exists_cmp s₁ s₂ hf a b hab).choose_spec i) u w
    (pullback.lift_snd _ _ _) wa wb hwa hwb, pullHom_σ]
  exact σ_congr s₁ s₂ hu₁ hu₂ wa wb (pullback.lift_fst e w hu) _ _ _ _ _ _ _ _

include hf in
/-- **Base change of the comparison of two solutions.** -/
lemma pullHom_cmp_eq {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂) {W : C}
    (w : W ⟶ Z) (wa : W ⟶ Y₁) (wb : W ⟶ Y₂) (hwa : w ≫ a = wa) (hwb : w ≫ b = wb) :
    pullHom (cmp s₁ s₂ hf a b hab) w wa wb hwa hwb =
      cmp s₁ s₂ hf wa wb (by rw [← hwa, ← hwb, Category.assoc, Category.assoc, hab]) := by
  have hab' : wa ≫ g₁ = wb ≫ g₂ := by rw [← hwa, ← hwb, Category.assoc, Category.assoc, hab]
  refine eq_of_pullHom_snd_eq hf (wa ≫ g₁) _ _ (fun i ↦ ?_)
  rw [pullHom_pullHom, pullHom_cmp s₁ s₂ hf a b hab _ _ _ _ _ (legA wa i) (legB wa wb hab' i)
      (pullback.fst _ _) (by rw [pullback.lift_snd]) (pullback.lift_fst _ _ _)
      (by rw [pullback.lift_snd]) (pullback.lift_fst _ _ _),
    pullHom_cmp s₁ s₂ hf wa wb hab' _ _ _ _ _ (legA wa i) (legB wa wb hab' i)
      (pullback.fst _ _) (by rw [pullback.lift_snd]) (pullback.lift_fst _ _ _)
      (by rw [pullback.lift_snd]) (pullback.lift_fst _ _ _)]

include hf in
/-- **The cocycle condition for the comparisons of solutions.** -/
lemma cmp_comp_cmp {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (c : Z ⟶ Y₃) (hab : a ≫ g₁ = b ≫ g₂)
    (hbc : b ≫ g₂ = c ≫ g₃) :
    cmp s₁ s₂ hf a b hab ≫ cmp s₂ s₃ hf b c hbc = cmp s₁ s₃ hf a c (hab.trans hbc) := by
  refine eq_of_pullHom_snd_eq hf (a ≫ g₁) _ _ (fun i ↦ ?_)
  rw [← pullHom_comp _ _ _ _ (pullback.snd _ _ ≫ b) _ rfl rfl rfl,
    pullHom_cmp s₁ s₂ hf a b hab _ _ _ _ _ (legA a i) (legB a b hab i)
      (pullback.fst _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _),
    pullHom_cmp s₂ s₃ hf b c hbc _ _ _ _ _ (legB a b hab i) (legB a c (hab.trans hbc) i)
      (pullback.fst _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _),
    pullHom_cmp s₁ s₃ hf a c (hab.trans hbc) _ _ _ _ _ (legA a i) (legB a c (hab.trans hbc) i)
      (pullback.fst _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _), σ_trans]

include hf in
/-- The comparison of a solution with itself is the identity. -/
lemma cmp_self {Z : C} (a : Z ⟶ Y₁) : cmp s₁ s₁ hf a a rfl = 𝟙 _ := by
  refine eq_of_pullHom_snd_eq hf (a ≫ g₁) _ _ (fun i ↦ ?_)
  rw [pullHom_cmp s₁ s₁ hf a a rfl _ _ _ _ _ (legA a i) (legA a i)
      (pullback.fst _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _), σ_self, pullHom_id_self]

include hf in
/-- The comparison of `s₂` with `s₁` is a right inverse of the comparison of `s₁` with `s₂`. -/
lemma cmp_comp_cmp_symm {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂) :
    cmp s₁ s₂ hf a b hab ≫ cmp s₂ s₁ hf b a hab.symm = 𝟙 _ := by
  rw [cmp_comp_cmp, cmp_self]

/-- The comparison of two solutions is an isomorphism. -/
instance isIso_cmp {Z : C} (a : Z ⟶ Y₁) (b : Z ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂) :
    IsIso (cmp s₁ s₂ hf a b hab) :=
  ⟨cmp s₂ s₁ hf b a hab.symm, cmp_comp_cmp_symm s₁ s₂ hf a b hab,
    cmp_comp_cmp_symm s₂ s₁ hf b a hab.symm⟩

/-! ### The canonical solutions -/

/-- The compatibility of the gluing morphisms of `D` with the restriction of `D` to a member of
the family, with the restricted gluing morphisms written out. -/
lemma can_comm' (i : ι) {W : C} {i₁ i₂ : ι} (x : W ⟶ pullback (f i₁) (f i))
    (y : W ⟶ pullback (f i₂) (f i)) (hy : y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _) :
    (F.map x.op.toLoc).toFunctor.map
        (D.hom (pullback.snd (f i₁) (f i) ≫ f i) (pullback.snd _ _) (pullback.fst _ _) rfl
          pullback.condition) ≫
        (F.mapComp' (pullback.fst (f i₁) (f i)).op.toLoc x.op.toLoc
          (x ≫ pullback.fst _ _).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app _ ≫
        D.hom ((x ≫ pullback.snd _ _) ≫ f i) (x ≫ pullback.fst _ _) (y ≫ pullback.fst _ _)
          (by rw [Category.assoc, Category.assoc, pullback.condition])
          (by rw [Category.assoc, pullback.condition, ← Category.assoc, hy]) ≫
        (F.mapComp' (pullback.fst (f i₂) (f i)).op.toLoc y.op.toLoc
          (y ≫ pullback.fst _ _).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app _ =
      ((F.mapComp' (pullback.snd (f i₁) (f i)).op.toLoc x.op.toLoc
          (x ≫ pullback.snd _ _).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          (D.obj i) ≫
        (F.mapComp' (pullback.snd (f i₂) (f i)).op.toLoc y.op.toLoc
          (x ≫ pullback.snd _ _).op.toLoc
          (by rw [← hy, ← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (D.obj i)) ≫
        (F.map y.op.toLoc).toFunctor.map
          (D.hom (pullback.snd (f i₂) (f i) ≫ f i) (pullback.snd _ _) (pullback.fst _ _) rfl
            pullback.condition) := by
  have e1 := map_eq_pullHom (D.hom (pullback.snd (f i₁) (f i) ≫ f i) (pullback.snd _ _)
    (pullback.fst _ _) rfl pullback.condition) x (x ≫ pullback.snd _ _) (x ≫ pullback.fst _ _)
    rfl rfl
  have e2 := map_eq_pullHom (D.hom (pullback.snd (f i₂) (f i) ≫ f i) (pullback.snd _ _)
    (pullback.fst _ _) rfl pullback.condition) y (x ≫ pullback.snd _ _) (y ≫ pullback.fst _ _)
    hy rfl
  rw [D.pullHom_hom x _ ((x ≫ pullback.snd _ _) ≫ f i) (by rw [Category.assoc])
    (pullback.snd _ _) (pullback.fst _ _) rfl pullback.condition _ _ rfl rfl] at e1
  rw [D.pullHom_hom y _ ((x ≫ pullback.snd _ _) ≫ f i) (by rw [← Category.assoc, hy])
    (pullback.snd _ _) (pullback.fst _ _) rfl pullback.condition _ _ hy rfl] at e2
  rw [e1, e2]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, D.hom_comp_assoc]

/-- The compatibility of the gluing morphisms of `D` with the restriction of `D` to a member of
the family. -/
lemma can_comm (i : ι) {W : C} (v : W ⟶ Xi i) {i₁ i₂ : ι} (x : W ⟶ pullback (f i₁) (f i))
    (y : W ⟶ pullback (f i₂) (f i)) (hx : x ≫ pullback.snd _ _ = v)
    (hy : y ≫ pullback.snd _ _ = v) :
    (F.map x.op.toLoc).toFunctor.map
        (D.hom (pullback.snd (f i₁) (f i) ≫ f i) (pullback.snd _ _) (pullback.fst _ _) rfl
          pullback.condition) ≫ (res f D (f i)).hom v x y hx hy =
      ((F.toDescentData (fun i' ↦ pullback.snd (f i') (f i))).obj (D.obj i)).hom v x y hx hy ≫
        (F.map y.op.toLoc).toFunctor.map
          (D.hom (pullback.snd (f i₂) (f i) ≫ f i) (pullback.snd _ _) (pullback.fst _ _) rfl
            pullback.condition) := by
  subst hx
  rw [res_hom f D (f i) _ x y rfl hy _ _ rfl rfl,
    toDescentData_obj_hom (F := F) (fun i' ↦ pullback.snd (f i') (f i)) (D.obj i)
      (x ≫ pullback.snd _ _) x y rfl hy]
  exact can_comm' i x y hy

/-- The canonical solution of `D` over a member `f i` of the family: the object `D.obj i`, with
the gluing isomorphisms of `D`. -/
abbrev can (i : ι) : Sol f D (f i) where
  obj := D.obj i
  iso := DescentData.isoMk (fun i' ↦ D.iso (pullback.snd (f i') (f i) ≫ f i)
      (pullback.snd _ _) (pullback.fst _ _) rfl pullback.condition)
    (fun _ v _ _ x y hx hy ↦ can_comm i v x y hx hy)

/-- The components of the canonical solution over `f i` are gluing morphisms of `D`. -/
lemma can_eH (i i' : ι) : (can (D := D) i).eH i' =
    D.hom (pullback.snd (f i') (f i) ≫ f i) (pullback.snd _ _) (pullback.fst _ _) rfl
      pullback.condition := rfl

/-- The inverse components of the canonical solution over `f i` are gluing morphisms of `D`. -/
lemma can_eI (i i' : ι) : (can (D := D) i).eI i' =
    D.hom (pullback.snd (f i') (f i) ≫ f i) (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition rfl := rfl

include hf in
/-- The comparison of two canonical solutions is the gluing morphism of `D`. -/
lemma cmp_can {Z : C} {i₁ i₂ : ι} (x₁ : Z ⟶ Xi i₁) (x₂ : Z ⟶ Xi i₂)
    (h : x₁ ≫ f i₁ = x₂ ≫ f i₂) (q : Z ⟶ X) (hq₁ : x₁ ≫ f i₁ = q) (hq₂ : x₂ ≫ f i₂ = q) :
    cmp (can (D := D) i₁) (can i₂) hf x₁ x₂ h = D.hom q x₁ x₂ hq₁ hq₂ := by
  subst hq₁
  refine eq_of_pullHom_snd_eq hf (x₁ ≫ f i₁) _ _ (fun i ↦ ?_)
  rw [pullHom_cmp _ _ hf x₁ x₂ h _ _ _ _ _ (legA x₁ i) (legB x₁ x₂ h i)
      (pullback.fst _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _), σ, can_eH, can_eI,
    D.pullHom_hom _ _ (pullback.snd (f i) (x₁ ≫ f i₁) ≫ x₁ ≫ f i₁) (by
      rw [← Category.assoc, pullback.lift_snd, Category.assoc]),
    D.pullHom_hom _ _ (pullback.snd (f i) (x₁ ≫ f i₁) ≫ x₁ ≫ f i₁) (by
      rw [← Category.assoc, pullback.lift_snd, Category.assoc]
      exact (congrArg (fun t ↦ pullback.snd (f i) (x₁ ≫ f i₁) ≫ t) h).symm),
    D.hom_comp, D.pullHom_hom _ _ (pullback.snd (f i) (x₁ ≫ f i₁) ≫ x₁ ≫ f i₁) rfl x₁ x₂ rfl
      h.symm _ _ rfl rfl]
  all_goals first | exact pullback.condition | exact pullback.lift_fst _ _ _ |
    exact pullback.lift_snd _ _ _ | rfl

end Cmp

/-! ### Gluing the local solutions -/

section Main

variable {J : GrothendieckTopology C} [F.IsPrestack J] (hf : Sieve.ofArrows Xi f ∈ J X)
  {κ : Type t'} {Y : κ → C} (r : ∀ j, Y j ⟶ X)
  (hloc : ∀ j, (F.toDescentData (fun i ↦ pullback.snd (f i) (r j))).IsEquivalence)

variable (D) in
/-- The solution of `D` over a member of the family `r`, given by effective descent along the
base change of `f`. -/
def locSol (j : κ) : Sol f D (r j) :=
  letI := hloc j
  ⟨(F.toDescentData _).objPreimage (res f D (r j)),
    (F.toDescentData _).objObjPreimageIso (res f D (r j))⟩

include hf in
/-- The composite `θ ζ a c hc ≫ cmp s₁ s₂ hf a b hab` depends only on the morphism `a`, not on the
proofs of its compatibilities. -/
lemma θ_comp_cmp_congr {X' Y₁ Y₂ : C} {h : Y₁ ⟶ X'} {M : F.obj (.mk (op X'))}
    {g₁ : Y₁ ⟶ X} {g₂ : Y₂ ⟶ X} {s₁ : Sol f D g₁} (s₂ : Sol f D g₂)
    (ζ : (F.map h.op.toLoc).toFunctor.obj M ⟶ s₁.obj) {W : C} {a a' : W ⟶ Y₁} (ha : a = a')
    (c : W ⟶ X') (hc : a ≫ h = c) (hc' : a' ≫ h = c) (b : W ⟶ Y₂) (hab : a ≫ g₁ = b ≫ g₂)
    (hab' : a' ≫ g₁ = b ≫ g₂) :
    θ ζ a c hc ≫ cmp s₁ s₂ hf a b hab = θ ζ a' c hc' ≫ cmp s₁ s₂ hf a' b hab' := by
  subst ha
  rfl

/-- The triple overlaps of the family `r`. -/
abbrev triple (j k l : κ) : C := pullback (pullback.snd (r j) (r k)) (pullback.fst (r k) (r l))

/-- The projection of a triple overlap to the overlap of the outer two members. -/
abbrev triple₁₃ (j k l : κ) : triple r j k l ⟶ pullback (r j) (r l) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      pullback.condition, Category.assoc])

include hf in
/-- **The local solutions glue.** -/
lemma exists_glue [(F.toDescentData r).IsEquivalence] :
    ∃ (M : F.obj (.mk (op X)))
      (ε : ∀ j, (F.map (r j).op.toLoc).toFunctor.obj M ≅ (locSol D r hloc j).obj),
      ∀ (j k : κ) {W : C} (a : W ⟶ Y j) (b : W ⟶ Y k) (c : W ⟶ X) (ha : a ≫ r j = c)
        (hb : b ≫ r k = c),
        θ (ε j).hom a c ha ≫ cmp (locSol D r hloc j) (locSol D r hloc k) hf a b
          (ha.trans hb.symm) = θ (ε k).hom b c hb := by
  obtain ⟨M, ε, hε⟩ := exists_iso_of_isEquivalence_toDescentData_of_isPullback F r
    (fun j k ↦ pullback (r j) (r k)) (fun j k ↦ pullback.fst _ _) (fun j k ↦ pullback.snd _ _)
    (fun j k ↦ pullback.fst _ _ ≫ r j) (fun j k ↦ IsPullback.of_hasPullback _ _)
    (fun _ _ ↦ rfl) (fun _ _ ↦ pullback.condition.symm) (triple r)
    (fun j k l ↦ pullback.fst _ _) (fun j k l ↦ pullback.snd _ _) (triple₁₃ r)
    (fun j k l ↦ IsPullback.of_hasPullback _ _)
    (fun j k l ↦ pullback.fst _ _ ≫ pullback.fst _ _)
    (fun j k l ↦ pullback.fst _ _ ≫ pullback.snd _ _)
    (fun j k l ↦ pullback.snd _ _ ≫ pullback.snd _ _)
    (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ pullback.condition.symm) (fun _ _ _ ↦ rfl)
    (fun _ _ _ ↦ pullback.lift_fst _ _ _) (fun _ _ _ ↦ pullback.lift_snd _ _ _)
    (fun j ↦ (locSol D r hloc j).obj)
    (fun j k ↦ asIso (cmp (locSol D r hloc j) (locSol D r hloc k) hf (pullback.fst _ _)
      (pullback.snd _ _) pullback.condition)) (by
      intro j k l
      simp only [asIso_hom]
      rw [pullHom_cmp_eq, pullHom_cmp_eq, pullHom_cmp_eq, cmp_comp_cmp])
  refine ⟨M, ε, fun j k W a b c ha hb ↦ ?_⟩
  have h₀ : θ (ε j).hom (pullback.fst (r j) (r k)) (pullback.fst _ _ ≫ r j) rfl ≫
      cmp (locSol D r hloc j) (locSol D r hloc k) hf (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition =
      θ (ε k).hom (pullback.snd (r j) (r k)) (pullback.fst _ _ ≫ r j)
        pullback.condition.symm := by
    have h := hε j k
    rw [asIso_hom, toDescentData_obj_hom] at h
    have h2 := congrArg (fun t ↦ (F.mapComp' (r j).op.toLoc (pullback.fst (r j) (r k)).op.toLoc
      (pullback.fst _ _ ≫ r j).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app M ≫ t) h
    refine (Category.assoc _ _ _).trans (h2.trans ?_)
    exact (congrArg _ (Category.assoc _ _ _)).trans
      (Cat.Hom.hom_inv_id_toNatTrans_app_assoc _ _ _)
  have hw : a ≫ r j = b ≫ r k := ha.trans hb.symm
  have h₁ := congrArg (fun φ ↦ pullHom φ (pullback.lift a b hw) c b
    (by rw [← Category.assoc, pullback.lift_fst, ha])
    (pullback.lift_snd _ _ _)) h₀
  rw [← pullHom_comp _ _ _ _ a _ _ (pullback.lift_fst _ _ _), pullHom_θ, pullHom_cmp_eq,
    pullHom_θ] at h₁
  exact h₁

variable [(F.toDescentData r).IsEquivalence]

variable (D) in
/-- The glued object. -/
def gM : F.obj (.mk (op X)) := (exists_glue hf r hloc (D := D)).choose

variable (D) in
/-- The identification of the glued object with the local solutions. -/
def gε (j : κ) :
    (F.map (r j).op.toLoc).toFunctor.obj (gM (D := D) hf r hloc) ≅ (locSol D r hloc j).obj :=
  (exists_glue hf r hloc (D := D)).choose_spec.choose j

/-- The identifications `gε` of the glued object with the local solutions are compatible with the
comparisons of the local solutions. -/
lemma gε_compat (j k : κ) {W : C} (a : W ⟶ Y j) (b : W ⟶ Y k) (c : W ⟶ X)
    (ha : a ≫ r j = c) (hb : b ≫ r k = c) :
    θ (gε (D := D) hf r hloc j).hom a c ha ≫ cmp (locSol D r hloc j) (locSol D r hloc k) hf a b
      (ha.trans hb.symm) = θ (gε (D := D) hf r hloc k).hom b c hb :=
  (exists_glue hf r hloc (D := D)).choose_spec.choose_spec j k a b c ha hb

/-- The local piece of the comparison of the glued object with `D` over `X i`. -/
def locPiece (i : ι) (j : κ) :
    (F.map (pullback.snd (r j) (f i) ≫ f i).op.toLoc).toFunctor.obj (gM (D := D) hf r hloc) ⟶
      (F.map (pullback.snd (r j) (f i) ≫ 𝟙 (Xi i)).op.toLoc).toFunctor.obj (D.obj i) :=
  θ (gε (D := D) hf r hloc j).hom (pullback.fst _ _) (pullback.snd _ _ ≫ f i) pullback.condition ≫
    cmp (locSol D r hloc j) (can i) hf (pullback.fst _ _) (pullback.snd _ _) pullback.condition ≫
    eqHom (D.obj i) (Category.comp_id _).symm

/-- The base change of `locPiece i j` along `n` is the composite of `θ`, the comparison with the
canonical solution over `f i`, and `eqHom`, at the composites with `n`. -/
lemma pullHom_locPiece (i : ι) (j : κ) {W : C} (n : W ⟶ pullback (r j) (f i)) (a : W ⟶ Y j)
    (u : W ⟶ Xi i) (c : W ⟶ X) (u' : W ⟶ Xi i) (hna : n ≫ pullback.fst _ _ = a)
    (hnu : n ≫ pullback.snd _ _ = u) (hc : n ≫ pullback.snd _ _ ≫ f i = c)
    (hu' : n ≫ pullback.snd _ _ ≫ 𝟙 _ = u') :
    pullHom (locPiece hf r hloc (D := D) i j) n c u' hc hu' =
      θ (gε (D := D) hf r hloc j).hom a c
          (by rw [← hna, Category.assoc, pullback.condition]; exact hc) ≫
        cmp (locSol D r hloc j) (can i) hf a u (by rw [← hna, ← hnu, Category.assoc,
          Category.assoc, pullback.condition]) ≫
        eqHom (D.obj i) (show u = u' by rw [← hu', Category.comp_id, hnu]) := by
  rw [locPiece, ← pullHom_comp _ _ n c a u' hc hna hu',
    ← pullHom_comp _ _ n a u u' hna hnu hu', pullHom_θ, pullHom_cmp_eq, pullHom_eqHom]

variable (hr : Sieve.ofArrows Y r ∈ J X)

include hr in
/-- There is a morphism from the pullback of the glued object along `f i` to `D.obj i` whose base
change to each member of the base change of `r` is `locPiece i j`. -/
lemma exists_ψ (i : ι) :
    ∃ ψ : (F.map (f i).op.toLoc).toFunctor.obj (gM (D := D) hf r hloc) ⟶
        (F.map (𝟙 (Xi i)).op.toLoc).toFunctor.obj (D.obj i),
      ∀ j, pullHom ψ (pullback.snd (r j) (f i)) (pullback.snd _ _ ≫ f i)
        (pullback.snd _ _ ≫ 𝟙 _) rfl rfl = locPiece hf r hloc (D := D) i j := by
  refine exists_pullHom_eq_of_fullyFaithful (fun j ↦ pullback.snd (r j) (f i))
    (F.fullyFaithfulToDescentData _ (ofArrows_pullback_mem hr (f i))) _ _ _ _ _ ?_
  intro W q j k u₁ u₂ h₁ h₂
  rw [pullHom_locPiece hf r hloc i j u₁ (u₁ ≫ pullback.fst _ _) q (q ≫ f i) (q ≫ 𝟙 _) rfl h₁
      (by rw [← Category.assoc, h₁]) (by rw [← Category.assoc, h₁]),
    pullHom_locPiece hf r hloc i k u₂ (u₂ ≫ pullback.fst _ _) q (q ≫ f i) (q ≫ 𝟙 _) rfl h₂
      (by rw [← Category.assoc, h₂]) (by rw [← Category.assoc, h₂]),
    ← cmp_comp_cmp (locSol D r hloc j) (locSol D r hloc k) (can i) hf
      (u₁ ≫ pullback.fst _ _) (u₂ ≫ pullback.fst _ _) q
      (by rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition,
        ← Category.assoc, ← Category.assoc, h₁, h₂])
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]),
    Category.assoc (cmp (locSol D r hloc j) (locSol D r hloc k) hf _ _ _),
    reassoc_of% (gε_compat hf r hloc j k (u₁ ≫ pullback.fst _ _) (u₂ ≫ pullback.fst _ _)
      (q ≫ f i) (by rw [Category.assoc, pullback.condition, ← Category.assoc, h₁])
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]))]

/-- The comparison of the glued object with `D` over `X i`. -/
def ψ (i : ι) : (F.map (f i).op.toLoc).toFunctor.obj (gM (D := D) hf r hloc) ⟶
    (F.map (𝟙 (Xi i)).op.toLoc).toFunctor.obj (D.obj i) :=
  (exists_ψ hf r hloc hr i).choose

/-- The base change of `ψ i` to the overlap of `Y j` with `X i` is `locPiece i j`. -/
lemma pullHom_ψ_snd (i : ι) (j : κ) :
    pullHom (ψ hf r hloc hr (D := D) i) (pullback.snd (r j) (f i)) (pullback.snd _ _ ≫ f i)
      (pullback.snd _ _ ≫ 𝟙 _) rfl rfl = locPiece hf r hloc (D := D) i j :=
  (exists_ψ hf r hloc hr (D := D) i).choose_spec j

/-- The base change of `ψ i` along `u` is, through any `a : W ⟶ Y j` over the same point of `X`,
the composite of `θ` and the comparison with the canonical solution over `f i`. -/
lemma pullHom_ψ (i : ι) {W : C} (u : W ⟶ Xi i) (c : W ⟶ X) (hc : u ≫ f i = c) (j : κ)
    (a : W ⟶ Y j) (ha : a ≫ r j = c) :
    pullHom (ψ hf r hloc hr (D := D) i) u c u hc (Category.comp_id u) =
      θ (gε (D := D) hf r hloc j).hom a c ha ≫
        cmp (locSol D r hloc j) (can i) hf a u (ha.trans hc.symm) := by
  have hn : a ≫ r j = u ≫ f i := ha.trans hc.symm
  rw [pullHom_eq_pullHom_of_snd _ (pullHom_ψ_snd hf r hloc hr (D := D) i j)
    (pullback.lift a u hn) u (pullback.lift_snd _ _ _) c u hc (Category.comp_id u),
    pullHom_locPiece hf r hloc i j _ a u c u (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)]
  simp only [eqHom_rfl, Category.comp_id]

include hr in
/-- **The comparison maps intertwine the descent datum**, written through base changes. -/
lemma pullHom_ψ_comp_hom {W : C} (q : W ⟶ X) {i₁ i₂ : ι} (x₁ : W ⟶ Xi i₁) (x₂ : W ⟶ Xi i₂)
    (hx₁ : x₁ ≫ f i₁ = q) (hx₂ : x₂ ≫ f i₂ = q) :
    pullHom (ψ hf r hloc hr (D := D) i₁) x₁ q x₁ hx₁ (Category.comp_id x₁) ≫
        D.hom q x₁ x₂ hx₁ hx₂ =
      pullHom (ψ hf r hloc hr (D := D) i₂) x₂ q x₂ hx₂ (Category.comp_id x₂) := by
  refine eq_of_pullHom_snd_eq hr q _ _ (fun j ↦ ?_)
  rw [← pullHom_comp _ _ _ _ (pullback.snd _ _ ≫ x₁) _ rfl rfl rfl, pullHom_pullHom,
    D.pullHom_hom _ _ (pullback.snd (r j) q ≫ q) rfl x₁ x₂ hx₁ hx₂ _ _ rfl rfl,
    pullHom_pullHom,
    pullHom_ψ hf r hloc hr i₁ _ _ (by rw [Category.assoc, hx₁]) j (pullback.fst _ _)
      pullback.condition,
    pullHom_ψ hf r hloc hr i₂ _ _ (by rw [Category.assoc, hx₂]) j (pullback.fst _ _)
      pullback.condition, Category.assoc,
    ← cmp_can hf (pullback.snd (r j) q ≫ x₁) (pullback.snd (r j) q ≫ x₂)
      (by rw [Category.assoc, Category.assoc, hx₁, hx₂]),
    cmp_comp_cmp]

/-- A component of the forward morphism of an isomorphism of functors is an isomorphism. -/
instance isIso_toNatTrans_hom_app {A B : Cat.{v', u'}} {G H : A ⟶ B} (e : G ≅ H) (x : A) :
    IsIso (e.hom.toNatTrans.app x) :=
  ⟨_, Cat.Hom.hom_inv_id_toNatTrans_app _ _, Cat.Hom.inv_hom_id_toNatTrans_app _ _⟩

/-- A component of the inverse of an isomorphism of functors is an isomorphism. -/
instance isIso_toNatTrans_inv_app {A B : Cat.{v', u'}} {G H : A ⟶ B} (e : G ≅ H) (x : A) :
    IsIso (e.inv.toNatTrans.app x) :=
  ⟨_, Cat.Hom.inv_hom_id_toNatTrans_app _ _, Cat.Hom.hom_inv_id_toNatTrans_app _ _⟩

/-- If `ζ` is an isomorphism, then so is `θ ζ a c hc`. -/
instance isIso_θ {X' Y' : C} {h : Y' ⟶ X'} {M : F.obj (.mk (op X'))} {N : F.obj (.mk (op Y'))}
    (ζ : (F.map h.op.toLoc).toFunctor.obj M ⟶ N) [IsIso ζ] {Z : C} (a : Z ⟶ Y') (c : Z ⟶ X')
    (hc : a ≫ h = c) : IsIso (θ ζ a c hc) := by
  dsimp only [θ]
  infer_instance

/-- The morphism `eqHom M₁ h` is an isomorphism, with inverse `eqHom M₁ h.symm`. -/
instance isIso_eqHom {X₁ : C} (M₁ : F.obj (.mk (op X₁))) {Y₁ : C} {u u' : Y₁ ⟶ X₁}
    (h : u = u') : IsIso (eqHom M₁ h) :=
  ⟨eqHom M₁ h.symm, by rw [eqHom_trans, eqHom_rfl], by rw [eqHom_trans, eqHom_rfl]⟩

/-- The base change of an isomorphism is an isomorphism. -/
instance isIso_pullHom {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y₁ : C} {f₁ : Y₁ ⟶ X₁} {f₂ : Y₁ ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso φ]
    {Y' : C} (g : Y' ⟶ Y₁) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) : IsIso (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) :=
  ⟨pullHom (inv φ) g gf₂ gf₁ hgf₂ hgf₁, by rw [pullHom_comp, IsIso.hom_inv_id, pullHom_id_self],
    by rw [pullHom_comp, IsIso.inv_hom_id, pullHom_id_self]⟩

include hr in
/-- The comparison `ψ i` of the glued object with `D` over `X i` is an isomorphism. -/
lemma isIso_ψ (i : ι) : IsIso (ψ hf r hloc hr (D := D) i) := by
  let hff := F.fullyFaithfulToDescentData _ (ofArrows_pullback_mem hr (f i))
  have : IsIso ((F.toDescentData (fun j ↦ pullback.snd (r j) (f i))).map
      (ψ hf r hloc hr (D := D) i)) := by
    refine descentData_isIso_of_components F _ (fun j ↦ ?_)
    change IsIso ((F.map (pullback.snd (r j) (f i)).op.toLoc).toFunctor.map
      (ψ hf r hloc hr (D := D) i))
    rw [map_eq_pullHom _ _ (pullback.snd _ _ ≫ f i) (pullback.snd _ _ ≫ 𝟙 _) rfl rfl,
      pullHom_ψ_snd]
    have : IsIso (locPiece hf r hloc (D := D) i j) := by
      dsimp only [locPiece]
      infer_instance
    infer_instance
  exact hff.isIso_of_isIso_map _

include hr in
/-- The comparisons `ψ` intertwine the canonical descent datum of the glued object with the
pullback of `D` along the identity. -/
lemma ψ_comm {W : C} (q : W ⟶ X) {i₁ i₂ : ι} (x₁ : W ⟶ Xi i₁) (x₂ : W ⟶ Xi i₂)
    (hx₁ : x₁ ≫ f i₁ = q) (hx₂ : x₂ ≫ f i₂ = q) :
    (F.map x₁.op.toLoc).toFunctor.map (ψ hf r hloc hr (D := D) i₁) ≫
        ((F.mapComp' (𝟙 (Xi i₁)).op.toLoc x₁.op.toLoc x₁.op.toLoc
            (by simp)).inv.toNatTrans.app (D.obj i₁) ≫
          D.hom q x₁ x₂ hx₁ hx₂ ≫
          (F.mapComp' (𝟙 (Xi i₂)).op.toLoc x₂.op.toLoc x₂.op.toLoc
            (by simp)).hom.toNatTrans.app (D.obj i₂)) =
      ((F.mapComp' (f i₁).op.toLoc x₁.op.toLoc q.op.toLoc
          (by rw [← hx₁]; rfl)).inv.toNatTrans.app (gM (D := D) hf r hloc) ≫
        (F.mapComp' (f i₂).op.toLoc x₂.op.toLoc q.op.toLoc
          (by rw [← hx₂]; rfl)).hom.toNatTrans.app (gM (D := D) hf r hloc)) ≫
        (F.map x₂.op.toLoc).toFunctor.map (ψ hf r hloc hr (D := D) i₂) := by
  rw [map_eq_pullHom _ x₁ q x₁ hx₁ (Category.comp_id x₁),
    map_eq_pullHom _ x₂ q x₂ hx₂ (Category.comp_id x₂)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [reassoc_of% (pullHom_ψ_comp_hom hf r hloc hr q x₁ x₂ hx₁ hx₂)]

include hr in
/-- The glued object is a preimage of `D`. -/
lemma nonempty_iso : Nonempty ((F.toDescentData f).obj (gM (D := D) hf r hloc) ≅ D) :=
  ⟨DescentData.isoMk (D₂ := resId f D)
    (fun i ↦ @asIso _ _ _ _ (ψ hf r hloc hr (D := D) i) (isIso_ψ hf r hloc hr (D := D) i))
    (fun W q i₁ i₂ x₁ x₂ hx₁ hx₂ ↦ by
      rw [resId_hom f D q x₁ x₂ hx₁ hx₂, toDescentData_obj_hom (F := F) f _ q x₁ x₂ hx₁ hx₂]
      exact ψ_comm hf r hloc hr q x₁ x₂ hx₁ hx₂) ≪≫
    (DescentData.pullFunctorIdIso F X).app D⟩

end Main

end StackTransitivity

open StackTransitivity in
/-- **Transitivity of effective descent.** Let `F` be a prestack for a Grothendieck topology `J`
on a category with fibre products, and let `f i : X i ⟶ X` and `r j : Y j ⟶ X` be covering
families. If descent is effective along `r` and along the base change of `f` to each `Y j`,
then descent is effective along `f`. -/
public theorem isEquivalence_toDescentData_of_isEquivalence_pullback
    {J : GrothendieckTopology C} [F.IsPrestack J] {X : C} {ι : Type t} {Xi : ι → C}
    (f : ∀ i, Xi i ⟶ X) (hf : Sieve.ofArrows Xi f ∈ J X) {κ : Type t'} {Y : κ → C}
    (r : ∀ j, Y j ⟶ X) (hr : Sieve.ofArrows Y r ∈ J X) [(F.toDescentData r).IsEquivalence]
    (hloc : ∀ j, (F.toDescentData (fun i ↦ pullback.snd (f i) (r j))).IsEquivalence) :
    (F.toDescentData f).IsEquivalence := by
  have hff := F.fullyFaithfulToDescentData f hf
  have := hff.full
  have := hff.faithful
  have : (F.toDescentData f).EssSurj :=
    ⟨fun D ↦ ⟨gM (D := D) hf r hloc, nonempty_iso hf r hloc hr (D := D)⟩⟩
  exact { }

end CategoryTheory.Pseudofunctor

end
