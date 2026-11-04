module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Abstract
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Descent

/-!
# Gluing data for small étale sheaves, read through inverse images

This file translates between the descent data of the pseudofunctor
`AlgebraicGeometry.SmallEtaleGluing.pseudofunctor` and gluing data phrased with the comparisons
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` of inverse images.

## Main definitions

* `AlgebraicGeometry.SmallEtaleGluing.pullbackTransition` — the inverse image of an isomorphism
  between two inverse images, identified through the composition comparisons.

## Main results

* `AlgebraicGeometry.SmallEtaleGluing.toDescentData_obj_hom` — the gluing isomorphisms of the
  canonical descent datum of a sheaf.
* `AlgebraicGeometry.SmallEtaleGluing.pullHom_eq_pullbackTransition` — pulling back a gluing
  isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

namespace SmallEtaleGluing

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {ι : Type*}


/-- Moving the identifications of a commutative square to the other side. -/
public theorem conj_of_eq {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (a₁ : X₁ ≅ Z₁)
    (b₁ : Y₁ ≅ Z₁) (a₂ : X₂ ≅ Z₂) (b₂ : Y₂ ≅ Z₂) (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂)
    (h : a₁.inv ≫ x ≫ a₂.hom = b₁.inv ≫ y ≫ b₂.hom) :
    x ≫ a₂.hom ≫ b₂.inv = (a₁.hom ≫ b₁.inv) ≫ y := by
  have := congrArg (fun z => a₁.hom ≫ z ≫ b₂.inv) h
  simpa using this

/-- Solving a commutative square with invertible vertical sides for its top side, the bottom side
being a composite. -/
public theorem iso_inv_comp_of_eq' {C : Type*} [Category C] {X X' Y Y' Z : C} (a : X ≅ X')
    (b : Y' ≅ Y) (x : X' ⟶ Y) (y₁ : X ⟶ Z) (y₂ : Z ⟶ Y') (h : a.hom ≫ x = (y₁ ≫ y₂) ≫ b.hom) :
    x = a.inv ≫ y₁ ≫ y₂ ≫ b.hom := by
  rw [← Category.assoc y₁, ← h, Iso.inv_hom_id_assoc]

/-- The gluing isomorphisms of the canonical descent datum of a sheaf, in terms of the
comparisons `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'`. -/
public theorem toDescentData_obj_hom {X : ι → B.Scheme} {S' : B.Scheme} (f : ∀ k, X k ⟶ S')
    (M : Sheaf (SmallEtale.topology B S'.obj S'.property) A) {Y : B.Scheme} (r : Y ⟶ S')
    {k l : ι} (f₁ : Y ⟶ X k) (f₂ : Y ⟶ X l) (hf₁ : f₁ ≫ f k = r) (hf₂ : f₂ ≫ f l = r) :
    (((pseudofunctor B A).toDescentData f).obj M).hom r f₁ f₂ hf₁ hf₂ =
      @CategoryStruct.comp (↑((pseudofunctor B A).obj ⟨op Y⟩)) _
        (((pseudofunctor B A).map f₁.op.toLoc).toFunctor.obj
          (((pseudofunctor B A).map (f k).op.toLoc).toFunctor.obj M))
        (((pseudofunctor B A).map r.op.toLoc).toFunctor.obj M)
        (((pseudofunctor B A).map f₂.op.toLoc).toFunctor.obj
          (((pseudofunctor B A).map (f l).op.toLoc).toFunctor.obj M))
      ((smallEtaleSheafPullbackCompIso' B A f₁ (f k) r hf₁).hom.app M)
        ((smallEtaleSheafPullbackCompIso' B A f₂ (f l) r hf₂).inv.app M) := by
  simp only [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  have h1 := pseudofunctor_mapComp'_inv_app B A f₁ (f k) r hf₁ (by rw [← hf₁]; rfl) M
  have h2 := pseudofunctor_mapComp'_hom_app B A f₂ (f l) r hf₂ (by rw [← hf₂]; rfl) M
  rw [h1, h2]

/-- The compatibility of a family of morphisms on an overlap `O` with maps `p`, `q` to two members
and a structure map `r` to the base, transported from the comparisons
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` to the canonical descent data. -/
public theorem toDescentData_comm_of_comp {X : ι → B.Scheme} {S' : B.Scheme}
    (f : ∀ k, X k ⟶ S') {k l : ι} {O : B.Scheme} (p : O ⟶ X k) (q : O ⟶ X l) (r : O ⟶ S')
    (hr₁ : p ≫ f k = r) (hr₂ : q ≫ f l = r)
    {F G : Sheaf (SmallEtale.topology B S'.obj S'.property) A}
    (φk : (smallEtaleSheafPullback B A (f k)).obj F ⟶ (smallEtaleSheafPullback B A (f k)).obj G)
    (φl : (smallEtaleSheafPullback B A (f l)).obj F ⟶ (smallEtaleSheafPullback B A (f l)).obj G)
    (h : (smallEtaleSheafPullbackCompIso' B A p (f k) r hr₁).inv.app F ≫
        (smallEtaleSheafPullback B A p).map φk ≫
          (smallEtaleSheafPullbackCompIso' B A p (f k) r hr₁).hom.app G =
      (smallEtaleSheafPullbackCompIso' B A q (f l) r hr₂).inv.app F ≫
        (smallEtaleSheafPullback B A q).map φl ≫
          (smallEtaleSheafPullbackCompIso' B A q (f l) r hr₂).hom.app G) :
    ((pseudofunctor B A).map p.op.toLoc).toFunctor.map φk ≫
        (((pseudofunctor B A).toDescentData f).obj G).hom r p q hr₁ hr₂ =
      (((pseudofunctor B A).toDescentData f).obj F).hom r p q hr₁ hr₂ ≫
        ((pseudofunctor B A).map q.op.toLoc).toFunctor.map φl := by
  rw [toDescentData_obj_hom B A f G r p q hr₁ hr₂, toDescentData_obj_hom B A f F r p q hr₁ hr₂]
  exact conj_of_eq ((smallEtaleSheafPullbackCompIso' B A p (f k) r hr₁).app F)
    ((smallEtaleSheafPullbackCompIso' B A q (f l) r hr₂).app F)
    ((smallEtaleSheafPullbackCompIso' B A p (f k) r hr₁).app G)
    ((smallEtaleSheafPullbackCompIso' B A q (f l) r hr₂).app G)
    ((smallEtaleSheafPullback B A p).map φk) ((smallEtaleSheafPullback B A q).map φl) h

/-- **The inverse image of a gluing isomorphism.** For an isomorphism `θ` between the inverse
images of `M₁` and `M₂` along `f₁` and `f₂`, its inverse image along `g`, read as an isomorphism
between the inverse images along named composites `gf₁ = g ≫ f₁` and `gf₂ = g ≫ f₂` through the
comparisons `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'`. -/
public def pullbackTransition {Y Y' X₁ X₂ : B.Scheme} (g : Y' ⟶ Y) {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {M₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) A}
    {M₂ : Sheaf (SmallEtale.topology B X₂.obj X₂.property) A}
    (θ : (smallEtaleSheafPullback B A f₁).obj M₁ ≅ (smallEtaleSheafPullback B A f₂).obj M₂)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    (smallEtaleSheafPullback B A gf₁).obj M₁ ≅ (smallEtaleSheafPullback B A gf₂).obj M₂ :=
  (smallEtaleSheafPullbackCompIso' B A g f₁ gf₁ h₁).symm.app M₁ ≪≫
    (smallEtaleSheafPullback B A g).mapIso θ ≪≫
      (smallEtaleSheafPullbackCompIso' B A g f₂ gf₂ h₂).app M₂

/-- Pulling back a gluing isomorphism in the pseudofunctor of inverse images is
`AlgebraicGeometry.SmallEtaleGluing.pullbackTransition`. -/
public theorem pullHom_eq_pullbackTransition {Y Y' X₁ X₂ : B.Scheme} (g : Y' ⟶ Y)
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {M₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) A}
    {M₂ : Sheaf (SmallEtale.topology B X₂.obj X₂.property) A}
    (θ : (smallEtaleSheafPullback B A f₁).obj M₁ ≅ (smallEtaleSheafPullback B A f₂).obj M₂)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pseudofunctor B A) θ.hom g gf₁ gf₂ h₁ h₂ =
      (pullbackTransition B A g θ gf₁ gf₂ h₁ h₂).hom := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have e1 := pseudofunctor_mapComp'_hom_app B A g f₁ gf₁ h₁ (by rw [← h₁]; rfl) M₁
  have e2 := pseudofunctor_mapComp'_inv_app B A g f₂ gf₂ h₂ (by rw [← h₂]; rfl) M₂
  rw [e1, e2]
  rfl

/-- The cocycle condition for a family of gluing isomorphisms on a triple overlap `T` with maps
`a₁₂`, `a₂₃`, `a₁₃` to the overlaps and `t₁`, `t₂`, `t₃` to the members, phrased with
`AlgebraicGeometry.SmallEtaleGluing.pullbackTransition`, is the cocycle condition for the pulled
back gluing morphisms of the pseudofunctor of inverse images. -/
public theorem pullHom_comp_of_cocycle {Xk Xl Xm Okl Olm Okm T : B.Scheme}
    {pkl : Okl ⟶ Xk} {qkl : Okl ⟶ Xl} {plm : Olm ⟶ Xl} {qlm : Olm ⟶ Xm}
    {pkm : Okm ⟶ Xk} {qkm : Okm ⟶ Xm} (a₁₂ : T ⟶ Okl) (a₂₃ : T ⟶ Olm) (a₁₃ : T ⟶ Okm)
    (t₁ : T ⟶ Xk) (t₂ : T ⟶ Xl) (t₃ : T ⟶ Xm)
    (h₁₂₁ : a₁₂ ≫ pkl = t₁) (h₁₂₂ : a₁₂ ≫ qkl = t₂) (h₂₃₁ : a₂₃ ≫ plm = t₂)
    (h₂₃₂ : a₂₃ ≫ qlm = t₃) (h₁₃₁ : a₁₃ ≫ pkm = t₁) (h₁₃₂ : a₁₃ ≫ qkm = t₃)
    {Gk : Sheaf (SmallEtale.topology B Xk.obj Xk.property) A}
    {Gl : Sheaf (SmallEtale.topology B Xl.obj Xl.property) A}
    {Gm : Sheaf (SmallEtale.topology B Xm.obj Xm.property) A}
    (θ₁₂ : (smallEtaleSheafPullback B A pkl).obj Gk ≅ (smallEtaleSheafPullback B A qkl).obj Gl)
    (θ₂₃ : (smallEtaleSheafPullback B A plm).obj Gl ≅ (smallEtaleSheafPullback B A qlm).obj Gm)
    (θ₁₃ : (smallEtaleSheafPullback B A pkm).obj Gk ≅ (smallEtaleSheafPullback B A qkm).obj Gm)
    (h : pullbackTransition B A a₁₂ θ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≪≫
        pullbackTransition B A a₂₃ θ₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
      pullbackTransition B A a₁₃ θ₁₃ t₁ t₃ h₁₃₁ h₁₃₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pseudofunctor B A) θ₁₂.hom a₁₂ t₁ t₂
        h₁₂₁ h₁₂₂ ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pseudofunctor B A) θ₂₃.hom a₂₃ t₂ t₃
        h₂₃₁ h₂₃₂ =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pseudofunctor B A) θ₁₃.hom a₁₃ t₁ t₃
      h₁₃₁ h₁₃₂ := by
  rw [pullHom_eq_pullbackTransition, pullHom_eq_pullbackTransition,
    pullHom_eq_pullbackTransition]
  exact congrArg Iso.hom h

/-- Reading off a gluing isomorphism on an overlap `O` with maps `p`, `q` to two members and a
structure map `r` to the base from a morphism of descent data. -/
public theorem iso_eq_of_comm {X : ι → B.Scheme} {S' : B.Scheme} (f : ∀ k, X k ⟶ S') {k l : ι}
    {O : B.Scheme} (p : O ⟶ X k) (q : O ⟶ X l) (r : O ⟶ S') (hr₁ : p ≫ f k = r)
    (hr₂ : q ≫ f l = r) (M : Sheaf (SmallEtale.topology B S'.obj S'.property) A)
    {Gk : Sheaf (SmallEtale.topology B (X k).obj (X k).property) A}
    {Gl : Sheaf (SmallEtale.topology B (X l).obj (X l).property) A}
    (εk : (smallEtaleSheafPullback B A (f k)).obj M ≅ Gk)
    (εl : (smallEtaleSheafPullback B A (f l)).obj M ≅ Gl)
    (θ : (smallEtaleSheafPullback B A p).obj Gk ≅ (smallEtaleSheafPullback B A q).obj Gl)
    (h : ((pseudofunctor B A).map p.op.toLoc).toFunctor.map εk.hom ≫ θ.hom =
      (((pseudofunctor B A).toDescentData f).obj M).hom r p q hr₁ hr₂ ≫
        ((pseudofunctor B A).map q.op.toLoc).toFunctor.map εl.hom) :
    (smallEtaleSheafPullback B A p).mapIso εk.symm ≪≫
        (smallEtaleSheafPullbackCompIso' B A p (f k) r hr₁).app M ≪≫
        (smallEtaleSheafPullbackCompIso' B A q (f l) r hr₂).symm.app M ≪≫
        (smallEtaleSheafPullback B A q).mapIso εl = θ := by
  rw [toDescentData_obj_hom B A f M r p q hr₁ hr₂] at h
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  exact (iso_inv_comp_of_eq' ((smallEtaleSheafPullback B A p).mapIso εk)
    ((smallEtaleSheafPullback B A q).mapIso εl) θ.hom _ _ h).symm

end SmallEtaleGluing

end AlgebraicGeometry

end
