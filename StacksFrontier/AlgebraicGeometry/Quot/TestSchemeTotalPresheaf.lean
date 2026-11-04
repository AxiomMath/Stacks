module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable

/-!
# Functors on the test schemes over an algebraic space, as presheaves over it

A functor `R : (SchemesOver Y)ᵒᵖ ⥤ Type w` on the test schemes over an algebraic space `Y`
determines a presheaf on the big fppf site, its *total presheaf*: its value at a scheme `T` is the
set of pairs of a section `y` of `Y` over `T` and an element of `R` at the test scheme `(T, y)`.
For `w = u` the projection to `y` is a morphism of presheaves to `Y`, whose fibres are the values
of `R`.  This is the dictionary between the functors on the test schemes, in which the
representability statements of the `Quot` chapter are phrased
(`AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver`), and the presheaves over
`Y`, on which the gluing results for algebraic spaces are proved.

## Main definitions

* `AlgebraicGeometry.Space.pointTestScheme`: the test scheme over `Y` that a section of `Y` is.
* `AlgebraicGeometry.Space.totalPresheaf`: the total presheaf of a functor on the test schemes.
* `AlgebraicGeometry.Space.IsFppfSheafOver`: a functor on the test schemes is an fppf sheaf over
  `Y` when its total presheaf is a sheaf.
* `AlgebraicGeometry.Space.totalProj`: the projection of the total presheaf to `Y`.

## Main results

* `AlgebraicGeometry.Space.spacePointsOverTotalProjIso`: the points over `Y` of the total
  presheaf, when it is an algebraic space, are the functor itself.
* `AlgebraicGeometry.Space.totalPresheafSpacePointsOverIso`: the total presheaf of the points of
  an algebraic space `H` over `Y` is `H`.
* `AlgebraicGeometry.Space.isPullback_totalPresheafRestrict`: the total presheaf of the
  restriction of a functor to the test schemes over a test scheme `V` over `Y` is the base change
  of the total presheaf along `V ⟶ Y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {Y : AlgebraicSpaces B S hS}

/-- Two composites of maps of a functor to types agree on an element when the composites of the
morphisms agree. -/
theorem _root_.CategoryTheory.FunctorToTypes.map_map_eq_of_comp_eq {C : Type*} [Category* C]
    (F : C ⥤ Type w) {X X' X'' Z : C} {a : X ⟶ X'} {b : X' ⟶ X''} {c : X ⟶ Z} {d : Z ⟶ X''}
    (h : a ≫ b = c ≫ d) (x : F.obj X) : F.map b (F.map a x) = F.map d (F.map c x) := by
  rw [← Functor.map_comp_apply, h, Functor.map_comp_apply]

/-- A composite of two maps of a functor to types is the identity on an element when the
composite of the morphisms is the identity. -/
theorem _root_.CategoryTheory.FunctorToTypes.map_map_eq_self_of_comp_eq_id {C : Type*}
    [Category* C] (F : C ⥤ Type w) {X X' : C} {a : X ⟶ X'} {b : X' ⟶ X} (h : a ≫ b = 𝟙 X)
    (x : F.obj X) : F.map b (F.map a x) = x := by
  rw [← Functor.map_comp_apply, h, Functor.map_id_apply]

/-! ### The test scheme of a section -/

/-- The test scheme over `Y` that a section `y` of `Y` over a scheme `T` of the site is: `T`
with the morphism to `Y` that the Yoneda lemma attaches to `y`. -/
def pointTestScheme (T : BigFppfOver B S hS) (y : Y.1.obj (Opposite.op T)) : SchemesOver Y :=
  CostructuredArrow.mk (Y := T)
    (ObjectProperty.homMk (yonedaEquiv.symm y) : (schemeSpaceFunctor B S hS).obj T ⟶ Y)

/-- The section of `Y` that the test scheme of a section is, is that section. -/
@[simp]
theorem testPoint_pointTestScheme (T : BigFppfOver B S hS) (y : Y.1.obj (Opposite.op T)) :
    testPoint (pointTestScheme T y) = y :=
  yonedaEquiv.apply_symm_apply y

/-- A morphism `g : T' ⟶ T` of the site, from the test scheme of a section `y'` of `Y` over
`T'` to that of a section `y` over `T`, when `y'` is the restriction of `y` along `g`. -/
def pointTestHom {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {y : Y.1.obj (Opposite.op T)}
    {y' : Y.1.obj (Opposite.op T')} (h : Y.1.map g.op y = y') :
    pointTestScheme T' y' ⟶ pointTestScheme T y :=
  CostructuredArrow.homMk g (by
    subst h
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map g ≫ yonedaEquiv.symm y = yonedaEquiv.symm (Y.1.map g.op y)
    rw [yonedaEquiv_symm_map]
    rfl)

/-- The underlying morphism of `AlgebraicGeometry.Space.pointTestHom`. -/
@[simp]
theorem pointTestHom_left {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {y : Y.1.obj (Opposite.op T)}
    {y' : Y.1.obj (Opposite.op T')} (h : Y.1.map g.op y = y') :
    (pointTestHom g h).left = g :=
  rfl

/-- The identity of `T`, from the test scheme of a section `y` to that of an equal section. -/
def pointTestSchemeHomOfEq (T : BigFppfOver B S hS) {y y' : Y.1.obj (Opposite.op T)}
    (h : y = y') : pointTestScheme T y ⟶ pointTestScheme T y' :=
  pointTestHom (𝟙 T) (by rw [h, op_id, Functor.map_id_apply])

/-- The underlying morphism of `AlgebraicGeometry.Space.pointTestSchemeHomOfEq`. -/
@[simp]
theorem pointTestSchemeHomOfEq_left (T : BigFppfOver B S hS) {y y' : Y.1.obj (Opposite.op T)}
    (h : y = y') : (pointTestSchemeHomOfEq T h).left = 𝟙 T :=
  rfl

/-- A test scheme over `Y` is the test scheme of its own section of `Y`. -/
def pointTestSchemeIso (T : SchemesOver Y) : pointTestScheme T.left (testPoint T) ≅ T :=
  CostructuredArrow.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom]
    exact ObjectProperty.hom_ext _ (yonedaEquiv_symm_testPoint T).symm)

/-- The underlying morphism of `AlgebraicGeometry.Space.pointTestSchemeIso`. -/
@[simp]
theorem pointTestSchemeIso_hom_left (T : SchemesOver Y) :
    (pointTestSchemeIso T).hom.left = 𝟙 _ :=
  rfl

/-- The underlying morphism of the inverse of `AlgebraicGeometry.Space.pointTestSchemeIso`. -/
@[simp]
theorem pointTestSchemeIso_inv_left (T : SchemesOver Y) :
    (pointTestSchemeIso T).inv.left = 𝟙 _ :=
  rfl

/-! ### The total presheaf -/

section Total

variable (R : (SchemesOver Y)ᵒᵖ ⥤ Type w)

/-- Two elements of the total presheaf built from the same restriction agree. -/
theorem totalPresheaf_mk_congr {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    {y : Y.1.obj (Opposite.op T)} {y₁ y₂ : Y.1.obj (Opposite.op T')} (h₁ : Y.1.map g.op y = y₁)
    (h₂ : Y.1.map g.op y = y₂) (r : R.obj (Opposite.op (pointTestScheme T y))) :
    (⟨y₁, R.map (pointTestHom g h₁).op r⟩ :
        Σ y' : Y.1.obj (Opposite.op T'), R.obj (Opposite.op (pointTestScheme T' y'))) =
      ⟨y₂, R.map (pointTestHom g h₂).op r⟩ := by
  subst h₁
  subst h₂
  rfl

/-- **A functor on the test schemes over `Y`, read as a presheaf on the big fppf site**: its
value at a scheme `T` of the site is the set of pairs of a section `y` of `Y` over `T` and an
element of the value of the functor at the test scheme `(T, y)`. -/
def totalPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max u w) where
  obj T := Σ y : Y.1.obj T, R.obj (Opposite.op (pointTestScheme T.unop y))
  map {T T'} g := ↾fun x => ⟨Y.1.map g x.1, R.map (pointTestHom g.unop rfl).op x.2⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    obtain ⟨y, r⟩ := x
    refine (totalPresheaf_mk_congr R (𝟙 T.unop) (y := y) (y₂ := y) rfl (by simp) r).trans ?_
    have : pointTestHom (Y := Y) (𝟙 T.unop) (y := y) (by simp) = 𝟙 _ :=
      CostructuredArrow.hom_ext _ _ rfl
    rw [this]
    simp
  map_comp {T T' T''} g g' := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    obtain ⟨y, r⟩ := x
    refine (totalPresheaf_mk_congr R (g ≫ g').unop (y := y) (y₂ := Y.1.map g' (Y.1.map g y)) rfl
      (by simp) r).trans ?_
    refine Sigma.ext rfl (heq_of_eq ?_)
    have hc : pointTestHom g'.unop rfl ≫ pointTestHom g.unop rfl =
        pointTestHom (Y := Y) (g ≫ g').unop (y := y) (by simp) :=
      CostructuredArrow.hom_ext _ _ rfl
    exact (congrArg (fun k => R.map k.op r) hc.symm).trans
      (Functor.map_comp_apply R (pointTestHom g.unop rfl).op (pointTestHom g'.unop rfl).op r)

/-- Two elements of the total presheaf restricted from the same element agree when their
sections of `Y` agree and the two restriction morphisms have the same underlying morphism. -/
theorem totalPresheaf_ext {T : BigFppfOver B S hS} {X : SchemesOver Y} (r : R.obj (Opposite.op X))
    {y₁ y₂ : Y.1.obj (Opposite.op T)} (h : y₁ = y₂) (f₁ : pointTestScheme T y₁ ⟶ X)
    (f₂ : pointTestScheme T y₂ ⟶ X) (hf : f₁.left = f₂.left) :
    (⟨y₁, R.map f₁.op r⟩ :
        Σ y' : Y.1.obj (Opposite.op T), R.obj (Opposite.op (pointTestScheme T y'))) =
      ⟨y₂, R.map f₂.op r⟩ := by
  subst h
  rw [CostructuredArrow.hom_ext f₁ f₂ hf]

/-- Two elements of the total presheaf restricted twice from the same element agree when their
sections of `Y` agree and the two composite restriction morphisms have the same underlying
morphism. -/
theorem totalPresheaf_ext₂ {T : BigFppfOver B S hS} {X X₁ X₂ : SchemesOver Y}
    (r : R.obj (Opposite.op X)) {y₁ y₂ : Y.1.obj (Opposite.op T)} (h : y₁ = y₂)
    (f₁ : pointTestScheme T y₁ ⟶ X₁) (f₂ : X₁ ⟶ X) (f₃ : pointTestScheme T y₂ ⟶ X₂)
    (f₄ : X₂ ⟶ X) (hf : f₁.left ≫ f₂.left = f₃.left ≫ f₄.left) :
    (⟨y₁, R.map f₁.op (R.map f₂.op r)⟩ :
        Σ y' : Y.1.obj (Opposite.op T), R.obj (Opposite.op (pointTestScheme T y'))) =
      ⟨y₂, R.map f₃.op (R.map f₄.op r)⟩ := by
  subst h
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    CostructuredArrow.hom_ext (f₁ ≫ f₂) (f₃ ≫ f₄) hf]

/-- The action of the total presheaf on a morphism of the site. -/
theorem totalPresheaf_map_apply {T T' : (BigFppfOver B S hS)ᵒᵖ} (g : T ⟶ T')
    (x : (totalPresheaf R).obj T) :
    (totalPresheaf R).map g x = ⟨Y.1.map g x.1, R.map (pointTestHom g.unop rfl).op x.2⟩ :=
  rfl

/-- **A functor on the test schemes over `Y` is an fppf sheaf over `Y`**: the presheaf
`AlgebraicGeometry.Space.totalPresheaf` it determines on the big fppf site is a sheaf. -/
def IsFppfSheafOver : Prop :=
  Presheaf.IsSheaf (BigFppfOver.topology B S hS) (totalPresheaf R)

variable {R} in
/-- The total presheaf is functorial in the functor on the test schemes. -/
def totalPresheafMap {R' : (SchemesOver Y)ᵒᵖ ⥤ Type w} (α : R ⟶ R') :
    totalPresheaf R ⟶ totalPresheaf R' where
  app T := ↾fun x => ⟨x.1, α.app _ x.2⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    obtain ⟨y, r⟩ := x
    refine Sigma.ext rfl (heq_of_eq ?_)
    change α.app _ (R.map _ r) = R'.map _ (α.app _ r)
    exact NatTrans.naturality_apply α _ r

variable {R} in
/-- An isomorphism of functors on the test schemes induces one of their total presheaves. -/
def totalPresheafIso {R' : (SchemesOver Y)ᵒᵖ ⥤ Type w} (e : R ≅ R') :
    totalPresheaf R ≅ totalPresheaf R' where
  hom := totalPresheafMap e.hom
  inv := totalPresheafMap e.inv
  hom_inv_id := by
    ext T x
    refine Sigma.ext rfl (heq_of_eq ?_)
    change e.inv.app _ (e.hom.app _ x.2) = x.2
    simp
  inv_hom_id := by
    ext T x
    refine Sigma.ext rfl (heq_of_eq ?_)
    change e.hom.app _ (e.inv.app _ x.2) = x.2
    simp

end Total

/-- The total presheaf of the universe lift of a functor is the universe lift of its total
presheaf. -/
def totalPresheafULiftIso (R : (SchemesOver Y)ᵒᵖ ⥤ Type u) :
    totalPresheaf (R ⋙ uliftFunctor.{w, u}) ≅ totalPresheaf R ⋙ uliftFunctor.{w, u} :=
  NatIso.ofComponents (fun _T => Equiv.toIso
    { toFun := fun x => ⟨⟨x.1, x.2.down⟩⟩
      invFun := fun x => ⟨x.down.1, ⟨x.down.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- A functor on the test schemes with values in `Type u` is an fppf sheaf over `Y` as soon as
its universe lift is. -/
theorem IsFppfSheafOver.of_uliftFunctor {R : (SchemesOver Y)ᵒᵖ ⥤ Type u}
    (h : IsFppfSheafOver (R ⋙ uliftFunctor.{u + 1, u})) : IsFppfSheafOver R := by
  have h' : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (totalPresheaf R ⋙ uliftFunctor.{u + 1, u}) :=
    (Presheaf.isSheaf_of_iso_iff (totalPresheafULiftIso R)).1 h
  exact Presheaf.isSheaf_of_isSheaf_comp _ _ uliftFunctor.{u + 1, u} h'

/-! ### The projection to `Y` -/

section Projection

variable (R : (SchemesOver Y)ᵒᵖ ⥤ Type u)

/-- The projection of the total presheaf of a functor with values in `Type u` to `Y`. -/
def totalProj : totalPresheaf R ⟶ Y.1 where
  app _T := ↾fun x => x.1
  naturality _ _ _ := rfl

/-- The projection to `Y` is compatible with the functoriality of the total presheaf. -/
@[reassoc (attr := simp)]
theorem totalPresheafMap_totalProj {R' : (SchemesOver Y)ᵒᵖ ⥤ Type u} (α : R ⟶ R') :
    totalPresheafMap α ≫ totalProj R' = totalProj R :=
  rfl

/-- **The points over `Y` of the total presheaf are the functor itself**, when the total
presheaf is an algebraic space: at a test scheme `T` over `Y`, an element of the total presheaf
over the section of `Y` that `T` is, is an element of the functor at `T`. -/
def spacePointsOverTotalProjIso (hR : IsAlgebraicSpace B S hS (totalPresheaf R)) :
    spacePointsOver (H := ⟨totalPresheaf R, hR⟩) (ObjectProperty.homMk (totalProj R)) ≅ R :=
  NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun x => R.map ((pointTestSchemeIso T.unop).inv ≫
        pointTestSchemeHomOfEq T.unop.left x.2.symm).op x.1.2
      invFun := fun r => ⟨⟨testPoint T.unop, R.map (pointTestSchemeIso T.unop).hom.op r⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨y, r⟩, hy⟩
        change y = testPoint T.unop at hy
        subst hy
        refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
        exact FunctorToTypes.map_map_eq_self_of_comp_eq_id R
          (by
            apply Quiver.Hom.unop_inj
            exact CostructuredArrow.hom_ext _ _ (by
              change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
              simp)) r
      right_inv := by
        intro r
        exact FunctorToTypes.map_map_eq_self_of_comp_eq_id R
          (by
            apply Quiver.Hom.unop_inj
            exact CostructuredArrow.hom_ext _ _ (by
              change ((𝟙 _ : _ ⟶ _) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
              simp)) r })
    (by
      rintro T T' g
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      obtain ⟨⟨y, r⟩, hy⟩ := x
      change y = testPoint T.unop at hy
      subst hy
      exact FunctorToTypes.map_map_eq_of_comp_eq R (by
        apply Quiver.Hom.unop_inj
        exact CostructuredArrow.hom_ext _ _ (by
              change ((𝟙 _ : _ ⟶ _) ≫ 𝟙 _) ≫ g.unop.left = g.unop.left ≫ 𝟙 _ ≫ 𝟙 _
              simp)) r)

end Projection

/-- An element of the total presheaf of the points of `H` over `Z` is determined by its section
of `H`. -/
theorem totalPresheafSpacePointsOver_ext {Z H : AlgebraicSpaces B S hS} (p : H ⟶ Z)
    {T : (BigFppfOver B S hS)ᵒᵖ} (z : Z.1.obj T)
    (h : H.1.obj (Opposite.op (pointTestScheme T.unop z).left))
    (hh : p.hom.app _ h = testPoint (pointTestScheme T.unop z)) :
    ∀ (z' : Z.1.obj T) (_ : p.hom.app T h = z')
      (hh' : p.hom.app _ h = testPoint (pointTestScheme T.unop z')),
      (⟨z', ⟨h, hh'⟩⟩ : (totalPresheaf (spacePointsOver p)).obj T) = ⟨z, ⟨h, hh⟩⟩ := by
  rintro z' rfl hh'
  have hz : p.hom.app T h = z := hh.trans (testPoint_pointTestScheme _ _)
  revert hh
  rw [← hz]
  intro hh
  rfl

/-- **The total presheaf of the points of an algebraic space over `Z` is that space**: an
element of it is a section `z` of `Z` together with a section of `H` over `z`. -/
def totalPresheafSpacePointsOverIso {Z H : AlgebraicSpaces B S hS} (p : H ⟶ Z) :
    totalPresheaf (spacePointsOver p) ≅ H.1 where
  hom := { app := fun T => ↾fun x => x.2.1, naturality := fun _ _ _ => rfl }
  inv := { app := fun T => ↾fun h => ⟨p.hom.app T h, ⟨h, (testPoint_pointTestScheme _ _).symm⟩⟩
           naturality := fun T T' g => by
             refine ConcreteCategory.hom_ext _ _ fun h => ?_
             exact totalPresheafSpacePointsOver_ext p (Z.1.map g (p.hom.app T h)) (H.1.map g h)
               ((NatTrans.naturality_apply p.hom g h).trans (testPoint_pointTestScheme _ _).symm)
               _ rfl _ }
  hom_inv_id := by
    refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => ?_)
    obtain ⟨z, ⟨h, hh⟩⟩ := x
    exact totalPresheafSpacePointsOver_ext p z h hh _ rfl _
  inv_hom_id := rfl

/-- The identification `AlgebraicGeometry.Space.totalPresheafSpacePointsOverIso` lies over
`Z`. -/
@[reassoc (attr := simp)]
theorem totalPresheafSpacePointsOverIso_hom_comp {Z H : AlgebraicSpaces B S hS} (p : H ⟶ Z) :
    (totalPresheafSpacePointsOverIso p).hom ≫ p.hom = totalProj (spacePointsOver p) := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => ?_)
  obtain ⟨z, ⟨h, hh⟩⟩ := x
  have e : p.hom.app T h = z := hh.trans (testPoint_pointTestScheme T.unop z)
  exact e

/-! ### Restriction to the test schemes over a test scheme -/

section Restrict

variable (R : (SchemesOver Y)ᵒᵖ ⥤ Type u) (V : SchemesOver Y)

/-- The restriction of a functor on the test schemes over `Y` to the test schemes over a test
scheme `V` over `Y`. -/
abbrev restrictTestScheme : (SchemesOver ((schemeSpaceFunctor B S hS).obj V.left))ᵒᵖ ⥤ Type u :=
  (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙ R

/-- The test scheme over `Y` of the image in `Y` of a section of `V` is the test scheme of the
section, regarded as a test scheme over `Y`. -/
def pointTestSchemeMapIso (T : BigFppfOver B S hS)
    (v : ((schemeSpaceFunctor B S hS).obj V.left).1.obj (Opposite.op T)) :
    pointTestScheme T (V.hom.hom.app _ v) ≅
      (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).obj (pointTestScheme T v) :=
  CostructuredArrow.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom]
    refine ObjectProperty.hom_ext _ ?_
    change yonedaEquiv.symm v ≫ V.hom.hom = yonedaEquiv.symm (V.hom.hom.app _ v)
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- The underlying morphism of `AlgebraicGeometry.Space.pointTestSchemeMapIso`. -/
@[simp]
theorem pointTestSchemeMapIso_hom_left (T : BigFppfOver B S hS)
    (v : ((schemeSpaceFunctor B S hS).obj V.left).1.obj (Opposite.op T)) :
    (pointTestSchemeMapIso V T v).hom.left = 𝟙 T :=
  rfl

/-- The comparison of the total presheaf of the restriction of `R` to `V` with the total
presheaf of `R`: a section `v` of `V` goes to its image in `Y`. -/
def totalPresheafRestrict : totalPresheaf (restrictTestScheme R V) ⟶ totalPresheaf R where
  app T := ↾fun x => ⟨V.hom.hom.app _ x.1, R.map (pointTestSchemeMapIso V T.unop x.1).hom.op x.2⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    obtain ⟨v, r⟩ := x
    refine totalPresheaf_ext₂ R r (NatTrans.naturality_apply V.hom.hom g v) _ _ _ _ ?_
    change 𝟙 _ ≫ g.unop = g.unop ≫ 𝟙 _
    simp

/-- The comparison of total presheaves lies over the structure morphism of `V`. -/
@[reassoc]
theorem totalPresheafRestrict_totalProj :
    totalPresheafRestrict R V ≫ totalProj R = totalProj (restrictTestScheme R V) ≫ V.hom.hom :=
  rfl

/-- **The total presheaf of the restriction to a test scheme `V` is the base change of the total
presheaf along `V ⟶ Y`.** -/
theorem isPullback_totalPresheafRestrict :
    IsPullback (totalPresheafRestrict R V) (totalProj (restrictTestScheme R V)) (totalProj R)
      V.hom.hom := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨v₁, r₁⟩ ⟨v₂, r₂⟩ ⟨h₁, h₂⟩
    change v₁ = v₂ at h₂
    subst h₂
    have h₃ := eq_of_heq (Sigma.mk.inj_iff.1 h₁).2
    refine Sigma.ext rfl (heq_of_eq ?_)
    have h₄ := congrArg (R.map (pointTestSchemeMapIso V T.unop v₁).inv.op) h₃
    exact (FunctorToTypes.map_map_eq_self_of_comp_eq_id R
        (pointTestSchemeMapIso V T.unop v₁).op.hom_inv_id r₁).symm.trans
      (h₄.trans (FunctorToTypes.map_map_eq_self_of_comp_eq_id R
        (pointTestSchemeMapIso V T.unop v₁).op.hom_inv_id r₂))
  · rintro ⟨y, r⟩ v h
    change y = V.hom.hom.app T v at h
    subst h
    refine ⟨⟨v, R.map (pointTestSchemeMapIso V T.unop v).inv.op r⟩, ?_, rfl⟩
    exact Sigma.ext rfl (heq_of_eq (FunctorToTypes.map_map_eq_self_of_comp_eq_id R
      (pointTestSchemeMapIso V T.unop v).op.inv_hom_id r))

end Restrict

end AlgebraicGeometry.Space

end
