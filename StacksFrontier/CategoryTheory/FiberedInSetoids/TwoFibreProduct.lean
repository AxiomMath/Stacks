module

public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs

/-!
# The 2-fibre product of categories fibred in setoids (Stacks 04SB)

Stacks Tag `04SB` (Lemma 4.39.4): the 2-fibre product over a base category `𝒞` of three
categories fibred in setoids is again fibred in setoids.

`TwoFibreProd pX pY pS F G` is the explicit 2-fibre product `𝒳 ×_𝒮 𝒴` of Stacks `0040`:
an object is a quadruple `(U, x, y, f)` with `x` over `U` in `𝒳`, `y` over `U` in `𝒴` and
`f : F x ⟶ G y` an isomorphism of `𝒮` lying over `𝟙 U`; a morphism is a pair `(a, b)` of
morphisms of `𝒳` and `𝒴` inducing the same morphism of `𝒞` and commuting with the
comparison isomorphisms. Its structure functor `TwoFibreProd.proj` sends `(U, x, y, f)` to
`U`. This is the 2-fibre product over a base, not Mathlib's
`CategoryTheory.Limits.CategoricalPullback`, which has no structure functor to `𝒞`.

## Main definitions

* `CategoryTheory.TwoFibreProd`: the 2-fibre product `𝒳 ×_𝒮 𝒴` over `𝒞`.
* `CategoryTheory.TwoFibreProd.proj`: its structure functor to `𝒞`.

## Main results

* `CategoryTheory.TwoFibreProd.proj_isFiberedInGroupoids`: the 2-fibre product of categories
  fibred in groupoids is fibred in groupoids.
* `CategoryTheory.TwoFibreProd.proj_fiber_isThin`: its fibres are thin when those of `pX` and
  `pY` are.
* `CategoryTheory.TwoFibreProd.proj_isFiberedInSetoids`: the 2-fibre product of categories
  fibred in setoids is fibred in setoids.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ u₁ v u w t s

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u} [Category.{v} 𝒳] {𝒴 : Type w} [Category.{t} 𝒴]
variable {𝒮 : Type s} [Category.{v₁} 𝒮]
variable (pX : 𝒳 ⥤ 𝒞) (pY : 𝒴 ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞)
variable (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

/-- **The 2-fibre product over `𝒞`** (Stacks `0040`). An object of `𝒳 ×_𝒮 𝒴` is a
quadruple `(U, x, y, f)` where `U` is an object of `𝒞`, `x` lies over `U` in `𝒳`, `y` lies
over `U` in `𝒴`, and `f : F(x) ⟶ G(y)` is an isomorphism of `𝒮` lying over `𝟙 U`. -/
structure TwoFibreProd where
  /-- The base object `U` of `𝒞`. -/
  base : 𝒞
  /-- The object `x` of `𝒳`. -/
  x : 𝒳
  /-- The object `y` of `𝒴`. -/
  y : 𝒴
  /-- `x` lies over `U`. -/
  hx : pX.obj x = base
  /-- `y` lies over `U`. -/
  hy : pY.obj y = base
  /-- `F(x)` lies over `U`. -/
  hFx : pS.obj (F.obj x) = base
  /-- `G(y)` lies over `U`. -/
  hGy : pS.obj (G.obj y) = base
  /-- The comparison morphism `f : F(x) ⟶ G(y)`. -/
  f : F.obj x ⟶ G.obj y
  /-- `f` is an isomorphism. -/
  isIso_f : IsIso f
  /-- `f` lies over `𝟙 U`. -/
  f_over : pS.map f = eqToHom hFx ≫ eqToHom hGy.symm

attribute [instance] TwoFibreProd.isIso_f

/-- A morphism `(U, x, y, f) ⟶ (U', x', y', f')` of the 2-fibre product is a pair `(a, b)`
of morphisms `a : x ⟶ x'` in `𝒳` and `b : y ⟶ y'` in `𝒴` inducing the same morphism
`U ⟶ U'` of `𝒞` and making the comparison square `f' ∘ F(a) = G(b) ∘ f` commute. -/
structure TwoFibreProd.Hom (P Q : TwoFibreProd pX pY pS F G) where
  /-- The `𝒳`-component. -/
  a : P.x ⟶ Q.x
  /-- The `𝒴`-component. -/
  b : P.y ⟶ Q.y
  /-- `a` and `b` induce the same morphism on bases. -/
  base_compat : eqToHom P.hx.symm ≫ pX.map a ≫ eqToHom Q.hx
      = eqToHom P.hy.symm ≫ pY.map b ≫ eqToHom Q.hy
  /-- The comparison square commutes. -/
  square : F.map a ≫ Q.f = P.f ≫ G.map b

namespace TwoFibreProd
variable {pX pY pS F G}

/-- A morphism of the 2-fibre product is determined by its two components. -/
@[ext] lemma Hom.ext' {P Q : TwoFibreProd pX pY pS F G} {φ ψ : Hom pX pY pS F G P Q}
    (ha : φ.a = ψ.a) (hb : φ.b = ψ.b) : φ = ψ := by
  cases φ; cases ψ; simp_all

/-- The category structure on `TwoFibreProd pX pY pS F G`, with `TwoFibreProd.Hom` as hom-type
and identities and composition taken componentwise in `𝒳` and `𝒴`. -/
instance : Category (TwoFibreProd pX pY pS F G) where
  Hom P Q := Hom pX pY pS F G P Q
  id P := ⟨𝟙 P.x, 𝟙 P.y, by simp, by simp⟩
  comp {P Q R} φ ψ := ⟨φ.a ≫ ψ.a, φ.b ≫ ψ.b, by
      rw [pX.map_comp, pY.map_comp]
      calc eqToHom P.hx.symm ≫ (pX.map φ.a ≫ pX.map ψ.a) ≫ eqToHom R.hx
          = (eqToHom P.hx.symm ≫ pX.map φ.a ≫ eqToHom Q.hx) ≫
              (eqToHom Q.hx.symm ≫ pX.map ψ.a ≫ eqToHom R.hx) := by
                simp
        _ = (eqToHom P.hy.symm ≫ pY.map φ.b ≫ eqToHom Q.hy) ≫
              (eqToHom Q.hy.symm ≫ pY.map ψ.b ≫ eqToHom R.hy) := by
                rw [φ.base_compat, ψ.base_compat]
        _ = eqToHom P.hy.symm ≫ (pY.map φ.b ≫ pY.map ψ.b) ≫ eqToHom R.hy := by
                simp, by
      rw [F.map_comp, G.map_comp, Category.assoc, ψ.square, ← Category.assoc, φ.square,
        Category.assoc]⟩
  id_comp := by intros; apply Hom.ext' <;> simp
  comp_id := by intros; apply Hom.ext' <;> simp
  assoc := by intros; apply Hom.ext' <;> simp

/-- The `𝒳`-component of the identity is the identity. -/
@[simp] lemma id_a (P : TwoFibreProd pX pY pS F G) : (𝟙 P : P ⟶ P).a = 𝟙 P.x := rfl
/-- The `𝒴`-component of the identity is the identity. -/
@[simp] lemma id_b (P : TwoFibreProd pX pY pS F G) : (𝟙 P : P ⟶ P).b = 𝟙 P.y := rfl
/-- The `𝒳`-component of a composite is the composite of the `𝒳`-components. -/
@[simp] lemma comp_a {P Q R : TwoFibreProd pX pY pS F G} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).a = φ.a ≫ ψ.a := rfl
/-- The `𝒴`-component of a composite is the composite of the `𝒴`-components. -/
@[simp] lemma comp_b {P Q R : TwoFibreProd pX pY pS F G} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).b = φ.b ≫ ψ.b := rfl

/-- The structure functor `𝒳 ×_𝒮 𝒴 ⥤ 𝒞` of the 2-fibre product, sending `(U, x, y, f)`
to `U`. -/
@[implicit_reducible]
def proj (pX : 𝒳 ⥤ 𝒞) (pY : 𝒴 ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    TwoFibreProd pX pY pS F G ⥤ 𝒞 where
  obj P := P.base
  map {P Q} φ := eqToHom P.hx.symm ≫ pX.map φ.a ≫ eqToHom Q.hx
  map_id P := by simp
  map_comp φ ψ := by simp

/-- The structure functor sends `(U, x, y, f)` to `U`. -/
@[simp] lemma proj_obj (P : TwoFibreProd pX pY pS F G) : (proj pX pY pS F G).obj P = P.base := rfl

/-- The structure functor sends a morphism to the morphism of bases its `𝒳`-component lies
over. -/
@[simp] lemma proj_map {P Q : TwoFibreProd pX pY pS F G} (φ : P ⟶ Q) :
    (proj pX pY pS F G).map φ = eqToHom P.hx.symm ≫ pX.map φ.a ≫ eqToHom Q.hx := rfl

/-- A morphism of the 2-fibre product induces the morphism `w` of `𝒞` exactly when its
`𝒳`-component lies over `w`. -/
lemma proj_map_eq_iff_a {P Q : TwoFibreProd pX pY pS F G} (φ : P ⟶ Q) (w : P.base ⟶ Q.base) :
    (proj pX pY pS F G).map φ = w ↔ pX.map φ.a = eqToHom P.hx ≫ w ≫ eqToHom Q.hx.symm := by
  rw [proj_map]
  exact ⟨by rintro rfl; simp, fun h ↦ by simp [h]⟩

/-- A morphism of the 2-fibre product induces the morphism `w` of `𝒞` exactly when its
`𝒴`-component lies over `w`. -/
lemma proj_map_eq_iff_b {P Q : TwoFibreProd pX pY pS F G} (φ : P ⟶ Q) (w : P.base ⟶ Q.base) :
    (proj pX pY pS F G).map φ = w ↔ pY.map φ.b = eqToHom P.hy ≫ w ≫ eqToHom Q.hy.symm := by
  rw [proj_map, φ.base_compat]
  exact ⟨by rintro rfl; simp, fun h ↦ by simp [h]⟩

/-- The `𝒳`-component of a morphism of the 2-fibre product lies over the morphism of `𝒞` that
the morphism induces. -/
lemma map_a_eq {P Q : TwoFibreProd pX pY pS F G} (φ : P ⟶ Q) :
    pX.map φ.a = eqToHom P.hx ≫ (proj pX pY pS F G).map φ ≫ eqToHom Q.hx.symm :=
  (proj_map_eq_iff_a φ _).mp rfl

/-- The `𝒴`-component of a morphism of the 2-fibre product lies over the morphism of `𝒞` that
the morphism induces. -/
lemma map_b_eq {P Q : TwoFibreProd pX pY pS F G} (φ : P ⟶ Q) :
    pY.map φ.b = eqToHom P.hy ≫ (proj pX pY pS F G).map φ ≫ eqToHom Q.hy.symm :=
  (proj_map_eq_iff_b φ _).mp rfl

/-- A pair of components both lying over one morphism `w : P.base ⟶ Q.base` of `𝒞` satisfies
the base-compatibility condition of `TwoFibreProd.Hom`. -/
lemma base_compat_of_map_eq {P Q : TwoFibreProd pX pY pS F G} {a : P.x ⟶ Q.x} {b : P.y ⟶ Q.y}
    {w : P.base ⟶ Q.base} (ha : pX.map a = eqToHom P.hx ≫ w ≫ eqToHom Q.hx.symm)
    (hb : pY.map b = eqToHom P.hy ≫ w ≫ eqToHom Q.hy.symm) :
    eqToHom P.hx.symm ≫ pX.map a ≫ eqToHom Q.hx
      = eqToHom P.hy.symm ≫ pY.map b ≫ eqToHom Q.hy := by
  simp [ha, hb]

/-- If `φ` lies over `g` and `p.map a` is `q.map φ` up to `eqToHom`s, then `a` lies over `g`. -/
private theorem isHomLift_of_map_eq {𝒵 : Type*} [Category 𝒵] {q : 𝒵 ⥤ 𝒞} {p : 𝒳 ⥤ 𝒞}
    {z z' : 𝒵} {x y : 𝒳} {φ : z ⟶ z'} {a : x ⟶ y} {R S : 𝒞} {g : R ⟶ S}
    (hφ : q.IsHomLift g φ) (hx : p.obj x = q.obj z) (hy : p.obj y = q.obj z')
    (ha : p.map a = eqToHom hx ≫ q.map φ ≫ eqToHom hy.symm) : p.IsHomLift g a :=
  IsHomLift.of_fac' p g a (hx.trans (IsHomLift.domain_eq q g φ))
    (hy.trans (IsHomLift.codomain_eq q g φ)) (by rw [ha, IsHomLift.fac' q g φ]; simp)

/-- A morphism of the 2-fibre product lying over `g : R ⟶ S` in `𝒞` has `𝒳`-component lying
over `g`. -/
lemma isHomLift_a {P Q : TwoFibreProd pX pY pS F G} {R S : 𝒞} {g : R ⟶ S} {φ : P ⟶ Q}
    (hφ : (proj pX pY pS F G).IsHomLift g φ) : pX.IsHomLift g φ.a :=
  isHomLift_of_map_eq hφ P.hx Q.hx (map_a_eq φ)

/-- A morphism of the 2-fibre product lying over `g : R ⟶ S` in `𝒞` has `𝒴`-component lying
over `g`. -/
lemma isHomLift_b {P Q : TwoFibreProd pX pY pS F G} {R S : 𝒞} {g : R ⟶ S} {φ : P ⟶ Q}
    (hφ : (proj pX pY pS F G).IsHomLift g φ) : pY.IsHomLift g φ.b :=
  isHomLift_of_map_eq hφ P.hy Q.hy (map_b_eq φ)

end TwoFibreProd

/-- Lifting `g : V ⟶ U` along a functor fibred in groupoids to an object over `x`, with the
lifted morphism lying over `g` up to `eqToHom`s. -/
private theorem exists_lift_eq {p : 𝒳 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids) {x : 𝒳} {U V : 𝒞}
    (hx : p.obj x = U) (g : V ⟶ U) :
    ∃ (x' : 𝒳) (a : x' ⟶ x) (h : p.obj x' = V), p.map a = eqToHom h ≫ g ≫ eqToHom hx.symm := by
  obtain ⟨x', a, hlift⟩ := hp.exists_lift (g ≫ eqToHom hx.symm) x rfl
  exact ⟨x', a, IsHomLift.domain_eq p (g ≫ eqToHom hx.symm) a,
    by simpa using IsHomLift.fac' p (g ≫ eqToHom hx.symm) a⟩

/-- Existence of lifts for the structure functor of the 2-fibre product (the first axiom of
`Functor.IsFiberedInGroupoids`): every morphism `g : V ⟶ P.base` of `𝒞` lifts to a morphism with
target `P`. -/
theorem TwoFibreProd.proj_exists_lift
    (hX : pX.IsFiberedInGroupoids) (hY : pY.IsFiberedInGroupoids) (hS : pS.IsFiberedInGroupoids)
    (hF : F ⋙ pS = pX) (hG : G ⋙ pS = pY)
    (P : TwoFibreProd pX pY pS F G) {V : 𝒞} (g : V ⟶ P.base) :
    ∃ (Q : TwoFibreProd pX pY pS F G) (χ : Q ⟶ P),
      (TwoFibreProd.proj pX pY pS F G).IsHomLift g χ := by
  obtain ⟨x', a, hx', ha⟩ := exists_lift_eq hX P.hx g
  obtain ⟨y', b, hy', hb⟩ := exists_lift_eq hY P.hy g
  have eFx' : pS.obj (F.obj x') = V := (Functor.congr_obj hF x').trans hx'
  have eGy' : pS.obj (G.obj y') = V := (Functor.congr_obj hG y').trans hy'
  have hFmap : pS.map (F.map a) = _ := Functor.congr_hom hF a
  have hGmap : pS.map (G.map b) = _ := Functor.congr_hom hG b
  have hcompat : (eqToHom eFx' ≫ eqToHom eGy'.symm) ≫ pS.map (G.map b)
      = pS.map (F.map a ≫ P.f) := by
    rw [pS.map_comp, hGmap, hFmap, P.f_over, ha, hb]
    simp
  obtain ⟨f', ⟨hf'base, hf'eq⟩, -⟩ := hS.unique_lift (G.map b) (F.map a ≫ P.f) _ hcompat
  have hf'lift : pS.IsHomLift (𝟙 V) f' :=
    IsHomLift.of_fac' pS (𝟙 V) f' eFx' eGy' (by rw [hf'base]; simp)
  have := hS.isStronglyCartesian_homLift (𝟙 V) f'
  have hf'iso : IsIso f' :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := pS) (f := 𝟙 V) f'
  refine ⟨⟨V, x', y', hx', hy', eFx', eGy', f', hf'iso, hf'base⟩,
    ⟨a, b, TwoFibreProd.base_compat_of_map_eq ha hb, hf'eq.symm⟩, ?_⟩
  refine IsHomLift.of_fac' (TwoFibreProd.proj pX pY pS F G) g _ rfl rfl ?_
  simp [ha]

/-- The comparison square of a componentwise fill-in commutes: if `a : R.x ⟶ Q.x` and
`b : R.y ⟶ Q.y` both lie over one morphism `g` of `𝒞` and factor the components of `ψ : R ⟶ P`
through those of `φ : Q ⟶ P`, then `F a ≫ Q.f = R.f ≫ G b`. -/
theorem TwoFibreProd.square_of_fill_in (hS : pS.IsFiberedInGroupoids)
    (hF : F ⋙ pS = pX) (hG : G ⋙ pS = pY) {P Q R : TwoFibreProd pX pY pS F G}
    (φ : Q ⟶ P) (ψ : R ⟶ P) {g : R.base ⟶ Q.base} {a : R.x ⟶ Q.x} {b : R.y ⟶ Q.y}
    (ha : pX.map a = eqToHom R.hx ≫ g ≫ eqToHom Q.hx.symm)
    (hb : pY.map b = eqToHom R.hy ≫ g ≫ eqToHom Q.hy.symm)
    (haComp : a ≫ φ.a = ψ.a) (hbComp : b ≫ φ.b = ψ.b) :
    F.map a ≫ Q.f = R.f ≫ G.map b := by
  have hFmap : pS.map (F.map a) = _ := Functor.congr_hom hF a
  have hGmap : pS.map (G.map b) = _ := Functor.congr_hom hG b
  have hu₁ : (F.map a ≫ Q.f) ≫ G.map φ.b = F.map ψ.a ≫ P.f := by
    rw [Category.assoc, ← φ.square, ← Category.assoc, ← F.map_comp, haComp]
  have hu₂ : (R.f ≫ G.map b) ≫ G.map φ.b = F.map ψ.a ≫ P.f := by
    rw [Category.assoc, ← G.map_comp, hbComp, ψ.square]
  have hbase : pS.map (F.map a ≫ Q.f) = pS.map (R.f ≫ G.map b) := by
    rw [pS.map_comp, pS.map_comp, hFmap, Q.f_over, hGmap, R.f_over, ha, hb]
    simp
  obtain ⟨w, -, hwUniq⟩ := hS.unique_lift (G.map φ.b) (F.map ψ.a ≫ P.f)
    (pS.map (F.map a ≫ Q.f)) (by rw [← pS.map_comp, hu₁])
  rw [hwUniq _ ⟨rfl, hu₁⟩, hwUniq _ ⟨hbase.symm, hu₂⟩]

/-- Existence and uniqueness of fill-ins for the structure functor of the 2-fibre product (the
second axiom of `Functor.IsFiberedInGroupoids`). -/
theorem TwoFibreProd.proj_unique_lift
    (hX : pX.IsFiberedInGroupoids) (hY : pY.IsFiberedInGroupoids) (hS : pS.IsFiberedInGroupoids)
    (hF : F ⋙ pS = pX) (hG : G ⋙ pS = pY) {P Q R : TwoFibreProd pX pY pS F G}
    (φ : Q ⟶ P) (ψ : R ⟶ P) (g : R.base ⟶ Q.base)
    (hg : g ≫ (TwoFibreProd.proj pX pY pS F G).map φ = (TwoFibreProd.proj pX pY pS F G).map ψ) :
    ∃! χ : R ⟶ Q, (TwoFibreProd.proj pX pY pS F G).map χ = g ∧ χ ≫ φ = ψ := by
  have hgX : (eqToHom R.hx ≫ g ≫ eqToHom Q.hx.symm) ≫ pX.map φ.a = pX.map ψ.a := by
    rw [TwoFibreProd.map_a_eq, TwoFibreProd.map_a_eq, ← hg]
    simp
  have hgY : (eqToHom R.hy ≫ g ≫ eqToHom Q.hy.symm) ≫ pY.map φ.b = pY.map ψ.b := by
    rw [TwoFibreProd.map_b_eq, TwoFibreProd.map_b_eq, ← hg]
    simp
  obtain ⟨a, ⟨haMap, haComp⟩, haUniq⟩ := hX.unique_lift φ.a ψ.a _ hgX
  obtain ⟨b, ⟨hbMap, hbComp⟩, hbUniq⟩ := hY.unique_lift φ.b ψ.b _ hgY
  refine ⟨⟨a, b, TwoFibreProd.base_compat_of_map_eq haMap hbMap,
      TwoFibreProd.square_of_fill_in pX pY pS F G hS hF hG φ ψ haMap hbMap haComp hbComp⟩,
    ⟨(TwoFibreProd.proj_map_eq_iff_a _ g).mpr haMap, TwoFibreProd.Hom.ext' haComp hbComp⟩, ?_⟩
  rintro χ ⟨hχmap, hχcomp⟩
  refine TwoFibreProd.Hom.ext' (haUniq _ ⟨?_, ?_⟩) (hbUniq _ ⟨?_, ?_⟩)
  · exact (TwoFibreProd.proj_map_eq_iff_a χ g).mp hχmap
  · simpa using congrArg TwoFibreProd.Hom.a hχcomp
  · exact (TwoFibreProd.proj_map_eq_iff_b χ g).mp hχmap
  · simpa using congrArg TwoFibreProd.Hom.b hχcomp

/-- The structure functor of the 2-fibre product over `𝒞` of categories fibred in groupoids is
fibred in groupoids. -/
theorem TwoFibreProd.proj_isFiberedInGroupoids
    (hX : pX.IsFiberedInGroupoids) (hY : pY.IsFiberedInGroupoids) (hS : pS.IsFiberedInGroupoids)
    (hF : F ⋙ pS = pX) (hG : G ⋙ pS = pY) :
    (TwoFibreProd.proj pX pY pS F G).IsFiberedInGroupoids where
  exists_lift g P hP := by
    subst hP
    exact TwoFibreProd.proj_exists_lift pX pY pS F G hX hY hS hF hG P g
  unique_lift φ ψ g hg := TwoFibreProd.proj_unique_lift pX pY pS F G hX hY hS hF hG φ ψ g hg

/-- Two morphisms of `𝒳` lying over `𝟙 U` between objects over `U` are equal if the fibre
over `U` is thin. -/
private theorem eq_of_isHomLift_of_isThin {p : 𝒳 ⥤ 𝒞} {U : 𝒞} (h : Quiver.IsThin (p.Fiber U))
    {x y : 𝒳} (hx : p.obj x = U) (hy : p.obj y = U) {a a' : x ⟶ y}
    (ha : p.IsHomLift (𝟙 U) a) (ha' : p.IsHomLift (𝟙 U) a') : a = a' :=
  congrArg Subtype.val ((h (Functor.Fiber.mk hx) (Functor.Fiber.mk hy)).elim
    (⟨a, ha⟩ : Functor.Fiber.mk hx ⟶ Functor.Fiber.mk hy) ⟨a', ha'⟩)

/-- If the fibres of `pX` and `pY` are thin, then every fibre of the structure functor of the
2-fibre product over `𝒞` is thin. -/
theorem TwoFibreProd.proj_fiber_isThin
    (hX : ∀ V : 𝒞, Quiver.IsThin (pX.Fiber V)) (hY : ∀ V : 𝒞, Quiver.IsThin (pY.Fiber V))
    (U : 𝒞) :
    Quiver.IsThin ((TwoFibreProd.proj pX pY pS F G).Fiber U) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩
  have hxP : pX.obj P.x = U := P.hx.trans hP
  have hxQ : pX.obj Q.x = U := Q.hx.trans hQ
  have hyP : pY.obj P.y = U := P.hy.trans hP
  have hyQ : pY.obj Q.y = U := Q.hy.trans hQ
  constructor
  rintro ⟨m, hm⟩ ⟨m', hm'⟩
  exact Functor.Fiber.hom_ext (TwoFibreProd.Hom.ext'
    (eq_of_isHomLift_of_isThin (hX U) hxP hxQ (TwoFibreProd.isHomLift_a hm)
      (TwoFibreProd.isHomLift_a hm'))
    (eq_of_isHomLift_of_isThin (hY U) hyP hyQ (TwoFibreProd.isHomLift_b hm)
      (TwoFibreProd.isHomLift_b hm')))

/-- **The 2-fibre product of categories fibred in setoids.** If `𝒳`, `𝒴`, `𝒮` are fibred in
setoids over `𝒞` and
`F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮` are 1-morphisms over `𝒞`, then the 2-fibre product `𝒳 ×_𝒮 𝒴`
over `𝒞`, with its structure functor, is again fibred in setoids over `𝒞`. -/
@[stacks 04SB]
theorem TwoFibreProd.proj_isFiberedInSetoids
    (hX : pX.IsFiberedInSetoids) (hY : pY.IsFiberedInSetoids) (hS : pS.IsFiberedInSetoids)
    (hF : F ⋙ pS = pX) (hG : G ⋙ pS = pY) :
    (TwoFibreProd.proj pX pY pS F G).IsFiberedInSetoids where
  isFiberedInGroupoids := TwoFibreProd.proj_isFiberedInGroupoids pX pY pS F G
    hX.isFiberedInGroupoids hY.isFiberedInGroupoids hS.isFiberedInGroupoids hF hG
  fiber_isThin := TwoFibreProd.proj_fiber_isThin pX pY pS F G hX.fiber_isThin hY.fiber_isThin

end CategoryTheory
