module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# Factoring a 1-morphism through a category fibred in groupoids over the target (Stacks 06N7)

Stacks Tag `06N7` (Lemma 4.35.16). Let `𝒞` be a category and let `𝒳`, `𝒴` be categories
fibred in groupoids over `𝒞` via `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞`. Let `F : 𝒳 ⥤ 𝒴` be a
1-morphism over `𝒞`, i.e. `F ⋙ q = p`. Then `F` factors, up to equivalence over `𝒞`,
through a category `𝒳'` such that

1. `𝒳'` is fibred in groupoids over `𝒞`, via a structure functor `r : 𝒳' ⥤ 𝒞`;
2. `a : 𝒳 ⥤ 𝒳'` is a 1-morphism over `𝒞` (`a ⋙ r = p`) and an equivalence over `𝒞`;
3. `t : 𝒳' ⥤ 𝒴` is a 1-morphism over `𝒞` (`t ⋙ q = r`) and is itself fibred in groupoids;
4. the factorization is exact: `a ⋙ t = F`.

The witness for `𝒳'` is the *vertical iso-comma* category `XPrime q F`: an object is a
triple `(x, y, φ)` with `φ : F x ≅ y` an isomorphism of `𝒴` lying over an identity of `𝒞`,
and a morphism is a compatible pair of morphisms of `𝒳` and `𝒴`. This is the `G = 𝟭 𝒴`
special case of the 2-fibre product of Stacks `0040` (the general construction over a base
is `CategoryTheory.TwoFibreProd` in Stacks `04SB`); it is kept separate here because its
object type must land in the universe demanded by the existential of the main theorem, which
the general construction — carrying the base object of `𝒞` as a field — does not.

"Lying over an identity" is Mathlib's `Functor.IsHomLift` at an identity morphism; the
characterization `IsHomLift.id_iff_exists_eqToHom` unpacks it into the `eqToHom` form the
`eqToHom` bookkeeping below works with. Conditions (2) and (3) are recorded strictly, with
`a ⋙ r = p`, `t ⋙ q = r` and `a ⋙ t = F` as equalities of functors rather than 2-isomorphisms,
which is stronger than the source demands; the notion of equivalence over `𝒞`
(`Functor.IsEquivalenceOver`) likewise asks for a strictly-over-`𝒞` quasi-inverse together
with unit and counit isomorphisms whose components are vertical.
-/

@[expose] public section

namespace CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃

/-- A morphism lies over an identity of `𝒞` exactly when its two endpoints lie over the same
object and its image is the corresponding `eqToHom`. This is the unpacked form of
`Functor.IsHomLift s (𝟙 (s.obj a)) ψ`, i.e. of "`ψ` is `s`-vertical". -/
theorem IsHomLift.id_iff_exists_eqToHom {𝒮 : Type*} {𝒞 : Type*} [Category 𝒮] [Category 𝒞]
    (s : 𝒮 ⥤ 𝒞) {a b : 𝒮} (ψ : a ⟶ b) :
    s.IsHomLift (𝟙 (s.obj a)) ψ ↔ ∃ h : s.obj a = s.obj b, s.map ψ = eqToHom h := by
  constructor
  · intro hψ
    refine ⟨(IsHomLift.codomain_eq s (𝟙 (s.obj a)) ψ).symm, ?_⟩
    simpa using IsHomLift.fac' s (𝟙 (s.obj a)) ψ
  · rintro ⟨h, heq⟩
    exact IsHomLift.of_fac' s (𝟙 (s.obj a)) ψ rfl h.symm (by simpa using heq)

namespace Functor

/-- A natural transformation is `s`-*vertical* when each of its components lies over an
identity of `𝒞`. -/
@[sga "4 VI 6.0"]
def IsVerticalNatTrans {𝒮 : Type u₁} {𝒮' : Type u₃} {𝒞 : Type u₂}
    [Category.{v₁} 𝒮] [Category.{v₃} 𝒮'] [Category.{v₂} 𝒞]
    (s : 𝒮 ⥤ 𝒞) {F G : 𝒮' ⥤ 𝒮} (α : F ⟶ G) : Prop :=
  ∀ X, s.IsHomLift (𝟙 (s.obj (F.obj X))) (α.app X)

/-- An *equivalence over `𝒞`*: a 1-morphism `a : 𝒳 ⥤ 𝒳'` over `𝒞` (so `a ⋙ r = p`) together
with a quasi-inverse that is again strictly a 1-morphism over `𝒞`, and unit and counit
isomorphisms whose components are vertical.

This is strictly stronger than `a` being an equivalence of the underlying categories: the
quasi-inverse commutes strictly with the structure functors, and both unit and counit are
vertical natural isomorphisms. -/
structure IsEquivalenceOver {𝒳 : Type u₁} {𝒳' : Type u₃} {𝒞 : Type u₂}
    [Category.{v₁} 𝒳] [Category.{v₃} 𝒳'] [Category.{v₂} 𝒞]
    (p : 𝒳 ⥤ 𝒞) (r : 𝒳' ⥤ 𝒞) (a : 𝒳 ⥤ 𝒳') : Type (max u₁ v₁ u₃ v₃) where
  /-- the quasi-inverse functor -/
  inv : 𝒳' ⥤ 𝒳
  /-- the quasi-inverse is strictly a 1-morphism over `𝒞`: `inv ⋙ p = r` -/
  inv_over : inv ⋙ p = r
  /-- unit natural isomorphism `a ⋙ inv ≅ 𝟭 𝒳` -/
  unitIso : a ⋙ inv ≅ 𝟭 𝒳
  /-- counit natural isomorphism `inv ⋙ a ≅ 𝟭 𝒳'` -/
  counitIso : inv ⋙ a ≅ 𝟭 𝒳'
  /-- the unit isomorphism is vertical over `𝒞` -/
  unit_vertical : IsVerticalNatTrans p unitIso.hom
  /-- the counit isomorphism is vertical over `𝒞` -/
  counit_vertical : IsVerticalNatTrans r counitIso.hom

namespace IsFiberedInGroupoids.Factorization

variable {𝒞 : Type u₂} [Category.{v₂} 𝒞]
    {𝒳 : Type u₁} [Category.{v₁} 𝒳]
    {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- The canonical vertical isomorphism between two lifts of the same base morphism in a
category fibred in groupoids, bundled with its defining properties. -/
structure LiftIsoData (P : 𝒳 ⥤ 𝒞) {x y z : 𝒳} (φ : y ⟶ x) (ψ : z ⟶ x)
    (hyz : P.obj z = P.obj y) where
  /-- the comparison isomorphism between the two lifts -/
  iso : z ≅ y
  /-- it lies over the identity, in the `eqToHom` form -/
  map_hom : P.map iso.hom = eqToHom hyz
  /-- it identifies the two lifts -/
  comp_hom : iso.hom ≫ φ = ψ

/-- In a category fibred in groupoids, two lifts of the same base morphism to the same target
are canonically isomorphic over the identity. -/
noncomputable def liftIsoData (P : 𝒳 ⥤ 𝒞) (hP : P.IsFiberedInGroupoids)
    {x y z : 𝒳} (φ : y ⟶ x) (ψ : z ⟶ x)
    (hyz : P.obj z = P.obj y)
    (hcompat : eqToHom hyz ≫ P.map φ = P.map ψ) :
    LiftIsoData P φ ψ hyz := by
  choose χ hχ huniq using hP.unique_lift φ ψ (eqToHom hyz) hcompat
  have hcompat' : eqToHom hyz.symm ≫ P.map ψ = P.map φ := by rw [← hcompat]; simp
  choose δ hδ huniqδ using hP.unique_lift ψ φ (eqToHom hyz.symm) hcompat'
  obtain ⟨hχmap, hχfac⟩ := hχ
  obtain ⟨hδmap, hδfac⟩ := hδ
  refine ⟨⟨χ, δ, ?_, ?_⟩, hχmap, hχfac⟩
  · choose _ _ huz using hP.unique_lift ψ ψ (𝟙 (P.obj z)) (by simp)
    rw [huz (χ ≫ δ) ⟨by rw [P.map_comp, hχmap, hδmap]; simp, by rw [Category.assoc, hδfac, hχfac]⟩,
        huz (𝟙 z) ⟨by simp, by simp⟩]
  · choose _ _ huy using hP.unique_lift φ φ (𝟙 (P.obj y)) (by simp)
    rw [huy (δ ≫ χ) ⟨by rw [P.map_comp, hδmap, hχmap]; simp, by rw [Category.assoc, hχfac, hδfac]⟩,
        huy (𝟙 y) ⟨by simp, by simp⟩]

/-- Objects of the vertical iso-comma category `𝒳 ×_{F, 𝒴, 𝟭} 𝒴`: triples `(x, y, φ)` with
`φ : F x ≅ y` an isomorphism of `𝒴` lying over an identity of `𝒞`. -/
structure XPrime (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) where
  /-- the object of `𝒳` -/
  x : 𝒳
  /-- the object of `𝒴` -/
  y : 𝒴
  /-- the comparison isomorphism `F x ≅ y` -/
  φ : F.obj x ≅ y
  /-- the comparison isomorphism is `q`-vertical, i.e. lies over an identity of `𝒞` -/
  vert : q.IsHomLift (𝟙 (q.obj (F.obj x))) φ.hom
  /-- A universe filler. It carries no information, but it raises the object type of `XPrime`
  from `Type (max u₁ u₃ v₃)` to `Type (max u₁ u₃ v₁ v₃)`, which is the universe in which the
  existential of Stacks 06N7 quantifies over the intermediate category. -/
  filler : ULift.{v₁} PUnit.{1}

/-- Morphisms of the vertical iso-comma category: a pair of morphisms of `𝒳` and `𝒴`
commuting with the comparison isomorphisms. -/
structure XPrimeHom (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) (A B : XPrime q F) where
  /-- the `𝒳`-component -/
  u : A.x ⟶ B.x
  /-- the `𝒴`-component -/
  v : A.y ⟶ B.y
  /-- the comparison square commutes -/
  w : F.map u ≫ B.φ.hom = A.φ.hom ≫ v

attribute [reassoc] XPrimeHom.w

/-- The category structure on the vertical iso-comma category `XPrime q F`, with `XPrimeHom`
as hom-type and identities and composition taken componentwise in `𝒳` and `𝒴`. -/
instance (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : Category.{max v₁ v₃} (XPrime q F) where
  Hom A B := XPrimeHom q F A B
  id A := { u := 𝟙 A.x, v := 𝟙 A.y, w := by simp }
  comp {A B C} f g :=
    { u := f.u ≫ g.u
      v := f.v ≫ g.v
      w := by rw [Functor.map_comp, Category.assoc, g.w, XPrimeHom.w_assoc] }
  id_comp f := by cases f; simp
  comp_id f := by cases f; simp
  assoc f g h := by cases f; cases g; cases h; simp

/-- Two morphisms of `XPrime q F` are equal as soon as their `𝒳`- and `𝒴`-components are: the
compatibility square `XPrimeHom.w` is a proposition and carries no extra data. This is what
reduces uniqueness of a fill-in in `XPrime q F` to uniqueness in `𝒳` and in `𝒴`. -/
@[ext]
lemma XPrimeHom.ext' {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {A B : XPrime q F} {f g : A ⟶ B}
    (hu : f.u = g.u) (hv : f.v = g.v) : f = g := by
  obtain ⟨fu, fv, fw⟩ := f
  obtain ⟨gu, gv, gw⟩ := g
  simp only at hu hv
  subst hu; subst hv; rfl

/-- The `𝒳`-component of the identity of `A` in `XPrime q F` is the identity of `A.x`. -/
@[simp] lemma XPrime.id_u {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} (A : XPrime q F) :
    (𝟙 A : A ⟶ A).u = 𝟙 A.x := rfl
/-- The `𝒴`-component of the identity of `A` in `XPrime q F` is the identity of `A.y`. -/
@[simp] lemma XPrime.id_v {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} (A : XPrime q F) :
    (𝟙 A : A ⟶ A).v = 𝟙 A.y := rfl
/-- The `𝒳`-component of a composite in `XPrime q F` is the composite of the `𝒳`-components. -/
@[simp] lemma XPrime.comp_u {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {A B C : XPrime q F}
    (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).u = f.u ≫ g.u := rfl
/-- The `𝒴`-component of a composite in `XPrime q F` is the composite of the `𝒴`-components. -/
@[simp] lemma XPrime.comp_v {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {A B C : XPrime q F}
    (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).v = f.v ≫ g.v := rfl

/-- The structure functor `r : XPrime q F ⥤ 𝒞`, `(x, y, φ) ↦ p x`. -/
@[implicit_reducible]
def XPrime.structureFunctor (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : XPrime q F ⥤ 𝒞 where
  obj A := p.obj A.x
  map f := p.map f.u
  map_id := by intro A; simp
  map_comp := by intro A B C f g; simp

/-- The 1-morphism `a : 𝒳 ⥤ XPrime q F`, `x ↦ (x, F x, refl)`. -/
@[implicit_reducible]
def XPrime.fromLeft (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : 𝒳 ⥤ XPrime q F where
  obj x := { x := x, y := F.obj x, φ := Iso.refl _, vert := IsHomLift.id rfl,
             filler := ⟨PUnit.unit⟩ }
  map {a b} u := { u := u, v := F.map u, w := by simp }
  map_id := by intro a; ext <;> simp
  map_comp := by intro a b c f g; ext <;> simp

/-- The 1-morphism `t : XPrime q F ⥤ 𝒴`, `(x, y, φ) ↦ y`. -/
@[implicit_reducible]
def XPrime.toRight (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : XPrime q F ⥤ 𝒴 where
  obj A := A.y
  map f := f.v
  map_id := by intro A; simp
  map_comp := by intro A B C f g; simp

/-- The quasi-inverse `b : XPrime q F ⥤ 𝒳` of `XPrime.fromLeft`, `(x, y, φ) ↦ x`. -/
@[implicit_reducible]
def XPrime.projLeft (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : XPrime q F ⥤ 𝒳 where
  obj A := A.x
  map f := f.u
  map_id := by intro A; simp
  map_comp := by intro A B C f g; simp

variable (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)

/-- `a` is a 1-morphism over `𝒞`. -/
lemma XPrime.fromLeft_comp_structureFunctor :
    fromLeft q F ⋙ structureFunctor p q F = p := by
  apply CategoryTheory.Functor.ext
  · intro X Y f; simp [fromLeft, structureFunctor]
  · intro X; rfl

/-- The factorization is exact: `a ⋙ t = F`. -/
lemma XPrime.fromLeft_comp_toRight : fromLeft q F ⋙ toRight q F = F := by
  apply CategoryTheory.Functor.ext
  · intro X Y f; simp [fromLeft, toRight]
  · intro X; rfl

/-- `q ∘ F = p` on objects. -/
lemma obj_eq_of_comp_eq (hF : F ⋙ q = p) (z : 𝒳) : q.obj (F.obj z) = p.obj z := by
  rw [← hF]; rfl

/-- `q ∘ F = p` on morphisms. -/
lemma map_eq_of_comp_eq (hF : F ⋙ q = p) {z w : 𝒳} (u : z ⟶ w) :
    q.map (F.map u) = eqToHom (obj_eq_of_comp_eq p q F hF z) ≫ p.map u
      ≫ eqToHom (obj_eq_of_comp_eq p q F hF w).symm :=
  CategoryTheory.Functor.congr_hom hF u

/-- `t` is a 1-morphism over `𝒞`. -/
lemma XPrime.toRight_comp_eq (hF : F ⋙ q = p) : toRight q F ⋙ q = structureFunctor p q F := by
  apply CategoryTheory.Functor.ext
  · intro A B f
    obtain ⟨hA, hAeq⟩ := (IsHomLift.id_iff_exists_eqToHom q A.φ.hom).1 A.vert
    obtain ⟨hB, hBeq⟩ := (IsHomLift.id_iff_exists_eqToHom q B.φ.hom).1 B.vert
    have hqcomm := congrArg q.map f.w
    rw [q.map_comp, q.map_comp, hAeq, hBeq] at hqcomm
    have hfv : q.map f.v = eqToHom hA.symm ≫ q.map (F.map f.u) ≫ eqToHom hB := by
      rw [hqcomm, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    simp only [toRight, structureFunctor, Functor.comp_obj, Functor.comp_map]
    rw [hfv, map_eq_of_comp_eq p q F hF f.u]
    simp
  · intro A
    simp only [Functor.comp_obj, toRight, structureFunctor]
    obtain ⟨hA, hAeq⟩ := (IsHomLift.id_iff_exists_eqToHom q A.φ.hom).1 A.vert
    rw [← hA, obj_eq_of_comp_eq p q F hF]

/-- `b` is a strict section of `a`. -/
lemma XPrime.fromLeft_comp_projLeft : fromLeft q F ⋙ projLeft q F = 𝟭 𝒳 := by
  apply CategoryTheory.Functor.ext
  · intro X Y f; simp [fromLeft, projLeft]
  · intro X; rfl

/-- `b` is a 1-morphism over `𝒞`. -/
lemma XPrime.projLeft_comp_eq : projLeft q F ⋙ p = structureFunctor p q F := by
  apply CategoryTheory.Functor.ext
  · intro X Y f; simp [projLeft, structureFunctor]
  · intro X; rfl

/-- The counit isomorphism `b ⋙ a ≅ 𝟭 (XPrime q F)`, with component at `A = (x, y, φ)`
given by `(𝟙 x, φ.hom)`. -/
def XPrime.counitIso : projLeft q F ⋙ fromLeft q F ≅ 𝟭 (XPrime q F) :=
  NatIso.ofComponents
    (fun A =>
      { hom := { u := 𝟙 A.x, v := A.φ.hom, w := by simp [fromLeft, projLeft] }
        inv := { u := 𝟙 A.x, v := A.φ.inv, w := by simp [fromLeft, projLeft] }
        hom_inv_id := by ext <;> simp [fromLeft, projLeft]
        inv_hom_id := by ext <;> simp [fromLeft, projLeft] })
    (by
      intro A B f
      ext <;> simp [fromLeft, projLeft, XPrimeHom.w])

/-- The `p`-image of the `𝒳`-leg of an iso-comma morphism, solved from its compatibility
square by applying `q`. -/
lemma map_u_eq (hF : F ⋙ q = p) {A B : XPrime q F} (g : A ⟶ B)
    {hA : q.obj (F.obj A.x) = q.obj A.y} (hAeq : q.map A.φ.hom = eqToHom hA)
    {hB : q.obj (F.obj B.x) = q.obj B.y} (hBeq : q.map B.φ.hom = eqToHom hB) :
    p.map g.u = eqToHom (obj_eq_of_comp_eq p q F hF A.x).symm ≫ eqToHom hA ≫ q.map g.v
        ≫ eqToHom hB.symm ≫ eqToHom (obj_eq_of_comp_eq p q F hF B.x) := by
  have key := congrArg q.map g.w
  rw [q.map_comp, q.map_comp, map_eq_of_comp_eq p q F hF g.u, hAeq, hBeq] at key
  have hgoal : eqToHom (obj_eq_of_comp_eq p q F hF A.x) ≫ p.map g.u
        ≫ eqToHom (obj_eq_of_comp_eq p q F hF B.x).symm
      = eqToHom hA ≫ q.map g.v ≫ eqToHom hB.symm := by
    rw [← cancel_mono (eqToHom hB)]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at key ⊢
    exact key
  calc p.map g.u
      = eqToHom (obj_eq_of_comp_eq p q F hF A.x).symm
          ≫ (eqToHom (obj_eq_of_comp_eq p q F hF A.x) ≫ p.map g.u
            ≫ eqToHom (obj_eq_of_comp_eq p q F hF B.x).symm)
          ≫ eqToHom (obj_eq_of_comp_eq p q F hF B.x) := by simp
    _ = eqToHom (obj_eq_of_comp_eq p q F hF A.x).symm
          ≫ (eqToHom hA ≫ q.map g.v ≫ eqToHom hB.symm)
          ≫ eqToHom (obj_eq_of_comp_eq p q F hF B.x) := by
        rw [hgoal]
    _ = eqToHom (obj_eq_of_comp_eq p q F hF A.x).symm ≫ eqToHom hA ≫ q.map g.v
          ≫ eqToHom hB.symm ≫ eqToHom (obj_eq_of_comp_eq p q F hF B.x) := by
        simp

/-- The `𝒴`-legs of two morphisms of the iso-comma category with a common target are related by
any fill-in of their `𝒳`-legs: this is the compatibility square of `XPrimeHom.w` transported
along `k`. -/
lemma XPrime.comp_v_of_comp_u {x y z : XPrime q F} (φ : y ⟶ x) (ψ : z ⟶ x) {k : z.x ⟶ y.x}
    (hk : k ≫ φ.u = ψ.u) :
    (F.map k ≫ y.φ.hom) ≫ φ.v = z.φ.hom ≫ ψ.v := by
  rw [Category.assoc, ← φ.w, ← Category.assoc, ← F.map_comp, hk, ψ.w]

/-- Existence of lifts for `t : XPrime q F ⥤ 𝒴`: a morphism `g : V ⟶ A.y` of `𝒴` is lifted by
taking a lift `χ` of its `p`-image in `𝒳` and comparing the two lifts `F χ ≫ A.φ` and `g` of that
image in `𝒴`. -/
lemma XPrime.toRight_exists_lift (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : F ⋙ q = p) {V U : 𝒴} (g : V ⟶ U) (A : XPrime q F) (hAU : A.y = U) :
    ∃ (B : XPrime q F) (χ : B ⟶ A), (toRight q F).IsHomLift g χ := by
  subst hAU
  obtain ⟨hAvert, hAeq⟩ := (IsHomLift.id_iff_exists_eqToHom q A.φ.hom).1 A.vert
  have hbase : p.obj A.x = q.obj A.y := by rw [← hAvert, obj_eq_of_comp_eq p q F hF]
  set basemor : q.obj V ⟶ p.obj A.x := q.map g ≫ eqToHom hbase.symm with hbasemor
  obtain ⟨b, χ, hχ⟩ := hp.exists_lift basemor A.x rfl
  have := hχ
  have hbV : p.obj b = q.obj V := IsHomLift.domain_eq p basemor χ
  have hχmap : p.map χ = eqToHom hbV ≫ q.map g ≫ eqToHom hbase.symm := by
    rw [IsHomLift.fac' p basemor χ]; simp [hbasemor]
  have hyz : q.obj V = q.obj (F.obj b) := by
    rw [obj_eq_of_comp_eq p q F hF b, hbV]
  obtain ⟨Diso, Dmap, Dcomp⟩ := liftIsoData q hq (F.map χ ≫ A.φ.hom) g hyz (by
    rw [q.map_comp, hAeq, map_eq_of_comp_eq p q F hF χ, hχmap]
    simp)
  refine ⟨{ x := b, y := V, φ := Diso.symm, vert := ?_, filler := ⟨PUnit.unit⟩ },
          { u := χ, v := g, w := ?_ }, ?_⟩
  · refine (IsHomLift.id_iff_exists_eqToHom q _).2 ⟨hyz.symm, ?_⟩
    rw [Iso.symm_hom]
    rw [← cancel_epi (q.map Diso.hom), ← q.map_comp]
    simp [Dmap]
  · dsimp only
    rw [Iso.symm_hom, Iso.eq_inv_comp]
    exact Dcomp
  · exact IsHomLift.of_fac' (toRight q F) g _ rfl rfl (by simp [toRight])

/-- Existence and uniqueness of fill-ins for `t : XPrime q F ⥤ 𝒴`.  The `𝒳`-leg of the fill-in is
forced: applying `q` to the desired square determines the base morphism it must lie over, and the
fill-in axiom for `p` then produces it. -/
lemma XPrime.toRight_unique_lift (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : F ⋙ q = p) {x y z : XPrime q F} (φ : y ⟶ x) (ψ : z ⟶ x) (f : z.y ⟶ y.y)
    (hf : f ≫ φ.v = ψ.v) :
    ∃! χ : z ⟶ y, (toRight q F).map χ = f ∧ χ ≫ φ = ψ := by
  obtain ⟨hY, hYeq⟩ := (IsHomLift.id_iff_exists_eqToHom q y.φ.hom).1 y.vert
  obtain ⟨hZ, hZeq⟩ := (IsHomLift.id_iff_exists_eqToHom q z.φ.hom).1 z.vert
  obtain ⟨hX, hXeq⟩ := (IsHomLift.id_iff_exists_eqToHom q x.φ.hom).1 x.vert
  set base : p.obj z.x ⟶ p.obj y.x :=
    eqToHom (obj_eq_of_comp_eq p q F hF z.x).symm ≫ eqToHom hZ ≫ q.map f ≫ eqToHom hY.symm
      ≫ eqToHom (obj_eq_of_comp_eq p q F hF y.x)
    with hbase
  obtain ⟨k, ⟨hk1, hk2⟩, hkuniq⟩ := hp.unique_lift φ.u ψ.u base (by
    rw [hbase, map_u_eq p q F hF φ hYeq hXeq, map_u_eq p q F hF ψ hZeq hXeq, ← hf, q.map_comp]
    simp)
  have hqsq : q.map (F.map k ≫ y.φ.hom) = q.map (z.φ.hom ≫ f) := by
    rw [q.map_comp, q.map_comp, map_eq_of_comp_eq p q F hF k, hYeq, hZeq, hk1, hbase]
    simp
  have sq : F.map k ≫ y.φ.hom = z.φ.hom ≫ f := by
    have := hq.isStronglyCartesian φ.v
    have : q.IsHomLift (q.map (F.map k ≫ y.φ.hom)) (z.φ.hom ≫ f) := by
      rw [hqsq]; infer_instance
    exact IsStronglyCartesian.ext q (q.map φ.v) φ.v (q.map (F.map k ≫ y.φ.hom))
      (by rw [XPrime.comp_v_of_comp_u q F φ ψ hk2, Category.assoc, hf])
  refine ⟨{ u := k, v := f, w := sq }, ⟨rfl, XPrimeHom.ext' hk2 hf⟩, ?_⟩
  rintro χ' ⟨hχ'v, hχ'comp⟩
  refine XPrimeHom.ext' (hkuniq _ ⟨?_, ?_⟩) hχ'v
  · rw [hbase, map_u_eq p q F hF χ' hZeq hYeq, show χ'.v = f from hχ'v]
  · simpa using congrArg XPrimeHom.u hχ'comp

/-- `t : XPrime q F ⥤ 𝒴` is fibred in groupoids: this is what exhibits `𝒳'` as fibred in
groupoids over `𝒴`, clause (3) of Stacks 06N7. -/
lemma XPrime.toRight_isFiberedInGroupoids (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (hF : F ⋙ q = p) :
    (toRight q F).IsFiberedInGroupoids where
  exists_lift g A hAU := toRight_exists_lift p q F hp hq hF g A hAU
  unique_lift φ ψ f hf := toRight_unique_lift p q F hp hq hF φ ψ f hf

/-- Existence of lifts for `r : XPrime q F ⥤ 𝒞`: a lift in `𝒳` of the base morphism extends to
the iso-comma category by taking the identity comparison isomorphism. -/
lemma XPrime.structureFunctor_exists_lift (hp : p.IsFiberedInGroupoids) {V U : 𝒞} (g : V ⟶ U)
    (A : XPrime q F) (hAU : p.obj A.x = U) :
    ∃ (B : XPrime q F) (χ : B ⟶ A), (structureFunctor p q F).IsHomLift g χ := by
  obtain ⟨x₀, χ, hχ⟩ := hp.exists_lift g A.x hAU
  have := hχ
  have hdom : p.obj x₀ = V := IsHomLift.domain_eq p g χ
  refine ⟨{ x := x₀, y := F.obj x₀, φ := Iso.refl _,
            vert := IsHomLift.id rfl, filler := ⟨PUnit.unit⟩ },
          { u := χ, v := F.map χ ≫ A.φ.hom, w := by simp }, ?_⟩
  exact IsHomLift.of_fac' (structureFunctor p q F) g _ hdom hAU (IsHomLift.fac' p g χ)

/-- Existence and uniqueness of fill-ins for `r : XPrime q F ⥤ 𝒞`.  The `𝒳`-leg is the fill-in
provided by `p`, and the `𝒴`-leg is then forced to be its conjugate by the comparison
isomorphisms. -/
lemma XPrime.structureFunctor_unique_lift (hp : p.IsFiberedInGroupoids) {A B₁ B₂ : XPrime q F}
    (φ : B₁ ⟶ A) (ψ : B₂ ⟶ A) (base : p.obj B₂.x ⟶ p.obj B₁.x)
    (hcomm : base ≫ p.map φ.u = p.map ψ.u) :
    ∃! χ : B₂ ⟶ B₁, (structureFunctor p q F).map χ = base ∧ χ ≫ φ = ψ := by
  obtain ⟨k, ⟨hk1, hk2⟩, hkuniq⟩ := hp.unique_lift φ.u ψ.u base hcomm
  have hv : (B₂.φ.inv ≫ F.map k ≫ B₁.φ.hom) ≫ φ.v = ψ.v := by
    rw [Category.assoc, XPrime.comp_v_of_comp_u q F φ ψ hk2, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  refine ⟨{ u := k, v := B₂.φ.inv ≫ F.map k ≫ B₁.φ.hom, w := by simp },
    ⟨hk1, XPrimeHom.ext' hk2 hv⟩, ?_⟩
  rintro χ' ⟨hχ'1, hχ'2⟩
  have hu : χ'.u = k := hkuniq _ ⟨hχ'1, by simpa using congrArg XPrimeHom.u hχ'2⟩
  refine XPrimeHom.ext' hu ?_
  rw [← cancel_epi B₂.φ.hom, ← χ'.w, hu, ← Category.assoc, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- `r : XPrime q F ⥤ 𝒞` is fibred in groupoids: clause (1) of Stacks 06N7. -/
lemma XPrime.structureFunctor_isFiberedInGroupoids (hp : p.IsFiberedInGroupoids)
    (_hq : q.IsFiberedInGroupoids) (_hF : F ⋙ q = p) :
    (structureFunctor p q F).IsFiberedInGroupoids where
  exists_lift g A hAU := structureFunctor_exists_lift p q F hp g A hAU
  unique_lift φ ψ base hcomm := structureFunctor_unique_lift p q F hp φ ψ base hcomm

end IsFiberedInGroupoids.Factorization

open IsFiberedInGroupoids.Factorization in
/-- **Stacks 06N7 (Lemma 4.35.16).** Let `𝒞` be a category and let `𝒳`, `𝒴` be categories
fibred in groupoids over `𝒞` via `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞`. Let `F : 𝒳 ⥤ 𝒴` be a
1-morphism over `𝒞` (`F ⋙ q = p`). Then there exist a category `𝒳'`, a structure functor
`r : 𝒳' ⥤ 𝒞` and functors `a : 𝒳 ⥤ 𝒳'`, `t : 𝒳' ⥤ 𝒴` such that

1. `r` is fibred in groupoids over `𝒞`;
2. `a` is a 1-morphism over `𝒞` (`a ⋙ r = p`) and an equivalence over `𝒞`;
3. `t` is a 1-morphism over `𝒞` (`t ⋙ q = r`) and is fibred in groupoids over `𝒴`;
4. `a ⋙ t = F`. -/
@[stacks 06N7]
theorem IsFiberedInGroupoids.exists_factorization_isFiberedInGroupoids
    {𝒞 : Type u₂} [Category.{v₂} 𝒞]
    {𝒳 : Type u₁} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type u₃} [Category.{v₃} 𝒴] (q : 𝒴 ⥤ 𝒞) (hq : q.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ q = p) :
    ∃ (𝒳' : Type (max u₁ u₃ v₁ v₃)) (_ : Category.{max v₁ v₃} 𝒳')
      (r : 𝒳' ⥤ 𝒞) (a : 𝒳 ⥤ 𝒳') (t : 𝒳' ⥤ 𝒴),
      r.IsFiberedInGroupoids ∧
      (a ⋙ r = p) ∧ Nonempty (IsEquivalenceOver p r a) ∧
      (t ⋙ q = r) ∧ t.IsFiberedInGroupoids ∧
      (a ⋙ t = F) := by
  refine ⟨XPrime q F, inferInstance, XPrime.structureFunctor p q F,
          XPrime.fromLeft q F, XPrime.toRight q F,
          XPrime.structureFunctor_isFiberedInGroupoids p q F hp hq hF,
          XPrime.fromLeft_comp_structureFunctor p q F,
          ⟨?_⟩,
          XPrime.toRight_comp_eq p q F hF,
          XPrime.toRight_isFiberedInGroupoids p q F hp hq hF,
          XPrime.fromLeft_comp_toRight q F⟩
  exact
    { inv := XPrime.projLeft q F
      inv_over := XPrime.projLeft_comp_eq p q F
      unitIso := eqToIso (XPrime.fromLeft_comp_projLeft q F).symm
      counitIso := XPrime.counitIso q F
      unit_vertical := by
        intro A
        refine (IsHomLift.id_iff_exists_eqToHom p _).2 ⟨rfl, ?_⟩
        rw [eqToIso.hom, eqToHom_app, eqToHom_map]
      counit_vertical := by
        intro A
        refine (IsHomLift.id_iff_exists_eqToHom (XPrime.structureFunctor p q F) _).2 ⟨rfl, ?_⟩
        simp [XPrime.counitIso, XPrime.structureFunctor, XPrime.fromLeft, XPrime.projLeft] }

end Functor

end CategoryTheory
