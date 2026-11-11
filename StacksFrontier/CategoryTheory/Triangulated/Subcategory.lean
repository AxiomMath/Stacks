module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksCore.Tactic.StacksAttribute

/-!
# Pre-triangulated and triangulated subcategories

Let `(D, [ ], T)` be a pre-triangulated category. Following [Stacks, Tag 05QM], a
*pre-triangulated subcategory* of `D` is a pair `(D', T')` such that

1. `D'` is an additive subcategory of `D` which is preserved under `[1]`, and such that
   `[1] : D' → D'` is an auto-equivalence,
2. `T' ⊆ T` is a set of distinguished triangles of `D` such that for every
   `(X, Y, Z, f, g, h) ∈ T'` the objects `X, Y, Z` and the morphisms `f, g, h` lie in `D'`,
3. `(D', [ ], T')` is a pre-triangulated category.

If `D` is triangulated, `(D', T')` is a *triangulated subcategory* when moreover
`(D', [ ], T')` is a triangulated category.

The subcategory `D'` need not be full: it is given by a predicate on the objects of `D` and a
predicate on the morphisms of `D`.

## Main definitions

* `CategoryTheory.Pretriangulated.AdditiveSubcategory D`: an additive (not necessarily full)
  subcategory of a preadditive category `D`.
* `CategoryTheory.Pretriangulated.AdditiveSubcategory.Carrier`: the subcategory itself, as a
  preadditive category, with its faithful additive inclusion `ι` into `D`; it has a zero object
  and binary (hence finite) biproducts, so it is an additive category.
* `CategoryTheory.Pretriangulated.AdditiveSubcategory.restrict`: the endofunctor of the
  subcategory induced by an endofunctor of `D` preserving it.
* `CategoryTheory.Pretriangulated.PretriangulatedSubcategory D`: a pre-triangulated
  subcategory `(D', T')` of the pre-triangulated category `D` ([Stacks, Tag 05QM]).
* `CategoryTheory.Pretriangulated.TriangulatedSubcategory D`: a triangulated subcategory of
  the triangulated category `D` ([Stacks, Tag 05QM]).
* `CategoryTheory.Pretriangulated.PretriangulatedSubcategory.top`,
  `CategoryTheory.Pretriangulated.TriangulatedSubcategory.top`: `(D, T)` itself.

## Implementation notes

*The additive subcategory.* A subcategory `D'` of `D` is a set of objects `obj` and a set of
morphisms `hom`, every morphism of `hom` having source and target in `obj`, containing the
identities of the objects of `obj` and closed under composition. The source asks that `D'` be
*additive* and that it be an additive subcategory, i.e. that `D'` be an additive category and
the inclusion `D' → D` an additive functor. Since the inclusion is injective on morphisms, its
additivity says exactly that each `Hom_{D'}(X, Y)` is a subgroup of `Hom_D(X, Y)` carrying the
induced group structure: this is `zero_mem`, `add_mem`, `neg_mem`. An additive functor sends
zero objects to zero objects and biproduct diagrams to biproduct diagrams; conversely, a zero
object of `D` lying in `D'` is a zero object of `D'` (its `Hom`-sets in `D'` are subsets of
singletons containing `0`), and a biproduct diagram of `D` whose four structure morphisms lie
in `D'` is one of `D'` (the biproduct identities characterize biproducts in a preadditive
category, `CategoryTheory.Limits.isBinaryBilimitOfTotal`). So "`D'` has a zero object and
binary direct sums" is `exists_isZero` and `exists_bicone`; `Carrier.hasZeroObject` and
`Carrier.hasBinaryBiproducts` confirm that these conditions make `D'` additive. In particular
a zero object of `D'` is the same thing as a zero object of `D` lying in `D'`, which is how
the zero object of TR1 is read below. No closure under isomorphism is imposed.

*The shift.* The source's `[1] : D' → D'` is the restriction of the ambient `[1]`, which
exists because `D'` is preserved by `[1]` on objects and on morphisms (`shift_obj`,
`shift_hom`); that it is an auto-equivalence is the field `isEquivalence_shift`, about the
induced functor `AdditiveSubcategory.restrict` on `Carrier`. It is additive automatically.

*The distinguished triangles.* `T'` is the field `triangles`, a set of triangles of `D`.
The source's axioms TR1–TR3 for `(D', [ ], T')` are transcribed internally to `D'`:
a triangle of `D'` is a triangle of `D` whose objects and morphisms lie in `D'`
(`AdditiveSubcategory.IsTriangle`; its third morphism has target `X[1]`, the restricted
shift agreeing with the ambient one), and an isomorphism of triangles of `D'` is an
isomorphism of triangles of `D` all of whose components and inverse components lie in `D'`.
The morphism `c` produced by TR3 and the morphisms `a, b` produced by TR4 are required to be
morphisms of `D'`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open Category Limits Preadditive ZeroObject

variable (D : Type u) [Category.{v} D]

/-- An *additive subcategory* `D'` of a preadditive category `D`, not necessarily full: a set
of objects `obj` and a set of morphisms `hom` forming a subcategory of `D`, such that `D'` is
an additive category and the inclusion `D' → D` is additive. Additivity of the inclusion
makes each `Hom_{D'}(X, Y)` a subgroup of `Hom_D(X, Y)`; a zero object and binary direct sums
of `D'` are then a zero object of `D` lying in `D'` and binary biproduct diagrams of `D` lying
in `D'` (see the module docstring). -/
structure AdditiveSubcategory [Preadditive D] where
  /-- The objects of the subcategory. -/
  obj : ObjectProperty D
  /-- The morphisms of the subcategory. -/
  hom : MorphismProperty D
  /-- The source of a morphism of the subcategory is an object of the subcategory. -/
  obj_src : ∀ {X Y : D} {f : X ⟶ Y}, hom f → obj X
  /-- The target of a morphism of the subcategory is an object of the subcategory. -/
  obj_tgt : ∀ {X Y : D} {f : X ⟶ Y}, hom f → obj Y
  /-- The subcategory contains the identities of its objects. -/
  id_mem : ∀ {X : D}, obj X → hom (𝟙 X)
  /-- The subcategory is closed under composition. -/
  comp_mem : ∀ {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z}, hom f → hom g → hom (f ≫ g)
  /-- `Hom_{D'}(X, Y)` contains `0`. -/
  zero_mem : ∀ {X Y : D}, obj X → obj Y → hom (0 : X ⟶ Y)
  /-- `Hom_{D'}(X, Y)` is closed under addition. -/
  add_mem : ∀ {X Y : D} {f g : X ⟶ Y}, hom f → hom g → hom (f + g)
  /-- `Hom_{D'}(X, Y)` is closed under negation. -/
  neg_mem : ∀ {X Y : D} {f : X ⟶ Y}, hom f → hom (-f)
  /-- `D'` has a zero object. -/
  exists_isZero : ∃ Z : D, obj Z ∧ IsZero Z
  /-- Any two objects of `D'` have a direct sum in `D'`. -/
  exists_bicone : ∀ {X Y : D}, obj X → obj Y → ∃ b : BinaryBicone X Y,
    Nonempty b.IsBilimit ∧ obj b.pt ∧ hom b.fst ∧ hom b.snd ∧ hom b.inl ∧ hom b.inr

namespace AdditiveSubcategory

variable {D} [Preadditive D] (S : AdditiveSubcategory D)

/-- The objects of the subcategory `S`, as a type. -/
@[ext]
structure Carrier where
  /-- The underlying object of `D`. -/
  obj : D
  /-- It lies in `S`. -/
  property : S.obj obj

/-- The morphisms of `S` between two of its objects, as a subgroup of the morphisms in `D`. -/
def homSubgroup (X Y : S.Carrier) : AddSubgroup (X.obj ⟶ Y.obj) where
  carrier := {f | S.hom f}
  zero_mem' := S.zero_mem X.property Y.property
  add_mem' := S.add_mem
  neg_mem' := S.neg_mem

instance : Category.{v} S.Carrier where
  Hom X Y := S.homSubgroup X Y
  id X := ⟨𝟙 X.obj, S.id_mem X.property⟩
  comp f g := ⟨f.1 ≫ g.1, S.comp_mem f.2 g.2⟩
  id_comp f := Subtype.ext (id_comp f.1)
  comp_id f := Subtype.ext (comp_id f.1)
  assoc f g h := Subtype.ext (assoc f.1 g.1 h.1)

variable {S}

@[ext]
lemma hom_ext {X Y : S.Carrier} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g := Subtype.ext h

@[simp]
lemma id_val (X : S.Carrier) : (𝟙 X : X ⟶ X).1 = 𝟙 X.obj := rfl

@[simp]
lemma comp_val {X Y Z : S.Carrier} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

variable (S)

instance : Preadditive S.Carrier where
  homGroup X Y := inferInstanceAs (AddCommGroup (S.homSubgroup X Y))
  add_comp _ _ _ f f' g := Subtype.ext (add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (comp_add _ _ _ f.1 g.1 g'.1)

@[simp]
lemma zero_val {X Y : S.Carrier} : (0 : X ⟶ Y).1 = 0 := rfl

/-- The inclusion functor of the subcategory `S` into `D`. -/
@[simps]
def ι : S.Carrier ⥤ D where
  obj X := X.obj
  map f := f.1

instance : S.ι.Faithful where
  map_injective h := Subtype.ext h

instance : S.ι.Additive where

/-- A zero object of `D` lying in `S` is a zero object of `S`. -/
lemma isZero_of_isZero {Z : S.Carrier} (hZ : IsZero Z.obj) : IsZero Z := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => hom_ext (hZ.eq_of_src _ _)⟩⟩,
    fun X => ⟨⟨⟨0⟩, fun f => hom_ext (hZ.eq_of_tgt _ _)⟩⟩⟩

instance hasZeroObject : HasZeroObject S.Carrier := by
  obtain ⟨Z, hZ, hZ'⟩ := S.exists_isZero
  exact (isZero_of_isZero (S := S) (Z := ⟨Z, hZ⟩) hZ').hasZeroObject

instance hasBinaryBiproducts : HasBinaryBiproducts S.Carrier where
  has_binary_biproduct X Y := by
    obtain ⟨b, ⟨hb⟩, hpt, hfst, hsnd, hinl, hinr⟩ := S.exists_bicone X.property Y.property
    let c : BinaryBicone X Y :=
      { pt := ⟨b.pt, hpt⟩
        fst := ⟨b.fst, hfst⟩
        snd := ⟨b.snd, hsnd⟩
        inl := ⟨b.inl, hinl⟩
        inr := ⟨b.inr, hinr⟩
        inl_fst := hom_ext b.inl_fst
        inl_snd := hom_ext b.inl_snd
        inr_fst := hom_ext b.inr_fst
        inr_snd := hom_ext b.inr_snd }
    exact HasBinaryBiproduct.mk ⟨c, isBinaryBilimitOfTotal c (hom_ext (IsBilimit.binary_total hb))⟩

/-- The subcategory `S` has finite biproducts: it is an additive category. -/
instance hasFiniteBiproducts : HasFiniteBiproducts S.Carrier :=
  have : HasTerminal S.Carrier := inferInstance
  have : HasFiniteProducts S.Carrier := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The endofunctor of the subcategory `S` induced by an endofunctor `F` of `D` which
preserves `S` on objects and on morphisms. -/
@[simps]
def restrict (F : D ⥤ D) (hobj : ∀ {X : D}, S.obj X → S.obj (F.obj X))
    (hhom : ∀ {X Y : D} {f : X ⟶ Y}, S.hom f → S.hom (F.map f)) : S.Carrier ⥤ S.Carrier where
  obj X := ⟨F.obj X.obj, hobj X.property⟩
  map f := ⟨F.map f.1, hhom f.2⟩
  map_id X := hom_ext (F.map_id X.obj)
  map_comp f g := hom_ext (F.map_comp f.1 g.1)

variable [HasShift D ℤ]

/-- A triangle of `D` is a *triangle of `S`* when its three objects and its three morphisms
lie in `S`. -/
def IsTriangle (T : Triangle D) : Prop :=
  S.obj T.obj₁ ∧ S.obj T.obj₂ ∧ S.obj T.obj₃ ∧ S.hom T.mor₁ ∧ S.hom T.mor₂ ∧ S.hom T.mor₃

/-- A morphism of triangles of `D` is a *morphism of triangles of `S`* when its three
components lie in `S`. -/
def IsTriangleHom {T₁ T₂ : Triangle D} (φ : T₁ ⟶ T₂) : Prop :=
  S.hom φ.hom₁ ∧ S.hom φ.hom₂ ∧ S.hom φ.hom₃

end AdditiveSubcategory

variable [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- **Stacks 05QM.** A *pre-triangulated subcategory* of the pre-triangulated category
`(D, [ ], T)`: a pair `(D', T')` where

1. `D'` is an additive (not necessarily full) subcategory of `D`
   (`toAdditiveSubcategory`), preserved under `[1]` (`shift_obj`, `shift_hom`), such that
   the induced functor `[1] : D' → D'` is an auto-equivalence (`isEquivalence_shift`);
2. `T' ⊆ T` (`triangles`, `triangles_subset`) is a set of distinguished triangles of `D` all
   of whose objects and morphisms lie in `D'` (`isTriangle_of_mem`);
3. `(D', [ ], T')` is a pre-triangulated category, i.e. satisfies TR1 (`isomorphic_mem`,
   `contractible_mem`, `exists_mem`), TR2 (`rotate_mem_iff`) and TR3 (`complete`), stated
   internally to `D'`: for triangles of `D'`, isomorphisms of triangles of `D'`, zero
   objects of `D'`, and morphisms of `D'`. -/
@[stacks 05QM "Pre-triangulated subcategory; the subcategory `D'` is a possibly non-full
additive subcategory, and TR1-TR3 for `(D', [ ], T')` are stated internally to `D'`."]
structure PretriangulatedSubcategory extends AdditiveSubcategory D where
  /-- `D'` is preserved by `[1]` on objects. -/
  shift_obj : ∀ {X : D}, obj X → obj (X⟦(1 : ℤ)⟧)
  /-- `D'` is preserved by `[1]` on morphisms. -/
  shift_hom : ∀ {X Y : D} {f : X ⟶ Y}, hom f → hom (f⟦(1 : ℤ)⟧')
  /-- The induced functor `[1] : D' → D'` is an auto-equivalence. -/
  isEquivalence_shift :
    (toAdditiveSubcategory.restrict (shiftFunctor D (1 : ℤ)) shift_obj shift_hom).IsEquivalence
  /-- The set `T'` of distinguished triangles of `D'`. -/
  triangles : Set (Triangle D)
  /-- `T' ⊆ T`. -/
  triangles_subset : triangles ⊆ distTriang D
  /-- The objects and morphisms of every triangle in `T'` lie in `D'`. -/
  isTriangle_of_mem : ∀ T ∈ triangles, toAdditiveSubcategory.IsTriangle T
  /-- TR1: a triangle of `D'` isomorphic in `D'` to a triangle of `T'` lies in `T'`. -/
  isomorphic_mem : ∀ T₁ ∈ triangles, ∀ T₂ : Triangle D, toAdditiveSubcategory.IsTriangle T₂ →
    ∀ e : T₂ ≅ T₁, toAdditiveSubcategory.IsTriangleHom e.hom →
      toAdditiveSubcategory.IsTriangleHom e.inv → T₂ ∈ triangles
  /-- TR1: for every object `X` of `D'` and zero object `Z` of `D'`, the triangle
  `(X, X, Z, id, 0, 0)` lies in `T'`. -/
  contractible_mem : ∀ {X Z : D}, obj X → obj Z → IsZero Z →
    Triangle.mk (𝟙 X) (0 : X ⟶ Z) (0 : Z ⟶ X⟦(1 : ℤ)⟧) ∈ triangles
  /-- TR1: every morphism `f : X ⟶ Y` of `D'` is the first morphism of a triangle of `T'`. -/
  exists_mem : ∀ {X Y : D} {f : X ⟶ Y}, hom f →
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ triangles
  /-- TR2: a triangle `(X, Y, Z, f, g, h)` of `D'` lies in `T'` if and only if its rotation
  `(Y, Z, X[1], g, h, -f[1])` does. -/
  rotate_mem_iff : ∀ T : Triangle D, toAdditiveSubcategory.IsTriangle T →
    (T ∈ triangles ↔ T.rotate ∈ triangles)
  /-- TR3: given triangles `T₁, T₂` of `T'` and morphisms `a, b` of `D'` with
  `b ∘ f₁ = f₂ ∘ a`, there is a morphism `c` of `D'` such that `(a, b, c)` is a morphism of
  triangles. -/
  complete : ∀ T₁ ∈ triangles, ∀ T₂ ∈ triangles, ∀ (a : T₁.obj₁ ⟶ T₂.obj₁)
    (b : T₁.obj₂ ⟶ T₂.obj₂), hom a → hom b → T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
      ∃ c : T₁.obj₃ ⟶ T₂.obj₃, hom c ∧ T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
        T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃

/-- **Stacks 05QM.** A *triangulated subcategory* of the triangulated category
`(D, [ ], T)`: a pre-triangulated subcategory `(D', T')` such that `(D', [ ], T')` is
moreover a triangulated category, i.e. satisfies TR4 internally to `D'` (`octahedron`):
given triangles `(X, Y, Q₁, f, p₁, d₁)`, `(X, Z, Q₂, g ∘ f, p₂, d₂)` and
`(Y, Z, Q₃, g, p₃, d₃)` of `T'`, there are morphisms `a : Q₁ ⟶ Q₂` and `b : Q₂ ⟶ Q₃` of `D'`
such that `(Q₁, Q₂, Q₃, a, b, p₁[1] ∘ d₃)` lies in `T'`, `(id_X, g, a)` is a morphism of
triangles from the first to the second triangle, and `(f, id_Z, b)` is a morphism of
triangles from the second to the third. -/
@[stacks 05QM "Triangulated subcategory; TR4 for `(D', [ ], T')` is stated internally to
`D'`."]
structure TriangulatedSubcategory [IsTriangulated D] extends PretriangulatedSubcategory D where
  /-- TR4 for `(D', [ ], T')`. -/
  octahedron : ∀ {X Y Z Q₁ Q₂ Q₃ : D} {f : X ⟶ Y} {g : Y ⟶ Z} {p₁ : Y ⟶ Q₁}
    {d₁ : Q₁ ⟶ X⟦(1 : ℤ)⟧} {p₂ : Z ⟶ Q₂} {d₂ : Q₂ ⟶ X⟦(1 : ℤ)⟧} {p₃ : Z ⟶ Q₃}
    {d₃ : Q₃ ⟶ Y⟦(1 : ℤ)⟧}, Triangle.mk f p₁ d₁ ∈ triangles →
      Triangle.mk (f ≫ g) p₂ d₂ ∈ triangles → Triangle.mk g p₃ d₃ ∈ triangles →
        ∃ (a : Q₁ ⟶ Q₂) (b : Q₂ ⟶ Q₃), hom a ∧ hom b ∧
          Triangle.mk a b (d₃ ≫ p₁⟦(1 : ℤ)⟧') ∈ triangles ∧
          p₁ ≫ a = g ≫ p₂ ∧ d₁ = a ≫ d₂ ∧
          p₂ ≫ b = p₃ ∧ d₂ ≫ f⟦(1 : ℤ)⟧' = b ≫ d₃

namespace AdditiveSubcategory

variable {D}

/-- The whole category `D`, as an additive subcategory of itself. -/
@[simps]
def top : AdditiveSubcategory D where
  obj := ⊤
  hom := ⊤
  obj_src _ := trivial
  obj_tgt _ := trivial
  id_mem _ := trivial
  comp_mem _ _ := trivial
  zero_mem _ _ := trivial
  add_mem _ _ := trivial
  neg_mem _ := trivial
  exists_isZero := ⟨0, trivial, isZero_zero D⟩
  exists_bicone {X Y} _ _ := ⟨_, ⟨BinaryBiproduct.isBilimit X Y⟩, trivial, trivial, trivial,
    trivial, trivial⟩

lemma isTriangle_top (T : Triangle D) : top.IsTriangle T :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

lemma isTriangleHom_top {T₁ T₂ : Triangle D} (φ : T₁ ⟶ T₂) : top.IsTriangleHom φ :=
  ⟨trivial, trivial, trivial⟩

instance : (top.restrict (shiftFunctor D (1 : ℤ)) (fun _ => trivial)
    (fun _ => trivial)).IsEquivalence where
  faithful.map_injective {X Y} f g h :=
    hom_ext ((shiftFunctor D (1 : ℤ)).map_injective (congrArg Subtype.val h))
  full.map_surjective {X Y} f := ⟨⟨(shiftFunctor D (1 : ℤ)).preimage f.1, trivial⟩,
    hom_ext ((shiftFunctor D (1 : ℤ)).map_preimage f.1)⟩
  essSurj.mem_essImage Y := by
    let e := (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by omega)).app Y.obj
    exact ⟨⟨Y.obj⟦(-1 : ℤ)⟧, trivial⟩, ⟨⟨e.hom, trivial⟩, ⟨e.inv, trivial⟩,
      hom_ext e.hom_inv_id, hom_ext e.inv_hom_id⟩⟩

end AdditiveSubcategory

open AdditiveSubcategory in
/-- The pre-triangulated category `(D, T)` is a pre-triangulated subcategory of itself. -/
def PretriangulatedSubcategory.top : PretriangulatedSubcategory D where
  toAdditiveSubcategory := AdditiveSubcategory.top
  shift_obj _ := trivial
  shift_hom _ := trivial
  isEquivalence_shift := inferInstance
  triangles := distTriang D
  triangles_subset := le_rfl
  isTriangle_of_mem T _ := isTriangle_top T
  isomorphic_mem _ h₁ _ _ e _ _ := isomorphic_distinguished _ h₁ _ e
  contractible_mem {X Z} _ _ hZ := by
    refine isomorphic_distinguished _ (contractible_distinguished X) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (hZ.iso (isZero_zero D))
      (by rfl) ((isZero_zero D).eq_of_tgt _ _) (hZ.eq_of_src _ _)
  exists_mem {_ _ f} _ := distinguished_cocone_triangle f
  rotate_mem_iff T _ := rotate_distinguished_triangle T
  complete T₁ h₁ T₂ h₂ a b _ _ comm := by
    obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism T₁ T₂ h₁ h₂ a b comm
    exact ⟨c, trivial, hc₁, hc₂⟩

/-- The triangulated category `(D, T)` is a triangulated subcategory of itself. -/
def TriangulatedSubcategory.top [IsTriangulated D] : TriangulatedSubcategory D where
  toPretriangulatedSubcategory := PretriangulatedSubcategory.top D
  octahedron {X Y Z Q₁ Q₂ Q₃ f g p₁ d₁ p₂ d₂ p₃ d₃} h₁ h₂ h₃ := by
    let o := Triangulated.someOctahedron rfl h₁ h₃ h₂
    exact ⟨o.m₁, o.m₃, trivial, trivial, o.mem, o.comm₁, o.comm₂.symm, o.comm₃, o.comm₄⟩

end CategoryTheory.Pretriangulated
