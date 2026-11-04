module

public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Simplicial objects as towers of truncated simplicial objects

A simplicial object of `C` is a functor `SimplexCategoryᵒᵖ ⥤ C`, while an `n`-truncated simplicial
object is a functor `(SimplexCategory.Truncated n)ᵒᵖ ⥤ C`, where `SimplexCategory.Truncated n` is
the full subcategory of `SimplexCategory` on the objects `⦋m⦌` with `m ≤ n`. Every object of
`SimplexCategory` lies in `SimplexCategory.Truncated n` for `n` its length, and the truncated
categories are nested, so a simplicial object is nothing more than a compatible family of
`n`-truncated simplicial objects, one for each `n`. This file makes that precise and, above all,
provides the direction that is actually used: *from* a compatible family *to* a simplicial object.

Mathlib has `CategoryTheory.SimplicialObject.truncation n` and
`CategoryTheory.SimplicialObject.Truncated.trunc`, together with the skeleton and coskeleton
adjunctions `skAdj` and `coskAdj`, but nothing relating a simplicial object to the *whole* family
of its truncations. The obstacle is that `SimplicialObject.Truncated C n` is a different category
for each `n`, so the compatibility between consecutive stages is a statement about objects of two
different categories.

## Main definitions

* `CategoryTheory.SimplicialObject.TruncatedTower`: a family `level n : Truncated C n` together
  with an equality identifying the `n`-truncation of `level (n + 1)` with `level n`.
* `CategoryTheory.SimplicialObject.TruncatedTower.assemble`: the simplicial object assembled from
  such a tower.
* `CategoryTheory.SimplicialObject.TruncatedTower.of`: the tower of truncations of a simplicial
  object.
* `CategoryTheory.SimplicialObject.TruncatedTower.ofStep`: a tower built by recursion on the
  truncation level, from a rule extending each stage to the next.
* `CategoryTheory.SimplicialObject.TruncatedIsoTower`: the same data with the compatibility
  weakened from an equality to an isomorphism, together with `assemble` and `truncationObjIso`
  for it.

## Main results

* `CategoryTheory.SimplicialObject.TruncatedTower.truncation_obj_assemble`: the `n`-truncation of
  `X.assemble` is `X.level n`, on the nose.
* `CategoryTheory.SimplicialObject.TruncatedTower.equivSimplicialObject`: towers and simplicial
  objects are in bijection; this is the object-level form of
  `SimplicialObject C ≃ lim_n SimplicialObject.Truncated C n`.
* `CategoryTheory.SimplicialObject.TruncatedTower.exists_simplicialObject_of_step`: if a property
  of truncated simplicial objects holds in degree `0` and can always be propagated along a
  one-step extension, then some simplicial object has that property at every truncation level.
  This is the form in which the construction is used to build a simplicial object by induction on
  the truncation level.
* `CategoryTheory.SimplicialObject.TruncatedTower.hom_ext`: a morphism of simplicial objects is
  determined by its truncations.
* `CategoryTheory.SimplicialObject.TruncatedIsoTower.exists_simplicialObject_of_step`: the same
  induction principle when the one-step extension only restricts to the previous stage up to
  isomorphism, for a property that is invariant under isomorphism.

## Implementation notes

The construction is forced to be degreewise. The object of `X.assemble` in degree `a` is read off
the stage `level a.len` at the minimal level where `a` lives, and a morphism `a ⟶ b` is read off
any single stage `level n` with `n` above both lengths; `mapAt_eq` says the result does not depend
on that choice, which is what makes `assemble` functorial. Taking `n = a.len ⊔ b.len` for the
definition and then transporting with `mapAt_eq` is cheaper than trying to fix one global level.

Two things make this work and are worth recording, since both are definitional rather than
proved. First, restriction along `SimplexCategory.Truncated.incl` and
`SimplexCategory.Truncated.inclusion` only changes the proof component of a
`ObjectProperty.FullSubcategory` object, so `((Truncated.trunc C n m h).obj Y).obj (op ⟨a, ha⟩)`
is *definitionally* `Y.obj (op ⟨a, ha'⟩)`, and likewise on morphisms; proof irrelevance does the
rest. Second, `Truncated.trunc` is definitionally transitive and definitionally the identity at
`n = n`. So the only genuine transport in the strict version is along the equality of functors
supplied by the tower, handled once in `mapAt_eq_of_le` via `Functor.congr_hom`.

The isomorphism-compatible version `TruncatedIsoTower` cannot use `Functor.congr_hom`, and the
same information has to be carried by a coherent family of comparison isomorphisms `levelIsoLe`,
built with `Nat.leRec`. Those are stated and used only through their *components* `levelHomLe`,
whose types are ascribed in the unrestricted spelling `(X.level n).obj (op ⟨a, _⟩)`: an iso-level
rewrite produces a term that is well typed but not type-correct at `implicit` transparency, after
which `rw` and `simp` both refuse. The two versions are related by `TruncatedTower.toIsoTower`,
but the strict one is kept because the equality `truncation_obj_assemble` and hence
`equivSimplicialObject` are genuinely stronger than anything the iso version can state.

No universe is narrowed: `C : Type u` with `[Category.{v} C]` throughout, as in
`Mathlib.AlgebraicTopology.SimplicialObject.Basic`.

## References

The Stacks project's chapter on simplicial methods defines truncated simplicial objects in
[Stacks, Tag 0180](https://stacks.math.columbia.edu/tag/0180) and develops the skeleton and
coskeleton functors, but states no result identifying a simplicial object with the family of all
of its truncations; nothing here carries a Stacks tag. The closest statement,
[Stacks, Tag 018A](https://stacks.math.columbia.edu/tag/018A), is a different one -- it produces
the untruncated object as a pointwise right Kan extension from one-step extendability -- and is
already available in this library.
-/

@[expose] public section

open CategoryTheory Opposite SimplexCategory

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : a ⟶ b` of `SimplexCategoryᵒᵖ` between objects of length at most `n`, read as a
morphism of `(SimplexCategory.Truncated n)ᵒᵖ`. -/
abbrev homAt {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ)
    (ha : a.unop.len ≤ n) (hb : b.unop.len ≤ n) :
    (op ⟨a.unop, ha⟩ : (SimplexCategory.Truncated n)ᵒᵖ) ⟶ op ⟨b.unop, hb⟩ :=
  Quiver.Hom.op (ObjectProperty.homMk (X := ⟨b.unop, hb⟩) (Y := ⟨a.unop, ha⟩) f.unop)

/-- Choosing one-step extensions recursively gives a family of truncated simplicial objects, all
satisfying `P`, in which each stage is related by `R` to the previous one. -/
private theorem exists_family_of_step {P : (n : ℕ) → SimplicialObject.Truncated C n → Prop}
    {R : (n : ℕ) → SimplicialObject.Truncated C (n + 1) → SimplicialObject.Truncated C n → Prop}
    (x₀ : SimplicialObject.Truncated C 0) (hx₀ : P 0 x₀)
    (step : ∀ (n : ℕ) (Y : SimplicialObject.Truncated C n), P n Y →
      ∃ Z : SimplicialObject.Truncated C (n + 1), R n Z Y ∧ P (n + 1) Z) :
    ∃ L : (n : ℕ) → SimplicialObject.Truncated C n,
      (∀ n, P n (L n)) ∧ ∀ n, R n (L (n + 1)) (L n) := by
  choose Z hZ hZP using step
  let L : (n : ℕ) → { Y : SimplicialObject.Truncated C n // P n Y } :=
    Nat.rec (motive := fun n => { Y : SimplicialObject.Truncated C n // P n Y }) ⟨x₀, hx₀⟩
      fun n Y => ⟨Z n Y.1 Y.2, hZP n Y.1 Y.2⟩
  exact ⟨fun n => (L n).1, fun n => (L n).2, fun n => hZ n (L n).1 (L n).2⟩

/-- A tower of truncated simplicial objects of `C`: an `n`-truncated simplicial object for every
`n`, each one the `n`-truncation of the next. -/
structure TruncatedTower (C : Type u) [Category.{v} C] where
  /-- The `n`-th stage of the tower. -/
  level (n : ℕ) : SimplicialObject.Truncated C n
  /-- The `n`-truncation of the `(n + 1)`-st stage is the `n`-th stage. -/
  trunc_level_succ (n : ℕ) :
    (Truncated.trunc C (n + 1) n).obj (level (n + 1)) = level n

namespace TruncatedTower

variable (X : TruncatedTower C)

/-- Any stage of the tower restricts to any lower stage. -/
theorem trunc_level {m n : ℕ} (h : m ≤ n) :
    (Truncated.trunc C n m h).obj (X.level n) = X.level m := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [show (Truncated.trunc C (n + 1) m (hn.trans (Nat.le_succ n))).obj (X.level (n + 1))
            = (Truncated.trunc C n m hn).obj
                ((Truncated.trunc C (n + 1) n (Nat.le_succ n)).obj (X.level (n + 1))) from rfl,
        X.trunc_level_succ n, ih]

/-- The object of the assembled simplicial object in degree `a`, read off the stage of the tower
at the length of `a`. -/
def pt (a : SimplexCategoryᵒᵖ) : C := (X.level a.unop.len).obj (op ⟨a.unop, le_rfl⟩)

/-- Every stage above the length of `a` computes `X.pt a`. -/
theorem level_obj_eq {a : SimplexCategoryᵒᵖ} {n : ℕ} (h : a.unop.len ≤ n) :
    (X.level n).obj (op ⟨a.unop, h⟩) = X.pt a :=
  Functor.congr_obj (X.trunc_level h) (op ⟨a.unop, le_rfl⟩)

/-- The action of the assembled simplicial object on a morphism, read off the stage `level n`. -/
def mapAt {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ)
    (ha : a.unop.len ≤ n) (hb : b.unop.len ≤ n) : X.pt a ⟶ X.pt b :=
  eqToHom (X.level_obj_eq ha).symm ≫ (X.level n).map (homAt f n ha hb) ≫
    eqToHom (X.level_obj_eq hb)

/-- Passing to a higher stage of the tower does not change `mapAt`. -/
theorem mapAt_eq_of_le {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) {m n : ℕ} (hmn : m ≤ n)
    (ha : a.unop.len ≤ m) (hb : b.unop.len ≤ m)
    (ha' : a.unop.len ≤ n) (hb' : b.unop.len ≤ n) :
    X.mapAt f n ha' hb' = X.mapAt f m ha hb := by
  have e₁ : (X.level n).obj (op (⟨a.unop, ha'⟩ : SimplexCategory.Truncated n))
      = (X.level m).obj (op (⟨a.unop, ha⟩ : SimplexCategory.Truncated m)) :=
    Functor.congr_obj (X.trunc_level hmn) (op ⟨a.unop, ha⟩)
  have e₂ : (X.level n).obj (op (⟨b.unop, hb'⟩ : SimplexCategory.Truncated n))
      = (X.level m).obj (op (⟨b.unop, hb⟩ : SimplexCategory.Truncated m)) :=
    Functor.congr_obj (X.trunc_level hmn) (op ⟨b.unop, hb⟩)
  have key : (X.level n).map (homAt f n ha' hb')
      = eqToHom e₁ ≫ (X.level m).map (homAt f m ha hb) ≫ eqToHom e₂.symm :=
    Functor.congr_hom (X.trunc_level hmn) (homAt f m ha hb)
  rw [mapAt, mapAt, key]
  simp

/-- `mapAt` does not depend on the chosen stage of the tower. -/
theorem mapAt_eq {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) {m n : ℕ}
    (ha : a.unop.len ≤ m) (hb : b.unop.len ≤ m)
    (ha' : a.unop.len ≤ n) (hb' : b.unop.len ≤ n) :
    X.mapAt f m ha hb = X.mapAt f n ha' hb' := by
  rw [X.mapAt_eq_of_le f (sup_le ha hb) le_sup_left le_sup_right ha hb,
    X.mapAt_eq_of_le f (sup_le ha' hb') le_sup_left le_sup_right ha' hb']

/-- `mapAt` sends the identity of `a` to the identity of `X.pt a`. -/
@[simp]
theorem mapAt_id (a : SimplexCategoryᵒᵖ) (n : ℕ) (ha : a.unop.len ≤ n) :
    X.mapAt (𝟙 a) n ha ha = 𝟙 (X.pt a) := by
  simp [mapAt, homAt]

/-- `mapAt` sends a composite to the composite of the images. -/
theorem mapAt_comp {a b c : SimplexCategoryᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (n : ℕ)
    (ha : a.unop.len ≤ n) (hb : b.unop.len ≤ n) (hc : c.unop.len ≤ n) :
    X.mapAt (f ≫ g) n ha hc = X.mapAt f n ha hb ≫ X.mapAt g n hb hc := by
  rw [mapAt, mapAt, mapAt,
    show homAt (f ≫ g) n ha hc = homAt f n ha hb ≫ homAt g n hb hc from rfl]
  simp

/-- The simplicial object assembled from a tower of truncated simplicial objects. -/
@[simps obj]
def assemble : SimplicialObject C where
  obj a := X.pt a
  map {a b} f := X.mapAt f (a.unop.len ⊔ b.unop.len) le_sup_left le_sup_right
  map_id a := by
    rw [X.mapAt_eq (𝟙 a) le_sup_left le_sup_right le_rfl le_rfl, X.mapAt_id]
  map_comp {a b c} f g := by
    rw [X.mapAt_eq (f ≫ g) le_sup_left le_sup_right
        (le_sup_of_le_left (le_sup_left (b := b.unop.len)))
        (le_sup_right (a := a.unop.len ⊔ b.unop.len)),
      X.mapAt_eq f le_sup_left le_sup_right
        (le_sup_of_le_left (le_sup_left (b := b.unop.len)))
        (le_sup_of_le_left (le_sup_right (a := a.unop.len))),
      X.mapAt_eq g le_sup_left le_sup_right
        (le_sup_of_le_left (le_sup_right (a := a.unop.len)))
        (le_sup_right (a := a.unop.len ⊔ b.unop.len)),
      X.mapAt_comp]

/-- The action of the assembled simplicial object on `f` may be read off any stage `n` above the
lengths of its source and target. -/
theorem assemble_map {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ)
    (ha : a.unop.len ≤ n) (hb : b.unop.len ≤ n) :
    X.assemble.map f = X.mapAt f n ha hb :=
  X.mapAt_eq f le_sup_left le_sup_right ha hb

/-- The `n`-truncation of the assembled simplicial object is the `n`-th stage of the tower. -/
theorem truncation_obj_assemble (n : ℕ) :
    (truncation n).obj X.assemble = X.level n := by
  refine Functor.ext (fun a => (X.level_obj_eq (a := op a.unop.obj) a.unop.property).symm)
    (fun a b u => ?_)
  rw [show ((truncation n).obj X.assemble).map u
      = X.assemble.map (Quiver.Hom.op u.unop.hom) from rfl,
    X.assemble_map _ n a.unop.property b.unop.property, mapAt]
  rfl

/-- The tower of all truncations of a simplicial object. -/
@[simps]
def of (Y : SimplicialObject C) : TruncatedTower C where
  level n := (truncation n).obj Y
  trunc_level_succ _ := rfl

/-- Assembling the tower of truncations of `Y` gives `Y` back. -/
theorem assemble_of (Y : SimplicialObject C) : (of Y).assemble = Y :=
  Functor.ext (fun _ => rfl) (fun a b f => by
    rw [(of Y).assemble_map f (a.unop.len ⊔ b.unop.len) le_sup_left le_sup_right, mapAt]
    rfl)

/-- Two towers with the same stages are equal. -/
@[ext]
theorem ext {X Y : TruncatedTower C} (h : ∀ n, X.level n = Y.level n) : X = Y := by
  cases X; cases Y; simp only [mk.injEq]; exact funext h

/-- Towers of truncated simplicial objects are the same thing as simplicial objects. This is the
object-level statement that `SimplicialObject C` is the limit of the categories
`SimplicialObject.Truncated C n`. -/
def equivSimplicialObject : TruncatedTower C ≃ SimplicialObject C where
  toFun X := X.assemble
  invFun Y := of Y
  left_inv X := ext (fun n => X.truncation_obj_assemble n)
  right_inv Y := assemble_of Y

/-- A tower built by recursion on the truncation level: a `0`-truncated simplicial object together
with a rule extending any `n`-truncated stage to an `(n + 1)`-truncated one restricting to it. -/
def ofStep (x₀ : SimplicialObject.Truncated C 0)
    (step : (n : ℕ) → (Y : SimplicialObject.Truncated C n) →
      { Z : SimplicialObject.Truncated C (n + 1) //
        (Truncated.trunc C (n + 1) n).obj Z = Y }) :
    TruncatedTower C where
  level := Nat.rec (motive := fun n => SimplicialObject.Truncated C n) x₀
    fun n Y => (step n Y).1
  trunc_level_succ n := (step n _).2

/-- Building a simplicial object by induction on the truncation level: a property of truncated
simplicial objects that holds in degree `0` and can always be propagated along a one-step
extension holds at every truncation level of some simplicial object. -/
theorem exists_simplicialObject_of_step {P : (n : ℕ) → SimplicialObject.Truncated C n → Prop}
    (x₀ : SimplicialObject.Truncated C 0) (hx₀ : P 0 x₀)
    (step : ∀ (n : ℕ) (Y : SimplicialObject.Truncated C n), P n Y →
      ∃ Z : SimplicialObject.Truncated C (n + 1),
        (Truncated.trunc C (n + 1) n).obj Z = Y ∧ P (n + 1) Z) :
    ∃ K : SimplicialObject C, ∀ n, P n ((truncation n).obj K) := by
  obtain ⟨L, hL, hR⟩ := exists_family_of_step
    (R := fun n Z Y => (Truncated.trunc C (n + 1) n).obj Z = Y) x₀ hx₀ step
  refine ⟨(TruncatedTower.mk L hR).assemble, fun n => ?_⟩
  rw [truncation_obj_assemble]
  exact hL n

/-- A morphism of simplicial objects is determined by its truncations. -/
theorem hom_ext {Y Z : SimplicialObject C} {f g : Y ⟶ Z}
    (h : ∀ n, (truncation n).map f = (truncation n).map g) : f = g := by
  ext a
  exact congrArg (fun t => NatTrans.app t (op ⟨a.unop, le_rfl⟩)) (h a.unop.len)

end TruncatedTower

/-- A tower of truncated simplicial objects of `C` in which each stage is identified with the
truncation of the next only up to isomorphism. -/
structure TruncatedIsoTower (C : Type u) [Category.{v} C] where
  /-- The `n`-th stage of the tower. -/
  level (n : ℕ) : SimplicialObject.Truncated C n
  /-- The `n`-truncation of the `(n + 1)`-st stage is isomorphic to the `n`-th stage. -/
  levelIso (n : ℕ) : (Truncated.trunc C (n + 1) n).obj (level (n + 1)) ≅ level n

/-- A tower whose stages agree on the nose is in particular one whose stages agree up to
isomorphism. -/
@[simps]
def TruncatedTower.toIsoTower (T : TruncatedTower C) : TruncatedIsoTower C where
  level := T.level
  levelIso n := CategoryTheory.eqToIso (T.trunc_level_succ n)

namespace TruncatedIsoTower

variable (X : TruncatedIsoTower C)

/-- The comparison isomorphism from any stage of the tower down to any lower stage, obtained by
composing the one-step isomorphisms. -/
def levelIsoLe {m : ℕ} : {n : ℕ} → (h : m ≤ n) →
    ((Truncated.trunc C n m h).obj (X.level n) ≅ X.level m) :=
  Nat.leRec (motive := fun n h => (Truncated.trunc C n m h).obj (X.level n) ≅ X.level m)
    (Iso.refl _)
    (fun {k} h ih => (Truncated.trunc C k m h).mapIso (X.levelIso k) ≪≫ ih)

/-- The comparison isomorphism from a stage to itself is the identity. -/
theorem levelIsoLe_self (m : ℕ) : X.levelIsoLe (le_refl m) = Iso.refl _ :=
  Nat.leRec_self _ _

/-- The comparison isomorphism from stage `k + 1` down to stage `m` is the one-step isomorphism
`levelIso k` followed by the comparison isomorphism from stage `k` down to stage `m`. -/
theorem levelIsoLe_succ {m k : ℕ} (h : m ≤ k) (h' : m ≤ k + 1) :
    X.levelIsoLe h' = (Truncated.trunc C k m h).mapIso (X.levelIso k) ≪≫ X.levelIsoLe h :=
  Nat.leRec_succ _ _ h

/-- The component of `levelIsoLe` at the object `a`, with its type spelled in the unrestricted
stages `X.level n` and `X.level m` rather than through `Truncated.trunc`. -/
def levelHomLe {m n : ℕ} (h : m ≤ n) (a : SimplexCategory) (ha : a.len ≤ m) :
    (X.level n).obj (op ⟨a, ha.trans h⟩) ⟶ (X.level m).obj (op ⟨a, ha⟩) :=
  (X.levelIsoLe h).hom.app (op ⟨a, ha⟩)

/-- The comparison morphism from a stage to itself is the identity. -/
@[simp]
theorem levelHomLe_self {m : ℕ} (a : SimplexCategory) (ha : a.len ≤ m) :
    X.levelHomLe (le_refl m) a ha = 𝟙 _ :=
  congrArg
    (fun e : (Truncated.trunc C m m (le_refl m)).obj (X.level m) ≅ X.level m =>
      e.hom.app (op ⟨a, ha⟩))
    (X.levelIsoLe_self m)

/-- The component of the one-step isomorphism `levelIso n` at the object `a`, with its type
spelled in the unrestricted stage `X.level (n + 1)`. -/
def levelIsoHom (n : ℕ) (a : SimplexCategory) (ha : a.len ≤ n) :
    (X.level (n + 1)).obj (op ⟨a, ha.trans (Nat.le_succ n)⟩) ⟶ (X.level n).obj (op ⟨a, ha⟩) :=
  (X.levelIso n).hom.app (op ⟨a, ha⟩)

/-- The comparison morphism from stage `k + 1` down to stage `m` is the component of `levelIso k`
followed by the comparison morphism from stage `k` down to stage `m`. -/
theorem levelHomLe_succ {m k : ℕ} (h : m ≤ k) (h' : m ≤ k + 1) (a : SimplexCategory)
    (ha : a.len ≤ m) :
    X.levelHomLe h' a ha
      = X.levelIsoHom k a (ha.trans h) ≫ X.levelHomLe h a ha :=
  congrArg
    (fun e : (Truncated.trunc C (k + 1) m h').obj (X.level (k + 1)) ≅ X.level m =>
      e.hom.app (op ⟨a, ha⟩))
    (X.levelIsoLe_succ h h')

/-- The comparison morphisms are coherent: going down from `n` to `m` and then from `m` to `k` is
going down from `n` to `k`. -/
theorem levelHomLe_comp {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (hkn : k ≤ n)
    (a : SimplexCategory) (hk : a.len ≤ k) :
    X.levelHomLe hmn a (hk.trans hkm) ≫ X.levelHomLe hkm a hk
      = X.levelHomLe hkn a hk := by
  induction n, hmn using Nat.le_induction with
  | base => rw [X.levelHomLe_self, Category.id_comp]
  | succ n hn ih =>
      rw [X.levelHomLe_succ hn (Nat.le_succ_of_le hn) a (hk.trans hkm),
        X.levelHomLe_succ (hkm.trans hn) hkn a hk, Category.assoc, ih (hkm.trans hn)]

/-- The object of the assembled simplicial object in degree `a`, read off the stage of the tower
at the length of `a`. -/
def pt (a : SimplexCategoryᵒᵖ) : C := (X.level a.unop.len).obj (op ⟨a.unop, le_rfl⟩)

/-- The comparison isomorphism from any stage above the length of `a` to `X.pt a`. -/
def ptIso {a : SimplexCategoryᵒᵖ} {n : ℕ} (h : a.unop.len ≤ n) :
    (X.level n).obj (op ⟨a.unop, h⟩) ≅ X.pt a :=
  (X.levelIsoLe h).app (op ⟨a.unop, le_rfl⟩)

/-- The forward map of `ptIso h` is the comparison morphism `levelHomLe h` at `a.unop`. -/
theorem ptIso_hom {a : SimplexCategoryᵒᵖ} {n : ℕ} (h : a.unop.len ≤ n) :
    (X.ptIso h).hom = X.levelHomLe h a.unop le_rfl := rfl

/-- The comparison isomorphisms to `X.pt a` are compatible with passing to a higher stage. -/
theorem ptIso_hom_eq {a : SimplexCategoryᵒᵖ} {m n : ℕ} (hmn : m ≤ n)
    (ha : a.unop.len ≤ m) (ha' : a.unop.len ≤ n) :
    (X.ptIso ha').hom = X.levelHomLe hmn a.unop ha ≫ (X.ptIso ha).hom := by
  rw [ptIso_hom, ptIso_hom, ← X.levelHomLe_comp ha hmn ha' a.unop le_rfl]
  rfl

/-- The action of the assembled simplicial object on a morphism, read off the stage `level n`. -/
def mapAt {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ)
    (ha : a.unop.len ≤ n) (hb : b.unop.len ≤ n) : X.pt a ⟶ X.pt b :=
  (X.ptIso ha).inv ≫ (X.level n).map (homAt f n ha hb) ≫ (X.ptIso hb).hom

/-- Passing to a higher stage of the tower does not change `mapAt`. -/
theorem mapAt_eq_of_le {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) {m n : ℕ} (hmn : m ≤ n)
    (ha : a.unop.len ≤ m) (hb : b.unop.len ≤ m)
    (ha' : a.unop.len ≤ n) (hb' : b.unop.len ≤ n) :
    X.mapAt f n ha' hb' = X.mapAt f m ha hb := by
  have hnat : (X.level n).map (homAt f n ha' hb') ≫ X.levelHomLe hmn b.unop hb
      = X.levelHomLe hmn a.unop ha ≫ (X.level m).map (homAt f m ha hb) :=
    (X.levelIsoLe hmn).hom.naturality (homAt f m ha hb)
  rw [mapAt, mapAt, Iso.inv_comp_eq, X.ptIso_hom_eq hmn ha ha', X.ptIso_hom_eq hmn hb hb']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  conv_lhs => rw [← Category.assoc, hnat]
  rw [Category.assoc]

/-- `mapAt` does not depend on the chosen stage of the tower. -/
theorem mapAt_eq {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) {m n : ℕ}
    (ha : a.unop.len ≤ m) (hb : b.unop.len ≤ m)
    (ha' : a.unop.len ≤ n) (hb' : b.unop.len ≤ n) :
    X.mapAt f m ha hb = X.mapAt f n ha' hb' := by
  rw [X.mapAt_eq_of_le f (sup_le ha hb) le_sup_left le_sup_right ha hb,
    X.mapAt_eq_of_le f (sup_le ha' hb') le_sup_left le_sup_right ha' hb']

/-- `mapAt` sends the identity of `a` to the identity of `X.pt a`. -/
@[simp]
theorem mapAt_id (a : SimplexCategoryᵒᵖ) (n : ℕ) (ha : a.unop.len ≤ n) :
    X.mapAt (𝟙 a) n ha ha = 𝟙 (X.pt a) := by
  simp [mapAt, homAt]

/-- `mapAt` sends a composite to the composite of the images. -/
theorem mapAt_comp {a b c : SimplexCategoryᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (n : ℕ)
    (ha : a.unop.len ≤ n) (hb : b.unop.len ≤ n) (hc : c.unop.len ≤ n) :
    X.mapAt (f ≫ g) n ha hc = X.mapAt f n ha hb ≫ X.mapAt g n hb hc := by
  rw [mapAt, mapAt, mapAt,
    show homAt (f ≫ g) n ha hc = homAt f n ha hb ≫ homAt g n hb hc from rfl]
  simp

/-- The simplicial object assembled from a tower whose stages agree up to isomorphism. -/
@[simps obj]
def assemble : SimplicialObject C where
  obj a := X.pt a
  map {a b} f := X.mapAt f (a.unop.len ⊔ b.unop.len) le_sup_left le_sup_right
  map_id a := by
    rw [X.mapAt_eq (𝟙 a) le_sup_left le_sup_right le_rfl le_rfl, X.mapAt_id]
  map_comp {a b c} f g := by
    rw [X.mapAt_eq (f ≫ g) le_sup_left le_sup_right
        (le_sup_of_le_left (le_sup_left (b := b.unop.len)))
        (le_sup_right (a := a.unop.len ⊔ b.unop.len)),
      X.mapAt_eq f le_sup_left le_sup_right
        (le_sup_of_le_left (le_sup_left (b := b.unop.len)))
        (le_sup_of_le_left (le_sup_right (a := a.unop.len))),
      X.mapAt_eq g le_sup_left le_sup_right
        (le_sup_of_le_left (le_sup_right (a := a.unop.len)))
        (le_sup_right (a := a.unop.len ⊔ b.unop.len)),
      X.mapAt_comp]

/-- The action of the assembled simplicial object on `f` may be read off any stage `n` above the
lengths of its source and target. -/
theorem assemble_map {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ)
    (ha : a.unop.len ≤ n) (hb : b.unop.len ≤ n) :
    X.assemble.map f = X.mapAt f n ha hb :=
  X.mapAt_eq f le_sup_left le_sup_right ha hb

/-- The `n`-th stage of the tower is isomorphic to the `n`-truncation of the assembled simplicial
object. -/
def levelIsoTruncationObjAssemble (n : ℕ) : X.level n ≅ (truncation n).obj X.assemble :=
  NatIso.ofComponents (fun a => X.ptIso (a := op a.unop.obj) a.unop.property)
    (fun {a b} u => by
      change (X.level n).map u ≫ (X.ptIso (a := op b.unop.obj) b.unop.property).hom
          = (X.ptIso (a := op a.unop.obj) a.unop.property).hom
            ≫ X.mapAt (Quiver.Hom.op u.unop.hom) (a.unop.obj.len ⊔ b.unop.obj.len)
              le_sup_left le_sup_right
      rw [X.mapAt_eq (Quiver.Hom.op u.unop.hom) le_sup_left le_sup_right
        a.unop.property b.unop.property, mapAt, Iso.hom_inv_id_assoc]
      rfl)

/-- The `n`-truncation of the assembled simplicial object is isomorphic to the `n`-th stage of the
tower. -/
def truncationObjAssembleIso (n : ℕ) : (truncation n).obj X.assemble ≅ X.level n :=
  (X.levelIsoTruncationObjAssemble n).symm

/-- Building a simplicial object by induction on the truncation level, when the one-step extension
only restricts to the previous stage up to isomorphism. The property being propagated has to be
invariant under isomorphism of truncated simplicial objects. -/
theorem exists_simplicialObject_of_step {P : (n : ℕ) → SimplicialObject.Truncated C n → Prop}
    (hP : ∀ (n : ℕ) (Y Z : SimplicialObject.Truncated C n), (Y ≅ Z) → P n Y → P n Z)
    (x₀ : SimplicialObject.Truncated C 0) (hx₀ : P 0 x₀)
    (step : ∀ (n : ℕ) (Y : SimplicialObject.Truncated C n), P n Y →
      ∃ Z : SimplicialObject.Truncated C (n + 1),
        Nonempty ((Truncated.trunc C (n + 1) n).obj Z ≅ Y) ∧ P (n + 1) Z) :
    ∃ K : SimplicialObject C, ∀ n, P n ((truncation n).obj K) := by
  obtain ⟨L, hL, hR⟩ := exists_family_of_step
    (R := fun n Z Y => Nonempty ((Truncated.trunc C (n + 1) n).obj Z ≅ Y)) x₀ hx₀ step
  let T : TruncatedIsoTower C := TruncatedIsoTower.mk L fun n => (hR n).some
  exact ⟨T.assemble, fun n => hP n _ _ (T.levelIsoTruncationObjAssemble n) (hL n)⟩

end TruncatedIsoTower

end CategoryTheory.SimplicialObject
