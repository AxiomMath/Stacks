module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubi
public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidal
public import Mathlib.CategoryTheory.Monoidal.Transport
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual

/-!
# The twisted Karoubi envelope of a graded symmetric monoidal category

Let `C` be a category graded over a ring `R`, with a monoidal structure for which the tensor
product of homogeneous morphisms of degrees `r` and `s` is homogeneous of degree `r + s` and the
associativity and unit constraints are homogeneous of degree zero. Then the twisted Karoubi
envelope of `C`, whose objects are the triples `(X, p, m)`, is monoidal for

  `(X, p, m) ⊗ (Y, q, n) = (X ⊗ Y, p ⊗ q, m + n)`

with unit `(𝟙_ C, 𝟙, 0)`, and with the constraints of `C` cut down by the idempotents. If the
commutativity constraint of a braided (symmetric) `C` has degree zero too, the twisted Karoubi
envelope is braided (symmetric) for the commutativity constraint of `C` cut down by the
idempotents.

Applied to the graded category of correspondences between smooth projective schemes over a field,
this is the symmetric monoidal structure on the category `M_k` of Chow motives (Stacks 0FGC).

## Main definitions

* `CategoryTheory.GradedCategory.IsGradedMonoidal`: tensor products of homogeneous morphisms are
  homogeneous of the sum of the degrees, and the associativity and unit constraints have degree
  zero.
* `CategoryTheory.GradedCategory.IsGradedBraided`: the commutativity constraint has degree zero.
* `CategoryTheory.GradedCategory.TwistedKaroubi.ofComm`: a homogeneous morphism of `C` of the
  right degree which intertwines two idempotents, as a morphism of triples.
* `CategoryTheory.GradedCategory.TwistedKaroubi.isoOfIso`: the same for an isomorphism of `C`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.forgetTwist`: the faithful functor
  `(X, p, m) ↦ (X, p)` to the Karoubi envelope, forgetting the twist.
* `CategoryTheory.GradedCategory.TwistedKaroubi.tensorUnitTwistIso`:
  `(X, p, n) ⊗ (𝟙_ C, 𝟙, m) ≅ (X, p, n + m)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTensorIso`:
  `(𝟙_ C, 𝟙, n) ⊗ (𝟙_ C, 𝟙, m) ≅ (𝟙_ C, 𝟙, n + m)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistHasInverse` and
  `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistExactPairing`: `(𝟙_ C, 𝟙, n)` is
  invertible with inverse `(𝟙_ C, 𝟙, n')` for `n + n' = 0`, and the two are dual.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.monoidalCategory`,
  `CategoryTheory.GradedCategory.TwistedKaroubi.braidedCategory` and
  `CategoryTheory.GradedCategory.TwistedKaroubi.symmetricCategory`: the monoidal, braided and
  symmetric structures.
* `CategoryTheory.GradedCategory.TwistedKaroubi.tensorObj_X`, `tensorObj_p`, `tensorObj_twist`,
  `tensorUnit_X`, `tensorUnit_p`, `tensorUnit_twist`, `associator_hom_val`, `braiding_hom_val`:
  the tensor product, the unit and the constraints are the stated ones.

## Implementation notes

Only the data are constructed by hand; the degree conditions are needed exactly there. The
coherence axioms are induced along the faithful functor `forgetTwist` to the Karoubi envelope of
`C`, which carries the symmetric monoidal structure of
`StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidal` and on which the tensor product and the
constraints are given by the same morphisms of `C` (`CategoryTheory.Monoidal.induced`,
`CategoryTheory.BraidedCategory.ofFaithful`, `CategoryTheory.SymmetricCategory.ofFaithful`).
The forgetful functor is thereby symmetric monoidal with identity comparison morphisms.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Idempotents

namespace CategoryTheory.GradedCategory

universe w v u

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- A monoidal structure on a graded category is *graded* when the tensor product of morphisms
homogeneous of degrees `m` and `n` is homogeneous of degree `m + n` and the associativity and unit
constraints, and their inverses, are homogeneous of degree zero. -/
class IsGradedMonoidal [MonoidalCategory C] : Prop where
  /-- Degrees add under the tensor product of morphisms. -/
  tensorHom_mem {X₁ Y₁ X₂ Y₂ : C} {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} {m n : ℤ} :
    f ∈ grade (R := R) X₁ Y₁ m → g ∈ grade (R := R) X₂ Y₂ n →
      f ⊗ₘ g ∈ grade (R := R) (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (m + n)
  /-- The associativity constraint has degree zero. -/
  associator_hom_mem (X Y Z : C) : (α_ X Y Z).hom ∈ grade (R := R) _ _ 0
  /-- The inverse associativity constraint has degree zero. -/
  associator_inv_mem (X Y Z : C) : (α_ X Y Z).inv ∈ grade (R := R) _ _ 0
  /-- The left unit constraint has degree zero. -/
  leftUnitor_hom_mem (X : C) : (λ_ X).hom ∈ grade (R := R) _ _ 0
  /-- The inverse left unit constraint has degree zero. -/
  leftUnitor_inv_mem (X : C) : (λ_ X).inv ∈ grade (R := R) _ _ 0
  /-- The right unit constraint has degree zero. -/
  rightUnitor_hom_mem (X : C) : (ρ_ X).hom ∈ grade (R := R) _ _ 0
  /-- The inverse right unit constraint has degree zero. -/
  rightUnitor_inv_mem (X : C) : (ρ_ X).inv ∈ grade (R := R) _ _ 0

/-- A braiding on a graded monoidal category is *graded* when the commutativity constraint and
its inverse are homogeneous of degree zero. -/
class IsGradedBraided [MonoidalCategory C] [BraidedCategory C] : Prop where
  /-- The commutativity constraint has degree zero. -/
  braiding_hom_mem (X Y : C) : (β_ X Y).hom ∈ grade (R := R) _ _ 0
  /-- The inverse commutativity constraint has degree zero. -/
  braiding_inv_mem (X Y : C) : (β_ X Y).inv ∈ grade (R := R) _ _ 0

namespace TwistedKaroubi

variable {R C}

/-- A morphism homogeneous of degree `i` is homogeneous of degree `j` when `i = j`. -/
theorem grade_cast {X Y : C} {a : X ⟶ Y} {i j : ℤ} (h : a ∈ grade (R := R) X Y i) (e : i = j) :
    a ∈ grade (R := R) X Y j :=
  e ▸ h

/-! ### Morphisms of triples from intertwining morphisms -/

section OfComm

/-- A homogeneous morphism `g : X ⟶ Y` of degree `n - m` intertwining `p` and `q` gives the
morphism `p ≫ g` of triples `(X, p, m) ⟶ (Y, q, n)`. -/
def ofComm {M N : TwistedKaroubi R C} (g : M.X ⟶ N.X)
    (hg : g ∈ grade (R := R) M.X N.X (N.twist - M.twist)) (h : M.p ≫ g = g ≫ N.p) : M ⟶ N :=
  Hom.mk (M.p ≫ g)
    ⟨by simpa using comp_mem (R := R) hg M.p_mem, by rw [← assoc, M.idem],
      by rw [assoc, ← h, ← assoc, M.idem]⟩

/-- The underlying morphism of `ofComm g hg h` is `p ≫ g`. -/
@[simp]
theorem ofComm_val {M N : TwistedKaroubi R C} (g : M.X ⟶ N.X)
    (hg : g ∈ grade (R := R) M.X N.X (N.twist - M.twist)) (h : M.p ≫ g = g ≫ N.p) :
    (ofComm g hg h).val = M.p ≫ g :=
  rfl

/-- Equal intertwining morphisms give equal morphisms of triples under `ofComm`. -/
theorem ofComm_congr {M N : TwistedKaroubi R C} {g g' : M.X ⟶ N.X}
    (hg : g ∈ grade (R := R) M.X N.X (N.twist - M.twist)) (h : M.p ≫ g = g ≫ N.p)
    (hg' : g' ∈ grade (R := R) M.X N.X (N.twist - M.twist)) (h' : M.p ≫ g' = g' ≫ N.p)
    (e : g = g') : ofComm g hg h = ofComm g' hg' h' := by
  subst e
  rfl

/-- Every morphism of triples is an `ofComm` of its underlying morphism. -/
theorem eq_ofComm {M N : TwistedKaroubi R C} (f : M ⟶ N) :
    f = ofComm f.val f.2.1 (by rw [f.2.2.1, f.2.2.2]) := by
  ext
  exact f.2.2.1.symm

/-- The composite of morphisms of degrees `n - m` and `l - n` has degree `l - m`. -/
theorem comp_mem' {M N P : TwistedKaroubi R C} {g : M.X ⟶ N.X} {g' : N.X ⟶ P.X}
    (hg : g ∈ grade (R := R) M.X N.X (N.twist - M.twist))
    (hg' : g' ∈ grade (R := R) N.X P.X (P.twist - N.twist)) :
    g ≫ g' ∈ grade (R := R) M.X P.X (P.twist - M.twist) :=
  grade_cast (comp_mem (R := R) hg' hg) (by omega)

/-- The composite of `ofComm g` and `ofComm g'` is `ofComm (g ≫ g')`. -/
theorem ofComm_comp {M N P : TwistedKaroubi R C} (g : M.X ⟶ N.X)
    (hg : g ∈ grade (R := R) M.X N.X (N.twist - M.twist)) (h : M.p ≫ g = g ≫ N.p)
    (g' : N.X ⟶ P.X) (hg' : g' ∈ grade (R := R) N.X P.X (P.twist - N.twist))
    (h' : N.p ≫ g' = g' ≫ P.p) :
    ofComm g hg h ≫ ofComm g' hg' h' =
      ofComm (g ≫ g') (comp_mem' hg hg') (by rw [← assoc, h, assoc, h', assoc]) := by
  ext
  simp only [comp_val, ofComm_val, assoc]
  rw [← assoc g N.p g', ← h, ← assoc, ← assoc, M.idem, assoc]

/-- The identity of a triple is `ofComm` of the identity of the underlying object. -/
theorem ofComm_id (M : TwistedKaroubi R C) :
    ofComm (𝟙 M.X) (grade_cast (id_mem (R := R) M.X) (sub_self M.twist).symm) (by simp) =
      𝟙 M := by
  ext
  simp

/-- An isomorphism of `C` whose two directions are homogeneous of the right degrees and which
intertwines the idempotents is an isomorphism of triples. -/
@[simps]
def isoOfIso {M N : TwistedKaroubi R C} (e : M.X ≅ N.X)
    (hhom : e.hom ∈ grade (R := R) M.X N.X (N.twist - M.twist))
    (hinv : e.inv ∈ grade (R := R) N.X M.X (M.twist - N.twist))
    (h : M.p ≫ e.hom = e.hom ≫ N.p) : M ≅ N where
  hom := ofComm e.hom hhom h
  inv := ofComm e.inv hinv (by rw [Iso.comp_inv_eq, assoc, h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [ofComm_comp, ← ofComm_id]
    exact ofComm_congr _ _ _ _ e.hom_inv_id
  inv_hom_id := by
    rw [ofComm_comp, ← ofComm_id]
    exact ofComm_congr _ _ _ _ e.inv_hom_id

end OfComm

/-! ### The forgetful functor to the Karoubi envelope -/

/-- The functor `(X, p, m) ↦ (X, p)` to the Karoubi envelope of `C`, forgetting the twist. -/
@[simps]
def forgetTwist : TwistedKaroubi R C ⥤ Karoubi C where
  obj M := ⟨M.X, M.p, M.idem⟩
  map {M N} f := ⟨f.val, by
    change M.p ≫ f.val ≫ N.p = f.val
    rw [(val_mem f).2.2, (val_mem f).2.1]⟩

/-- Forgetting the twist is faithful. -/
instance : (forgetTwist (R := R) (C := C)).Faithful where
  map_injective h := hom_ext (congrArg Karoubi.Hom.f h)

/-! ### The monoidal structure -/

section Monoidal

variable [MonoidalCategory C] [IsGradedMonoidal R C]

/-- The tensor product of morphisms of degrees `n - m` and `n' - m'` has degree
`(n + n') - (m + m')`. -/
theorem tensor_mem' {M N M' N' : TwistedKaroubi R C} {g : M.X ⟶ N.X} {g' : M'.X ⟶ N'.X}
    (hg : g ∈ grade (R := R) M.X N.X (N.twist - M.twist))
    (hg' : g' ∈ grade (R := R) M'.X N'.X (N'.twist - M'.twist)) :
    g ⊗ₘ g' ∈ grade (R := R) (M.X ⊗ M'.X) (N.X ⊗ N'.X)
      ((N.twist + N'.twist) - (M.twist + M'.twist)) :=
  grade_cast (IsGradedMonoidal.tensorHom_mem hg hg') (by ring)

omit [Preadditive C] in
/-- If `p₁ ≫ a = a` and `p₂ ≫ b = b`, then `(p₁ ⊗ p₂) ≫ (a ⊗ b) = a ⊗ b`. -/
theorem tensor_fix_left {X₁ Y₁ X₂ Y₂ : C} {p₁ : X₁ ⟶ X₁} {p₂ : X₂ ⟶ X₂} {a : X₁ ⟶ Y₁}
    {b : X₂ ⟶ Y₂} (ha : p₁ ≫ a = a) (hb : p₂ ≫ b = b) : (p₁ ⊗ₘ p₂) ≫ (a ⊗ₘ b) = a ⊗ₘ b := by
  rw [tensorHom_comp_tensorHom, ha, hb]

omit [Preadditive C] in
/-- If `a ≫ q₁ = a` and `b ≫ q₂ = b`, then `(a ⊗ b) ≫ (q₁ ⊗ q₂) = a ⊗ b`. -/
theorem tensor_fix_right {X₁ Y₁ X₂ Y₂ : C} {q₁ : Y₁ ⟶ Y₁} {q₂ : Y₂ ⟶ Y₂} {a : X₁ ⟶ Y₁}
    {b : X₂ ⟶ Y₂} (ha : a ≫ q₁ = a) (hb : b ≫ q₂ = b) : (a ⊗ₘ b) ≫ (q₁ ⊗ₘ q₂) = a ⊗ₘ b := by
  rw [tensorHom_comp_tensorHom, ha, hb]

/-- The tensor product of triples `(X, p, m) ⊗ (Y, q, n) = (X ⊗ Y, p ⊗ q, m + n)`. -/
def tensorObjCore (M N : TwistedKaroubi R C) : TwistedKaroubi R C where
  X := M.X ⊗ N.X
  p := M.p ⊗ₘ N.p
  p_mem := by simpa using IsGradedMonoidal.tensorHom_mem M.p_mem N.p_mem
  idem := by rw [tensorHom_comp_tensorHom, M.idem, N.idem]
  twist := M.twist + N.twist

/-- The tensor product of morphisms of triples is the tensor product of `C`. -/
def tensorHomCore {M N M' N' : TwistedKaroubi R C} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObjCore M M' ⟶ tensorObjCore N N' :=
  Hom.mk (f.val ⊗ₘ g.val)
    ⟨tensor_mem' (val_mem f).1 (val_mem g).1,
      tensor_fix_left (val_mem f).2.1 (val_mem g).2.1,
      tensor_fix_right (val_mem f).2.2 (val_mem g).2.2⟩

/-- The unit triple `(𝟙_ C, 𝟙, 0)`. -/
def tensorUnitCore : TwistedKaroubi R C where
  X := 𝟙_ C
  p := 𝟙 _
  p_mem := id_mem _
  idem := comp_id _
  twist := 0

/-- The associativity constraint of `C` intertwines the idempotents of `(M ⊗ N) ⊗ P` and
`M ⊗ (N ⊗ P)`. -/
theorem comm_associator (M N P : TwistedKaroubi R C) :
    (tensorObjCore (tensorObjCore M N) P).p ≫ (α_ M.X N.X P.X).hom =
      (α_ M.X N.X P.X).hom ≫ (tensorObjCore M (tensorObjCore N P)).p :=
  associator_naturality M.p N.p P.p

/-- The left unit constraint of `C` intertwines the idempotents of `𝟙 ⊗ M` and `M`. -/
theorem comm_leftUnitor (M : TwistedKaroubi R C) :
    (tensorObjCore tensorUnitCore M).p ≫ (λ_ M.X).hom = (λ_ M.X).hom ≫ M.p := by
  change (𝟙 (𝟙_ C) ⊗ₘ M.p) ≫ (λ_ M.X).hom = (λ_ M.X).hom ≫ M.p
  rw [id_tensorHom]
  exact leftUnitor_naturality M.p

/-- The right unit constraint of `C` intertwines the idempotents of `M ⊗ 𝟙` and `M`. -/
theorem comm_rightUnitor (M : TwistedKaroubi R C) :
    (tensorObjCore M tensorUnitCore).p ≫ (ρ_ M.X).hom = (ρ_ M.X).hom ≫ M.p := by
  change (M.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ M.X).hom = (ρ_ M.X).hom ≫ M.p
  rw [tensorHom_id]
  exact rightUnitor_naturality M.p

/-- The monoidal data on triples: the tensor product `(X ⊗ Y, p ⊗ q, m + n)`, the unit
`(𝟙_ C, 𝟙, 0)`, and the constraints of `C` cut down by the idempotents. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (TwistedKaroubi R C) where
  tensorObj := tensorObjCore
  whiskerLeft M _ _ f := tensorHomCore (𝟙 M) f
  whiskerRight f N := tensorHomCore f (𝟙 N)
  tensorHom := tensorHomCore
  tensorUnit := tensorUnitCore
  associator M N P := isoOfIso (α_ M.X N.X P.X)
    (grade_cast (IsGradedMonoidal.associator_hom_mem (R := R) M.X N.X P.X) (by
      change (0 : ℤ) = M.twist + (N.twist + P.twist) - (M.twist + N.twist + P.twist); ring))
    (grade_cast (IsGradedMonoidal.associator_inv_mem (R := R) M.X N.X P.X) (by
      change (0 : ℤ) = M.twist + N.twist + P.twist - (M.twist + (N.twist + P.twist)); ring))
    (comm_associator M N P)
  leftUnitor M := isoOfIso (λ_ M.X)
    (grade_cast (IsGradedMonoidal.leftUnitor_hom_mem (R := R) M.X) (by
      change (0 : ℤ) = M.twist - (0 + M.twist); ring))
    (grade_cast (IsGradedMonoidal.leftUnitor_inv_mem (R := R) M.X) (by
      change (0 : ℤ) = 0 + M.twist - M.twist; ring))
    (comm_leftUnitor M)
  rightUnitor M := isoOfIso (ρ_ M.X)
    (grade_cast (IsGradedMonoidal.rightUnitor_hom_mem (R := R) M.X) (by
      change (0 : ℤ) = M.twist - (M.twist + 0); ring))
    (grade_cast (IsGradedMonoidal.rightUnitor_inv_mem (R := R) M.X) (by
      change (0 : ℤ) = M.twist + 0 - M.twist; ring))
    (comm_rightUnitor M)

/-- The underlying object of `M ⊗ N` is `M.X ⊗ N.X`. -/
@[simp] theorem tensorObj_X (M N : TwistedKaroubi R C) : (M ⊗ N).X = M.X ⊗ N.X := rfl

/-- The idempotent of `M ⊗ N` is `M.p ⊗ N.p`. -/
@[simp] theorem tensorObj_p (M N : TwistedKaroubi R C) : (M ⊗ N).p = M.p ⊗ₘ N.p := rfl

/-- The twist of `M ⊗ N` is the sum of the twists. -/
@[simp] theorem tensorObj_twist (M N : TwistedKaroubi R C) :
    (M ⊗ N).twist = M.twist + N.twist := rfl

/-- The underlying object of the unit is `𝟙_ C`. -/
@[simp] theorem tensorUnit_X : (𝟙_ (TwistedKaroubi R C)).X = 𝟙_ C := rfl

/-- The idempotent of the unit is the identity of `𝟙_ C`. -/
@[simp] theorem tensorUnit_p : (𝟙_ (TwistedKaroubi R C)).p = 𝟙 (𝟙_ C) := rfl

/-- The twist of the unit is zero. -/
@[simp] theorem tensorUnit_twist : (𝟙_ (TwistedKaroubi R C)).twist = 0 := rfl

/-- The underlying morphism of `f ⊗ g` is the tensor product of the underlying morphisms. -/
@[simp] theorem tensorHom_val {M N M' N' : TwistedKaroubi R C} (f : M ⟶ N) (g : M' ⟶ N') :
    (f ⊗ₘ g).val = f.val ⊗ₘ g.val := rfl

/-- The underlying morphism of `M ◁ f` is `M.p ⊗ f`. -/
@[simp] theorem whiskerLeft_val (M : TwistedKaroubi R C) {N N' : TwistedKaroubi R C}
    (f : N ⟶ N') : (M ◁ f).val = M.p ⊗ₘ f.val := rfl

/-- The underlying morphism of `f ▷ N` is `f ⊗ N.p`. -/
@[simp] theorem whiskerRight_val {M M' : TwistedKaroubi R C} (f : M ⟶ M')
    (N : TwistedKaroubi R C) : (f ▷ N).val = f.val ⊗ₘ N.p := rfl

/-- The associativity constraint of triples is that of `C`, cut down by the idempotents. -/
theorem associator_hom_val (M N P : TwistedKaroubi R C) :
    (α_ M N P).hom.val = ((M ⊗ N) ⊗ P).p ≫ (α_ M.X N.X P.X).hom := rfl

/-- The inverse associativity constraint of triples is that of `C`, cut down by the
idempotents. -/
theorem associator_inv_val (M N P : TwistedKaroubi R C) :
    (α_ M N P).inv.val = (M ⊗ (N ⊗ P)).p ≫ (α_ M.X N.X P.X).inv := rfl

/-- The left unit constraint of triples is that of `C`, cut down by the idempotents. -/
theorem leftUnitor_hom_val (M : TwistedKaroubi R C) :
    (λ_ M).hom.val = (𝟙_ (TwistedKaroubi R C) ⊗ M).p ≫ (λ_ M.X).hom := rfl

/-- The inverse left unit constraint of triples is that of `C`, cut down by the idempotent. -/
theorem leftUnitor_inv_val (M : TwistedKaroubi R C) :
    (λ_ M).inv.val = M.p ≫ (λ_ M.X).inv := rfl

/-- The right unit constraint of triples is that of `C`, cut down by the idempotents. -/
theorem rightUnitor_hom_val (M : TwistedKaroubi R C) :
    (ρ_ M).hom.val = (M ⊗ 𝟙_ (TwistedKaroubi R C)).p ≫ (ρ_ M.X).hom := rfl

/-- The inverse right unit constraint of triples is that of `C`, cut down by the idempotent. -/
theorem rightUnitor_inv_val (M : TwistedKaroubi R C) :
    (ρ_ M).inv.val = M.p ≫ (ρ_ M.X).inv := rfl

/-- The data needed to induce the monoidal axioms along `forgetTwist`: the tensor product, the
unit and the constraints of triples are sent to those of the Karoubi envelope on the nose. -/
def inducingFunctorData : Monoidal.InducingFunctorData (forgetTwist (R := R) (C := C)) where
  μIso M N := Iso.refl (forgetTwist.obj M ⊗ forgetTwist.obj N)
  εIso := Iso.refl (𝟙_ (Karoubi C))
  whiskerLeft_eq M N N' f := by
    apply Karoubi.hom_ext
    change M.p ⊗ₘ f.val = (M.p ⊗ₘ N.p) ≫ (M.p ⊗ₘ f.val) ≫ (M.p ⊗ₘ N'.p)
    rw [tensor_fix_right M.idem (val_mem f).2.2, tensor_fix_left M.idem (val_mem f).2.1]
  whiskerRight_eq {M M'} f N := by
    apply Karoubi.hom_ext
    change f.val ⊗ₘ N.p = (M.p ⊗ₘ N.p) ≫ (f.val ⊗ₘ N.p) ≫ (M'.p ⊗ₘ N.p)
    rw [tensor_fix_right (val_mem f).2.2 N.idem, tensor_fix_left (val_mem f).2.1 N.idem]
  tensorHom_eq {M N M' N'} f g := by
    apply Karoubi.hom_ext
    change f.val ⊗ₘ g.val = (M.p ⊗ₘ M'.p) ≫ (f.val ⊗ₘ g.val) ≫ (N.p ⊗ₘ N'.p)
    rw [tensor_fix_right (val_mem f).2.2 (val_mem g).2.2,
      tensor_fix_left (val_mem f).2.1 (val_mem g).2.1]
  associator_eq M N P := by
    apply Karoubi.hom_ext
    change ((M.p ⊗ₘ N.p) ⊗ₘ P.p) ≫ (α_ M.X N.X P.X).hom =
      (((M.p ⊗ₘ N.p) ⊗ₘ P.p) ≫ ((M.p ⊗ₘ N.p) ⊗ₘ P.p)) ≫
        ((((M.p ⊗ₘ N.p) ⊗ₘ P.p) ≫ (α_ M.X N.X P.X).hom) ≫
          ((M.p ⊗ₘ (N.p ⊗ₘ P.p)) ≫ (M.p ⊗ₘ (N.p ⊗ₘ P.p))))
    have hp : ((M.p ⊗ₘ N.p) ⊗ₘ P.p) ≫ ((M.p ⊗ₘ N.p) ⊗ₘ P.p) = (M.p ⊗ₘ N.p) ⊗ₘ P.p :=
      ((M ⊗ N) ⊗ P).idem
    have hq : (M.p ⊗ₘ (N.p ⊗ₘ P.p)) ≫ (M.p ⊗ₘ (N.p ⊗ₘ P.p)) = M.p ⊗ₘ (N.p ⊗ₘ P.p) :=
      (M ⊗ (N ⊗ P)).idem
    have hc := comm_associator M N P
    change ((M.p ⊗ₘ N.p) ⊗ₘ P.p) ≫ (α_ M.X N.X P.X).hom =
      (α_ M.X N.X P.X).hom ≫ (M.p ⊗ₘ (N.p ⊗ₘ P.p)) at hc
    rw [hp, hq, hc, assoc, hq, ← assoc, hc, assoc, hq]
  leftUnitor_eq M := by
    apply Karoubi.hom_ext
    change (𝟙 (𝟙_ C) ⊗ₘ M.p) ≫ (λ_ M.X).hom =
      ((𝟙 (𝟙_ C) ⊗ₘ M.p) ≫ (𝟙 (𝟙_ C) ⊗ₘ M.p)) ≫ ((𝟙 (𝟙_ C) ⊗ₘ M.p) ≫ (λ_ M.X).hom)
    have hu : (𝟙 (𝟙_ C) ⊗ₘ M.p) ≫ (𝟙 (𝟙_ C) ⊗ₘ M.p) = 𝟙 (𝟙_ C) ⊗ₘ M.p :=
      (𝟙_ (TwistedKaroubi R C) ⊗ M).idem
    rw [hu, ← assoc, hu]
  rightUnitor_eq M := by
    apply Karoubi.hom_ext
    change (M.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ M.X).hom =
      ((M.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (M.p ⊗ₘ 𝟙 (𝟙_ C))) ≫ ((M.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ M.X).hom)
    have hu : (M.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (M.p ⊗ₘ 𝟙 (𝟙_ C)) = M.p ⊗ₘ 𝟙 (𝟙_ C) :=
      (M ⊗ 𝟙_ (TwistedKaroubi R C)).idem
    rw [hu, ← assoc, hu]

/-- The twisted Karoubi envelope of a graded monoidal category is monoidal, with
`(X, p, m) ⊗ (Y, q, n) = (X ⊗ Y, p ⊗ q, m + n)` and unit `(𝟙_ C, 𝟙, 0)`. -/
instance monoidalCategory : MonoidalCategory (TwistedKaroubi R C) where
  toMonoidalCategoryStruct := monoidalCategoryStruct
  tensorHom_def := (Monoidal.induced forgetTwist inducingFunctorData).tensorHom_def
  id_tensorHom_id := (Monoidal.induced forgetTwist inducingFunctorData).id_tensorHom_id
  tensorHom_comp_tensorHom :=
    (Monoidal.induced forgetTwist inducingFunctorData).tensorHom_comp_tensorHom
  whiskerLeft_id := (Monoidal.induced forgetTwist inducingFunctorData).whiskerLeft_id
  id_whiskerRight := (Monoidal.induced forgetTwist inducingFunctorData).id_whiskerRight
  associator_naturality :=
    (Monoidal.induced forgetTwist inducingFunctorData).associator_naturality
  leftUnitor_naturality :=
    (Monoidal.induced forgetTwist inducingFunctorData).leftUnitor_naturality
  rightUnitor_naturality :=
    (Monoidal.induced forgetTwist inducingFunctorData).rightUnitor_naturality
  pentagon := (Monoidal.induced forgetTwist inducingFunctorData).pentagon
  triangle := (Monoidal.induced forgetTwist inducingFunctorData).triangle

/-- The monoidal data of the monoidal structure are those of
`CategoryTheory.GradedCategory.TwistedKaroubi.monoidalCategoryStruct`, up to unfolding instances
only, so that clients elaborating `⊗` through either instance path meet the same term. -/
theorem toMonoidalCategoryStruct_eq :
    (MonoidalCategory.toMonoidalCategoryStruct : MonoidalCategoryStruct (TwistedKaroubi R C)) =
      monoidalCategoryStruct := by
  with_reducible_and_instances rfl

/-- Forgetting the twist is a monoidal functor to the Karoubi envelope. -/
instance forgetTwistMonoidal : (forgetTwist (R := R) (C := C)).Monoidal :=
  Monoidal.fromInducedMonoidal forgetTwist inducingFunctorData

/-- The tensor comparison morphism of `forgetTwist` is the identity. -/
theorem forgetTwist_μ (M N : TwistedKaroubi R C) :
    Functor.LaxMonoidal.μ (forgetTwist (R := R) (C := C)) M N =
      𝟙 (forgetTwist.obj M ⊗ forgetTwist.obj N) :=
  rfl

/-! ### Tensoring with the twisted units -/

/-- Tensoring with the twisted unit `(𝟙_ C, 𝟙, m)` adds `m` to the twist:
`(X, p, n) ⊗ (𝟙_ C, 𝟙, m) ≅ (X, p, n + m)`, by the right unit constraint of `C`. -/
def tensorUnitTwistIso (M : TwistedKaroubi R C) (m : ℤ) :
    M ⊗ { ofObj (R := R) (𝟙_ C) with twist := m } ≅ { M with twist := M.twist + m } :=
  isoOfIso (ρ_ M.X)
    (grade_cast (IsGradedMonoidal.rightUnitor_hom_mem (R := R) M.X) (by
      change (0 : ℤ) = M.twist + m - (M.twist + m); ring))
    (grade_cast (IsGradedMonoidal.rightUnitor_inv_mem (R := R) M.X) (by
      change (0 : ℤ) = M.twist + m - (M.twist + m); ring))
    (by
      change (M.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ M.X).hom = (ρ_ M.X).hom ≫ M.p
      rw [tensorHom_id]
      exact rightUnitor_naturality M.p)

/-- The underlying morphism of `tensorUnitTwistIso M m` is the right unit constraint of `C`, cut
down by the idempotent. -/
@[simp]
theorem tensorUnitTwistIso_hom_val (M : TwistedKaroubi R C) (m : ℤ) :
    (tensorUnitTwistIso M m).hom.val = (M.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ M.X).hom :=
  rfl

/-- Changing the twist along an equality of integers is an isomorphism of triples. -/
def twistCongrIso (M : TwistedKaroubi R C) {m n : ℤ} (h : m = n) :
    ({ M with twist := m } : TwistedKaroubi R C) ≅ { M with twist := n } :=
  eqToIso (by rw [h])

omit [MonoidalCategory C] [IsGradedMonoidal R C] in
/-- The underlying morphism of `twistCongrIso M h` is the idempotent `M.p`. -/
@[simp]
theorem twistCongrIso_hom_val (M : TwistedKaroubi R C) {m n : ℤ} (h : m = n) :
    (twistCongrIso M h).hom.val = M.p := by
  subst h
  rfl

/-- The twisted units multiply: `(𝟙_ C, 𝟙, n) ⊗ (𝟙_ C, 𝟙, m) ≅ (𝟙_ C, 𝟙, n + m)`. -/
def unitTwistTensorIso (n m : ℤ) :
    ({ ofObj (R := R) (𝟙_ C) with twist := n } : TwistedKaroubi R C) ⊗
        { ofObj (R := R) (𝟙_ C) with twist := m } ≅
      { ofObj (R := R) (𝟙_ C) with twist := n + m } :=
  tensorUnitTwistIso { ofObj (R := R) (𝟙_ C) with twist := n } m

/-- The twisted unit `(𝟙_ C, 𝟙, 0)` is the unit of the twisted Karoubi envelope. -/
theorem unitTwist_zero : ({ ofObj (R := R) (𝟙_ C) with twist := 0 } : TwistedKaroubi R C) =
    𝟙_ (TwistedKaroubi R C) :=
  rfl

/-- The twisted unit `(𝟙_ C, 𝟙, n)` is invertible, with inverse `(𝟙_ C, 𝟙, n')` for
`n + n' = 0`. -/
def unitTwistHasInverse (n n' : ℤ) (h : n + n' = 0) :
    HasInverse ({ ofObj (R := R) (𝟙_ C) with twist := n } : TwistedKaroubi R C) where
  inv := { ofObj (R := R) (𝟙_ C) with twist := n' }
  isoLeft := unitTwistTensorIso n n' ≪≫ twistCongrIso (ofObj (R := R) (𝟙_ C)) h
  isoRight := unitTwistTensorIso n' n ≪≫
    twistCongrIso (ofObj (R := R) (𝟙_ C)) ((add_comm n' n).trans h)

/-- The twisted unit `(𝟙_ C, 𝟙, n)` is invertible. -/
theorem isInvertible_unitTwist (n : ℤ) :
    IsInvertible ({ ofObj (R := R) (𝟙_ C) with twist := n } : TwistedKaroubi R C) :=
  ⟨unitTwistHasInverse n (-n) (add_neg_cancel n)⟩

/-- `(𝟙_ C, 𝟙, n')` is a right dual of `(𝟙_ C, 𝟙, n)` for `n + n' = 0`, with the coevaluation
the inverse of `(𝟙_ C, 𝟙, n) ⊗ (𝟙_ C, 𝟙, n') ≅ 𝟙`. -/
@[instance_reducible]
noncomputable def unitTwistExactPairing (n n' : ℤ) (h : n + n' = 0) :
    ExactPairing ({ ofObj (R := R) (𝟙_ C) with twist := n } : TwistedKaroubi R C)
      { ofObj (R := R) (𝟙_ C) with twist := n' } :=
  (unitTwistHasInverse n n' h).exactPairing

end Monoidal

/-! ### The braiding -/

section Braided

variable [MonoidalCategory C] [IsGradedMonoidal R C] [BraidedCategory C] [IsGradedBraided R C]

omit [IsGradedBraided R C] in
/-- The commutativity constraint of `C` intertwines the idempotents of `M ⊗ N` and `N ⊗ M`. -/
theorem comm_braiding (M N : TwistedKaroubi R C) :
    (M ⊗ N).p ≫ (β_ M.X N.X).hom = (β_ M.X N.X).hom ≫ (N ⊗ M).p :=
  BraidedCategory.braiding_naturality M.p N.p

omit [IsGradedBraided R C] in
/-- Precomposing `(M.p ⊗ N.p) ≫ β` with `M.p ⊗ N.p` and postcomposing it with `N.p ⊗ M.p`
give the same morphism. -/
theorem braided_aux' (M N : TwistedKaroubi R C) :
    (M.p ⊗ₘ N.p) ≫ ((M.p ⊗ₘ N.p) ≫ (β_ M.X N.X).hom) =
      ((M.p ⊗ₘ N.p) ≫ (β_ M.X N.X).hom) ≫ (N.p ⊗ₘ M.p) := by
  have hp : (M.p ⊗ₘ N.p) ≫ (M.p ⊗ₘ N.p) = M.p ⊗ₘ N.p := (M ⊗ N).idem
  have hq : (N.p ⊗ₘ M.p) ≫ (N.p ⊗ₘ M.p) = N.p ⊗ₘ M.p := (N ⊗ M).idem
  have hc := comm_braiding M N
  change (M.p ⊗ₘ N.p) ≫ (β_ M.X N.X).hom = (β_ M.X N.X).hom ≫ (N.p ⊗ₘ M.p) at hc
  rw [← assoc, hp, hc, assoc, hq]

/-- The commutativity constraint of triples: that of `C`, cut down by the idempotents. -/
def braidingIso (M N : TwistedKaroubi R C) : M ⊗ N ≅ N ⊗ M :=
  isoOfIso (β_ M.X N.X)
    (grade_cast (IsGradedBraided.braiding_hom_mem (R := R) M.X N.X) (by
      change (0 : ℤ) = N.twist + M.twist - (M.twist + N.twist); ring))
    (grade_cast (IsGradedBraided.braiding_inv_mem (R := R) M.X N.X) (by
      change (0 : ℤ) = M.twist + N.twist - (N.twist + M.twist); ring))
    (comm_braiding M N)

/-- `forgetTwist` sends `braidingIso M N` to the braiding of the Karoubi envelope, up to the
tensor comparison morphisms. -/
theorem braided_aux (M N : TwistedKaroubi R C) :
    Functor.LaxMonoidal.μ forgetTwist M N ≫ forgetTwist.map (braidingIso M N).hom =
      (β_ (forgetTwist.obj M) (forgetTwist.obj N)).hom ≫
        Functor.LaxMonoidal.μ forgetTwist N M :=
  Karoubi.hom_ext _ _ (braided_aux' M N)

/-- The twisted Karoubi envelope of a graded braided monoidal category is braided, for the
commutativity constraint of `C` cut down by the idempotents. -/
instance braidedCategory : BraidedCategory (TwistedKaroubi R C) :=
  BraidedCategory.ofFaithful forgetTwist braidingIso (fun M N => braided_aux M N)

/-- The commutativity constraint of triples is that of `C`, cut down by the idempotents. -/
theorem braiding_hom_val (M N : TwistedKaroubi R C) :
    (β_ M N).hom.val = (M ⊗ N).p ≫ (β_ M.X N.X).hom := rfl

/-- Forgetting the twist is a braided functor to the Karoubi envelope. -/
instance forgetTwistBraided : (forgetTwist (R := R) (C := C)).Braided where
  braided M N := braided_aux M N

end Braided

section Symmetric

variable [MonoidalCategory C] [IsGradedMonoidal R C] [SymmetricCategory C]
  [IsGradedBraided R C]

/-- The twisted Karoubi envelope of a graded symmetric monoidal category is symmetric. -/
instance symmetricCategory : SymmetricCategory (TwistedKaroubi R C) :=
  SymmetricCategory.ofFaithful forgetTwist

end Symmetric

end TwistedKaroubi

end CategoryTheory.GradedCategory
