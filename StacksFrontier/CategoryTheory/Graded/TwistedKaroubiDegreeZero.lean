module

public import StacksFrontier.CategoryTheory.Graded.DegreeZeroMonoidal
public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidal

/-!
# Untwisted triples

Let `C` be a category graded over a ring `R`. A formal direct factor `(X, p)` of the degree-zero
category `DegreeZero R C` (an object of its Karoubi envelope) is the same thing as a twisted
idempotent `(X, p, 0)` of twist zero, and the morphisms agree: both are the degree-zero
morphisms of `C` fixed by the two idempotents. This file makes that into a functor

  `Karoubi (DegreeZero R C) ⥤ TwistedKaroubi R C`, `(X, p) ↦ (X, p, 0)`,

which is fully faithful and additive, and braided monoidal when `C` is graded braided monoidal.
For the graded category of correspondences it embeds the motives of twist zero, built from
correspondences of degree zero, into the category `M_k` of Chow motives; this is the functor
along which the universal property of Stacks 0FGH extends.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.untwisted`: the functor `(X, p) ↦ (X, p, 0)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.untwistedCoreMonoidal`: its monoidal structure,
  with identity comparison morphisms.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Idempotents

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]

variable (R C) in
/-- The functor `(X, p) ↦ (X, p, 0)` from the Karoubi envelope of the degree-zero category to the
twisted Karoubi envelope. -/
@[simps obj_X obj_p obj_twist]
def untwisted : Karoubi (DegreeZero R C) ⥤ TwistedKaroubi R C where
  obj P :=
    { X := P.X.toC
      p := DegreeZero.val P.p
      p_mem := DegreeZero.val_mem P.p
      idem := congrArg DegreeZero.val P.idem
      twist := 0 }
  map {P Q} f := Hom.mk (DegreeZero.val f.f)
    ⟨by rw [sub_self]; exact DegreeZero.val_mem f.f,
      congrArg DegreeZero.val (Karoubi.p_comp f), congrArg DegreeZero.val (Karoubi.comp_p f)⟩
  map_id P := rfl
  map_comp f g := rfl

/-- The underlying morphism of `C` of the image of `f` under `untwisted` is that of `f`. -/
@[simp]
theorem untwisted_map_val {P Q : Karoubi (DegreeZero R C)} (f : P ⟶ Q) :
    ((untwisted R C).map f).val = DegreeZero.val f.f :=
  rfl

/-- A morphism `f : (X, p) ⟶ (Y, q)` of the Karoubi envelope satisfies `p ≫ f = f` in `C`. -/
theorem p_comp_val {P Q : Karoubi (DegreeZero R C)} (f : P ⟶ Q) :
    DegreeZero.val P.p ≫ DegreeZero.val f.f = DegreeZero.val f.f :=
  congrArg DegreeZero.val (Karoubi.p_comp f)

/-- A morphism `f : (X, p) ⟶ (Y, q)` of the Karoubi envelope satisfies `f ≫ q = f` in `C`. -/
theorem comp_p_val {P Q : Karoubi (DegreeZero R C)} (f : P ⟶ Q) :
    DegreeZero.val f.f ≫ DegreeZero.val Q.p = DegreeZero.val f.f :=
  congrArg DegreeZero.val (Karoubi.comp_p f)

/-- The idempotent `p` of an object `(X, p)` of the Karoubi envelope satisfies `p ≫ p = p` in
`C`. -/
theorem p_idem_val (P : Karoubi (DegreeZero R C)) :
    DegreeZero.val P.p ≫ DegreeZero.val P.p = DegreeZero.val P.p :=
  congrArg DegreeZero.val P.idem

/-- The functor `(X, p) ↦ (X, p, 0)` is faithful. -/
instance : (untwisted R C).Faithful where
  map_injective {_ _} _ _ h := Karoubi.hom_ext _ _ (DegreeZero.hom_ext (congrArg Hom.val h))

/-- The functor `(X, p) ↦ (X, p, 0)` is full. -/
instance : (untwisted R C).Full where
  map_surjective {P Q} g := by
    refine ⟨⟨DegreeZero.homMk g.val ?_, ?_⟩, hom_ext rfl⟩
    · have h := (val_mem g).1
      change g.val ∈ grade (R := R) _ _ (0 - 0) at h
      rwa [sub_self] at h
    · exact DegreeZero.hom_ext <|
        (congrArg (fun t ↦ DegreeZero.val P.p ≫ t) (val_mem g).2.2).trans (val_mem g).2.1

/-- The functor `(X, p) ↦ (X, p, 0)` is additive. -/
instance : (untwisted R C).Additive where

section Monoidal

variable [MonoidalCategory C] [IsGradedMonoidal R C]

/-- The tensor product of two idempotents is idempotent. -/
private theorem tensorHom_idem {D : Type*} [Category D] [MonoidalCategory D]
    {X Y : D} {f : X ⟶ X} {g : Y ⟶ Y} (hf : f ≫ f = f) (hg : g ≫ g = g) :
    (f ⊗ₘ g) ≫ (f ⊗ₘ g) = f ⊗ₘ g := by
  rw [tensorHom_comp_tensorHom, hf, hg]

omit [IsGradedMonoidal R C] in
/-- For objects `(X, p)` and `(Y, q)` of the Karoubi envelope, `p ⊗ q` is idempotent in `C`. -/
theorem tensor_p_idem (P Q : Karoubi (DegreeZero R C)) :
    (DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p) ≫ (DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p) =
      DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p :=
  tensorHom_idem (p_idem_val P) (p_idem_val Q)

/-- The comparison `(X, p, 0) ⊗ (Y, q, 0) ≅ (X ⊗ Y, p ⊗ q, 0)`; both sides are `(X ⊗ Y, p ⊗ q)`
with twists `0 + 0` and `0`, and the comparison is `p ⊗ q`, the identity of either. -/
def untwistedμIso (P Q : Karoubi (DegreeZero R C)) :
    (untwisted R C).obj P ⊗ (untwisted R C).obj Q ≅ (untwisted R C).obj (P ⊗ Q) where
  hom := Hom.mk (DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p)
    ⟨grade_cast (DegreeZero.tensorHom_mem (R := R) (DegreeZero.val_mem P.p)
        (DegreeZero.val_mem Q.p)) (by simp), tensor_p_idem P Q, tensor_p_idem P Q⟩
  inv := Hom.mk (DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p)
    ⟨grade_cast (DegreeZero.tensorHom_mem (R := R) (DegreeZero.val_mem P.p)
        (DegreeZero.val_mem Q.p)) (by simp), tensor_p_idem P Q, tensor_p_idem P Q⟩
  hom_inv_id := hom_ext (tensor_p_idem P Q)
  inv_hom_id := hom_ext (tensor_p_idem P Q)

/-- The underlying morphism of `C` of `(untwistedμIso P Q).hom` is `p ⊗ q`. -/
@[simp]
theorem untwistedμIso_hom_val (P Q : Karoubi (DegreeZero R C)) :
    (untwistedμIso P Q).hom.val = DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p :=
  rfl

/-- The comparison of units `(𝟙, 𝟙, 0) ≅ (𝟙, 𝟙, 0)`. -/
def untwistedεIso : 𝟙_ (TwistedKaroubi R C) ≅ (untwisted R C).obj (𝟙_ (Karoubi (DegreeZero R C)))
    where
  hom := Hom.mk (𝟙 (𝟙_ C)) ⟨grade_cast (id_mem (R := R) (𝟙_ C)) (by simp),
    Category.id_comp _, Category.id_comp _⟩
  inv := Hom.mk (𝟙 (𝟙_ C)) ⟨grade_cast (id_mem (R := R) (𝟙_ C)) (by simp),
    Category.id_comp _, Category.id_comp _⟩
  hom_inv_id := hom_ext (Category.id_comp _)
  inv_hom_id := hom_ext (Category.id_comp _)

/-- The underlying morphism of `C` of `untwistedεIso.hom` is the identity of `𝟙_ C`. -/
@[simp]
theorem untwistedεIso_hom_val : (untwistedεIso (R := R) (C := C)).hom.val = 𝟙 (𝟙_ C) :=
  rfl

omit [IsGradedMonoidal R C] in
/-- For `f : (X, p) ⟶ (Y, q)` and an object `(X', r)`, the square
`(f ⊗ r) ≫ (q ⊗ r) = (p ⊗ r) ≫ (f ⊗ r)` commutes in `C`. -/
theorem untwisted_natural_left {P Q : Karoubi (DegreeZero R C)} (f : P ⟶ Q)
    (X' : Karoubi (DegreeZero R C)) :
    (DegreeZero.val f.f ⊗ₘ DegreeZero.val X'.p) ≫ (DegreeZero.val Q.p ⊗ₘ DegreeZero.val X'.p) =
      (DegreeZero.val P.p ⊗ₘ DegreeZero.val X'.p) ≫
        (DegreeZero.val f.f ⊗ₘ DegreeZero.val X'.p) := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, comp_p_val, p_comp_val, p_idem_val]

omit [IsGradedMonoidal R C] in
/-- For an object `(X', r)` and `f : (X, p) ⟶ (Y, q)`, the square
`(r ⊗ f) ≫ (r ⊗ q) = (r ⊗ p) ≫ (r ⊗ f)` commutes in `C`. -/
theorem untwisted_natural_right {P Q : Karoubi (DegreeZero R C)} (X' : Karoubi (DegreeZero R C))
    (f : P ⟶ Q) :
    (DegreeZero.val X'.p ⊗ₘ DegreeZero.val f.f) ≫ (DegreeZero.val X'.p ⊗ₘ DegreeZero.val Q.p) =
      (DegreeZero.val X'.p ⊗ₘ DegreeZero.val P.p) ≫
        (DegreeZero.val X'.p ⊗ₘ DegreeZero.val f.f) := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, comp_p_val, p_comp_val, p_idem_val]

omit [IsGradedMonoidal R C] in
/-- For objects `(X, p)`, `(Y, q)`, `(Z, r)`, the associator `α_ X Y Z` of `C` commutes with the
idempotents `(p ⊗ q) ⊗ r` and `p ⊗ (q ⊗ r)`. -/
theorem untwisted_associativity (X Y Z : Karoubi (DegreeZero R C)) :
    ((DegreeZero.val X.p ⊗ₘ DegreeZero.val Y.p) ⊗ₘ DegreeZero.val Z.p) ≫
        ((DegreeZero.val X.p ⊗ₘ DegreeZero.val Y.p) ⊗ₘ DegreeZero.val Z.p) ≫
          ((DegreeZero.val X.p ⊗ₘ DegreeZero.val Y.p) ⊗ₘ DegreeZero.val Z.p) ≫
            (α_ X.X.toC Y.X.toC Z.X.toC).hom =
      (((DegreeZero.val X.p ⊗ₘ DegreeZero.val Y.p) ⊗ₘ DegreeZero.val Z.p) ≫
          (α_ X.X.toC Y.X.toC Z.X.toC).hom) ≫
        (DegreeZero.val X.p ⊗ₘ (DegreeZero.val Y.p ⊗ₘ DegreeZero.val Z.p)) ≫
          (DegreeZero.val X.p ⊗ₘ (DegreeZero.val Y.p ⊗ₘ DegreeZero.val Z.p)) := by
  have hp := tensorHom_idem (tensor_p_idem X Y) (p_idem_val Z)
  have hq := tensorHom_idem (p_idem_val X) (tensor_p_idem Y Z)
  rw [reassoc_of% hp, reassoc_of% hp, assoc, hq, associator_naturality, associator_naturality_assoc,
    hq]

omit [IsGradedMonoidal R C] in
/-- For an object `(X, p)`, the left unitor `λ_ X` of `C` composed after the idempotent `𝟙 ⊗ p`
is unchanged by inserting further copies of `𝟙 ⊗ p`. -/
theorem untwisted_left_unitality (X : Karoubi (DegreeZero R C)) :
    (𝟙 (𝟙_ C) ⊗ₘ DegreeZero.val X.p) ≫ (λ_ X.X.toC).hom =
      (𝟙 (𝟙_ C) ⊗ₘ DegreeZero.val X.p) ≫ (𝟙 (𝟙_ C) ⊗ₘ DegreeZero.val X.p) ≫
        (𝟙 (𝟙_ C) ⊗ₘ DegreeZero.val X.p) ≫ (λ_ X.X.toC).hom := by
  have hu := tensorHom_idem (f := 𝟙 (𝟙_ C)) (id_comp _) (p_idem_val X)
  rw [reassoc_of% hu, reassoc_of% hu]

omit [IsGradedMonoidal R C] in
/-- For an object `(X, p)`, the right unitor `ρ_ X` of `C` composed after the idempotent `p ⊗ 𝟙`
is unchanged by inserting further copies of `p ⊗ 𝟙`. -/
theorem untwisted_right_unitality (X : Karoubi (DegreeZero R C)) :
    (DegreeZero.val X.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ X.X.toC).hom =
      (DegreeZero.val X.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (DegreeZero.val X.p ⊗ₘ 𝟙 (𝟙_ C)) ≫
        (DegreeZero.val X.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ X.X.toC).hom := by
  have hu := tensorHom_idem (p_idem_val X) (g := 𝟙 (𝟙_ C)) (id_comp _)
  rw [reassoc_of% hu, reassoc_of% hu]

/-- The functor `(X, p) ↦ (X, p, 0)` is monoidal: both tensor products are `(X ⊗ Y, p ⊗ q)`, and
the twists `0 + 0` and `0` agree. -/
def untwistedCoreMonoidal : (untwisted R C).CoreMonoidal where
  εIso := untwistedεIso
  μIso := untwistedμIso
  μIso_hom_natural_left f X' := hom_ext (untwisted_natural_left f X')
  μIso_hom_natural_right X' f := hom_ext (untwisted_natural_right X' f)
  associativity X Y Z := hom_ext (untwisted_associativity X Y Z)
  left_unitality X := hom_ext (untwisted_left_unitality X)
  right_unitality X := hom_ext (untwisted_right_unitality X)

/-- The functor `(X, p) ↦ (X, p, 0)` is monoidal. -/
instance untwistedMonoidal : (untwisted R C).Monoidal :=
  (untwistedCoreMonoidal (R := R) (C := C)).toMonoidal

/-- The underlying morphism of `C` of the tensor comparison `μ` of `untwisted` at `(X, p)` and
`(Y, q)` is `p ⊗ q`. -/
@[simp]
theorem untwisted_μ_val (P Q : Karoubi (DegreeZero R C)) :
    (Functor.LaxMonoidal.μ (untwisted R C) P Q).val = DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p :=
  rfl

/-- The underlying morphism of `C` of the unit comparison `ε` of `untwisted` is the identity of
`𝟙_ C`. -/
@[simp]
theorem untwisted_ε_val : (Functor.LaxMonoidal.ε (untwisted R C)).val = 𝟙 (𝟙_ C) :=
  rfl

end Monoidal

section Braided

variable [MonoidalCategory C] [IsGradedMonoidal R C] [BraidedCategory C] [IsGradedBraided R C]

omit [IsGradedMonoidal R C] [IsGradedBraided R C] in
/-- For objects `(X, p)` and `(Y, q)`, the braiding `β_ X Y` of `C` composed after `p ⊗ q`
intertwines the idempotents `p ⊗ q` and `q ⊗ p`. -/
theorem untwisted_braided (P Q : Karoubi (DegreeZero R C)) :
    (DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p) ≫
        ((DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p) ≫ (β_ P.X.toC Q.X.toC).hom) =
      ((DegreeZero.val P.p ⊗ₘ DegreeZero.val Q.p) ≫ (β_ P.X.toC Q.X.toC).hom) ≫
        (DegreeZero.val Q.p ⊗ₘ DegreeZero.val P.p) := by
  rw [reassoc_of% tensor_p_idem, assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_naturality_assoc, tensor_p_idem]

/-- The functor `(X, p) ↦ (X, p, 0)` is braided: on both sides the commutativity constraint is
that of `C`, cut down by the idempotents. -/
instance untwistedBraided : (untwisted R C).Braided where
  braided P Q := hom_ext (untwisted_braided P Q)

end Braided

end CategoryTheory.GradedCategory.TwistedKaroubi
