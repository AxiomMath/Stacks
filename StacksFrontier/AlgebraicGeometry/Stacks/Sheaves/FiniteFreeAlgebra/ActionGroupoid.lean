module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Presheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Scheme

/-!
# The action-groupoid presentation of the presheaf of finite free algebras

Change of basis acts on free algebra structures by the explicit conjugation
`a(g, m) = g⁻¹ ∘ m ∘ (g ⊗ g)`. Transported through the representation of the scheme of
structure constants, this is an action on the points of that scheme, and the resulting
action-groupoid functor is naturally isomorphic to the presheaf in groupoids of free rank-`d`
algebras.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.unitFixingSubgroup`,
  `AlgebraicGeometry.FiniteFreeAlgebra.UnitFixingMatrix`: the change-of-basis group, as the
  invertible matrices fixing the distinguished unit vector, and its functor of points.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationCoefficients`: the action in coordinates.
* `AlgebraicGeometry.FiniteFreeAlgebra.ConjugationPreservesAlgebraLaws`: the statement that
  those coefficients again satisfy the algebra relations.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationAction`,
  `AlgebraicGeometry.FiniteFreeAlgebra.conjugationOnPointsOf`,
  `AlgebraicGeometry.FiniteFreeAlgebra.conjugationOnPoints`: the action on structures, on the
  points of a scheme carrying a given identification with structures, and on the points of the
  scheme of structure constants.
* `AlgebraicGeometry.FiniteFreeAlgebra.ActionGroupoidPresheaf`: the groupoid with objects
  `X(T)` and arrows `(g, x) : x ⟶ a(g, x)`, together with its base change.
* `AlgebraicGeometry.FiniteFreeAlgebra.ActionGroupoidPresheaf.toFunctor`: that data bundled as
  a functor to groupoids.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.presheaf_actionGroupoid`: the natural isomorphism from
  the presheaf of free algebras to the action-groupoid functor.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationPreservesAlgebraLaws`: conjugation does
  preserve the algebra relations.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationOnPoints_one`,
  `AlgebraicGeometry.FiniteFreeAlgebra.conjugationOnPoints_mul` and
  `AlgebraicGeometry.FiniteFreeAlgebra.conjugationOnPoints_naturality`: the three laws of the
  action on `X(T)`.

## Implementation notes

With column-vector matrices this is a right action: `a(h, a(g, m)) = a(g * h, m)`. Accordingly
a composite `f ≫ g` has matrix `matrix(f) * matrix(g)`, and the forward algebra maps used by
the presheaf of free algebras correspond to the inverses of these matrices. Objects of the
action groupoid are scheme morphisms into the representing scheme.

The action, the groupoids, their base change and the natural isomorphism are constructed for an
arbitrary identification `rep : Representation d` of points with structures; the representation
of the scheme of structure constants is substituted only in `conjugationOnPoints` and the main
theorem.

## References

* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

attribute [local irreducible] representation

/-- The subgroup of invertible matrices fixing the distinguished unit vector. -/
public def unitFixingSubgroup (R : Type*) [CommRing R] (d : ℕ) [NeZero d] :
    Subgroup (Matrix.GeneralLinearGroup (Fin d) R) where
  carrier := {g | ∀ k, g k 0 = if k = 0 then 1 else 0}
  one_mem' := by simp [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh k
    simp only [Set.mem_ofPred_eq] at hg hh
    simp [Matrix.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg k
    simp only [Set.mem_ofPred_eq] at hg
    calc
      g⁻¹ k 0 = ∑ l, g⁻¹ k l * g l 0 := by simp [hg]
      _ = (1 : Matrix (Fin d) (Fin d) R) k 0 := by
        rw [← Matrix.mul_apply]
        simp
      _ = if k = 0 then 1 else 0 := by simp [Matrix.one_apply]

/-- A point of the unit-fixing change-of-basis group. -/
public abbrev UnitFixingMatrix (R : Type*) [CommRing R] (d : ℕ) [NeZero d] :=
  ↥(unitFixingSubgroup R d)

/-- Extension of scalars for a unit-fixing matrix, with independent ring universes. -/
public def UnitFixingMatrix.map {R S : Type*} [CommRing R] [CommRing S]
    {d : ℕ} [NeZero d] (f : R →+* S) (g : UnitFixingMatrix R d) :
    UnitFixingMatrix S d :=
  ⟨Matrix.GeneralLinearGroup.map f g.1, by
    intro k
    simp [Matrix.GeneralLinearGroup.map_apply, g.2 k]⟩

private lemma unitFixingMatrix_map_one {R S : Type*} [CommRing R] [CommRing S]
    {d : ℕ} [NeZero d] (f : R →+* S) :
    UnitFixingMatrix.map f (1 : UnitFixingMatrix R d) = 1 :=
  Subtype.ext (Matrix.GeneralLinearGroup.map_one f)

private lemma unitFixingMatrix_map_mul {R S : Type*} [CommRing R] [CommRing S]
    {d : ℕ} [NeZero d] (f : R →+* S) (g h : UnitFixingMatrix R d) :
    UnitFixingMatrix.map f (g * h) = UnitFixingMatrix.map f g * UnitFixingMatrix.map f h :=
  Subtype.ext (Matrix.GeneralLinearGroup.map_mul f g.1 h.1)

/-- The coefficients of `g⁻¹ ∘ m ∘ (g ⊗ g)`, in the standard column bases. -/
public def conjugationCoefficients {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (g : UnitFixingMatrix R d) (m : FiniteFreeAlgebra R d)
    (i j k : Fin d) : R :=
  ∑ l, ∑ p, ∑ q, g.1⁻¹ k l * m.coeff p q l * g.1 p i * g.1 q j

/-- Conjugation preserves the associativity, commutativity and unit relations defining the
scheme of structure constants. -/
public def ConjugationPreservesAlgebraLaws (d : ℕ) [NeZero d] : Prop :=
  ∀ (R : Type u) [CommRing R] (g : UnitFixingMatrix R d)
      (m : FiniteFreeAlgebra R d),
    let c := conjugationCoefficients g m
    (∀ i j k n, ∑ l, c i j l * c l k n = ∑ l, c i l n * c j k l) ∧
    (∀ i j k, c i j k = c j i k) ∧
    (∀ i j, c i 0 j = if i = j then 1 else 0)

/-- The conjugation action of a unit-fixing matrix on free algebra structures, with structure
constants `conjugationCoefficients`. -/
public def conjugationAction {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (g : UnitFixingMatrix R d) (m : FiniteFreeAlgebra R d) :
    FiniteFreeAlgebra R d where
  coeff := conjugationCoefficients g m
  assoc := (laws R g m).1
  comm := (laws R g m).2.1
  unit_coeff := (laws R g m).2.2

/-- The conjugation action on the points of the scheme of structure constants, transported
through a given identification of those points with free algebra structures. -/
public def conjugationOnPointsOf {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})
    (g : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    T ⟶ scheme.{u} d :=
  (rep.equiv T).symm (conjugationAction laws g (rep.equiv T x))

/-- The conjugation action on the points `X(T)` of the scheme of structure constants,
transported through its representation of free algebra structures. -/
public def conjugationOnPoints {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})
    (g : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    T ⟶ scheme.{u} d :=
  conjugationOnPointsOf (representation.{u} d) laws T g x

/-- The action-groupoid functor `T ↦ (X(T), G(T) × X(T))`: its objects are the points of `X`,
and its arrows, composition and pullback are given by the conjugation action and matrix
multiplication. -/
public structure ActionGroupoidPresheaf (B : BigFppfSite.{u})
    (d : ℕ) [NeZero d] (laws : ConjugationPreservesAlgebraLaws.{u} d) where
  /-- The identity law for the concrete action. -/
  action_one (T : Scheme.{u}) (x : T ⟶ scheme.{u} d) :
    conjugationOnPoints laws T 1 x = x
  /-- The right-action law in column-matrix convention. -/
  action_mul (T : Scheme.{u}) (g h : UnitFixingMatrix Γ(T, ⊤) d)
      (x : T ⟶ scheme.{u} d) :
    conjugationOnPoints laws T (g * h) x =
      conjugationOnPoints laws T h (conjugationOnPoints laws T g x)
  /-- The action is natural on all schemes, hence is an action of functors of points. -/
  action_naturality {T U : Scheme.{u}} (f : T ⟶ U)
      (g : UnitFixingMatrix Γ(U, ⊤) d) (x : U ⟶ scheme.{u} d) :
    conjugationOnPoints laws T (g.map f.appTop.hom) (f ≫ x) =
      f ≫ conjugationOnPoints laws U g x
  /-- The action groupoid has exactly `X(T)` as its type of objects. -/
  groupoid (T : B.Schemesᵒᵖ) : Groupoid (T.unop.1 ⟶ scheme.{u} d)
  /-- The base-change functors. -/
  pullback {T U : B.Schemesᵒᵖ} (f : T ⟶ U) :
    @Functor (T.unop.1 ⟶ scheme.{u} d) (groupoid T).toCategory
      (U.unop.1 ⟶ scheme.{u} d) (groupoid U).toCategory
  /-- Pullback of points is precomposition. -/
  pullback_obj {T U : B.Schemesᵒᵖ} (f : T ⟶ U)
      (x : T.unop.1 ⟶ scheme.{u} d) :
    (pullback f).obj x = B.inclusion.map f.unop ≫ x
  /-- The identity base change is the identity functor. -/
  pullback_id (T : B.Schemesᵒᵖ) :
    pullback (𝟙 T) = @Functor.id _ (groupoid T).toCategory
  /-- Base change is strictly functorial. -/
  pullback_comp {T U V : B.Schemesᵒᵖ} (f : T ⟶ U) (g : U ⟶ V) :
    pullback (f ≫ g) = (pullback f).comp (pullback g)
  /-- The arrow `(g,x)` has source `x` and target `a(g,x)`. -/
  arrowEquiv (T : B.Schemesᵒᵖ)
      (x y : T.unop.1 ⟶ scheme.{u} d) :
    @Quiver.Hom _ (groupoid T).toCategory.toQuiver x y ≃
      {g : UnitFixingMatrix Γ(T.unop.1, ⊤) d //
        conjugationOnPoints laws T.unop.1 g x = y}
  /-- Identity arrows correspond to the identity matrix. -/
  arrowEquiv_id (T : B.Schemesᵒᵖ) (x : T.unop.1 ⟶ scheme.{u} d) :
    (arrowEquiv T x x (@CategoryStruct.id _ (groupoid T).toCategory.toCategoryStruct x)).1 = 1
  /-- In the right-action convention, the first matrix precedes the second. -/
  arrowEquiv_comp (T : B.Schemesᵒᵖ)
      {x y z : T.unop.1 ⟶ scheme.{u} d}
      (f : @Quiver.Hom _ (groupoid T).toCategory.toQuiver x y)
      (g : @Quiver.Hom _ (groupoid T).toCategory.toQuiver y z) :
    (arrowEquiv T x z
      (@CategoryStruct.comp _ (groupoid T).toCategory.toCategoryStruct x y z f g)).1 =
      (arrowEquiv T x y f).1 * (arrowEquiv T y z g).1
  /-- Pullback of arrows extends the entries of the matrix. -/
  pullback_arrow {T U : B.Schemesᵒᵖ} (f : T ⟶ U)
      {x y : T.unop.1 ⟶ scheme.{u} d}
      (e : @Quiver.Hom _ (groupoid T).toCategory.toQuiver x y) :
    (arrowEquiv U _ _ ((pullback f).map e)).1 =
      ((arrowEquiv T x y e).1).map (B.inclusion.map f.unop).appTop.hom

/-- Bundle the specified action groupoids and pullback maps as a functor. -/
public def ActionGroupoidPresheaf.toFunctor {B : BigFppfSite.{u}}
    {d : ℕ} [NeZero d] {laws : ConjugationPreservesAlgebraLaws.{u} d}
    (P : ActionGroupoidPresheaf B d laws) : B.Schemesᵒᵖ ⥤ Grpd.{u, u} where
  obj T := @Grpd.of (T.unop.1 ⟶ scheme.{u} d) (P.groupoid T)
  map f := P.pullback f
  map_id := P.pullback_id
  map_comp := P.pullback_comp

private lemma gl_inv_mul_entry_sum {R : Type*} [CommRing R] {d : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin d) R) (i j : Fin d) :
    (∑ k, g.1 i k * (g⁻¹).1 k j) = if i = j then 1 else 0 := by
  rw [← Matrix.mul_apply]
  simp [Matrix.one_apply]

private lemma unitFixingMatrix_mul_inv_entry_sum {R : Type*} [CommRing R] {d : ℕ}
    [NeZero d] (g : UnitFixingMatrix R d) (i j : Fin d) :
    (∑ k, g.1 i k * g.1⁻¹ k j) = if i = j then 1 else 0 :=
  gl_inv_mul_entry_sum g.1 i j

/-- Summing a multiple of `g c a * g⁻¹ a e` over `a` extracts the diagonal term. -/
private lemma sum_mul_gl_inv_ite {R : Type*} [CommRing R] {d : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin d) R) (c e : Fin d) (C : R) :
    (∑ a, C * (g.1 c a * (g⁻¹).1 a e)) = if c = e then C else 0 := by
  rw [← Finset.mul_sum, gl_inv_mul_entry_sum]
  split_ifs <;> simp

/-- A change of basis by `g⁻¹` undoes the one by `g` on a bilinear expression. -/
private lemma sum_bilinear_change_inv {R : Type*} [CommRing R] {d : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin d) R) (B : Fin d → Fin d → Fin d → R) (i j l : Fin d) :
    (∑ a, ∑ b, (g⁻¹).1 a i * (g⁻¹).1 b j *
      (∑ p, ∑ q, g.1 p a * g.1 q b * B p q l)) = B i j l := by
  rw [sum_bilinear_change]
  simp_rw [gl_inv_mul_entry_sum]
  simp

private lemma sum_rotate7 {α β γ δ ε ζ η R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε] [Fintype ζ] [Fintype η]
    [AddCommMonoid R] (f : α → β → γ → δ → ε → ζ → η → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ w, f a b c d e z w) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, ∑ w, ∑ a, f a b c d e z w := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  exact Finset.sum_comm

private lemma sum_rotate6 {α β γ δ ε ζ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε] [Fintype ζ]
    [AddCommMonoid R] (f : α → β → γ → δ → ε → ζ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ z, f a b c d e z) =
      ∑ a, ∑ b, ∑ c, ∑ e, ∑ z, ∑ d, f a b c d e z :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma sum_rotate5_second {α β γ δ ε R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    [AddCommMonoid R] (f : α → β → γ → δ → ε → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ a, ∑ c, ∑ d, ∑ e, ∑ b, f a b c d e :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma sum_rotate4_four_to_two {α β γ δ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid R] (f : α → β → γ → δ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ d, ∑ b, ∑ c, f a b c d :=
  Finset.sum_congr rfl fun _ _ =>
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

private lemma sum_rotate5_first {α β γ δ ε R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    [AddCommMonoid R] (f : α → β → γ → δ → ε → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e :=
  Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma sum_rotate4_third_to_first {α β γ δ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid R] (f : α → β → γ → δ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ a, ∑ b, ∑ d, f a b c d :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

private lemma conjugation_assoc_contract_left {R : Type*} [CommRing R]
    {d : ℕ} [NeZero d] (g : UnitFixingMatrix R d)
    (m : FiniteFreeAlgebra R d) (i j k n b c d₁ e z w : Fin d) :
    (∑ a, g.1⁻¹ a e * m.coeff z w e * g.1 z i * g.1 w j *
      (g.1⁻¹ n b * m.coeff c d₁ b * g.1 c a * g.1 d₁ k)) =
      if c = e then
        g.1⁻¹ n b * m.coeff z w e * g.1 z i * g.1 w j *
          m.coeff c d₁ b * g.1 d₁ k
      else 0 :=
  by
  rw [← sum_mul_gl_inv_ite g.1 c e]
  exact Finset.sum_congr rfl fun a _ => by ring

private lemma conjugation_assoc_contract_right {R : Type*} [CommRing R]
    {d : ℕ} [NeZero d] (g : UnitFixingMatrix R d)
    (m : FiniteFreeAlgebra R d) (i j k n b c d₁ e z w : Fin d) :
    (∑ a, g.1⁻¹ n e * m.coeff z w e * g.1 z i * g.1 w a *
      (g.1⁻¹ a b * m.coeff c d₁ b * g.1 c j * g.1 d₁ k)) =
      if w = b then
        g.1⁻¹ n e * m.coeff z w e * g.1 z i * m.coeff c d₁ b *
          g.1 c j * g.1 d₁ k
      else 0 :=
  by
  rw [← sum_mul_gl_inv_ite g.1 w b]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The isomorphism of free `d`-dimensional structures from `m` to its image under the
conjugation action of a unit-fixing matrix `g`, with matrix `g⁻¹`: conjugating the structure
constants by `g` is the same free algebra read in the basis obtained from the standard one
by `g`. -/
public def conjugationIso {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (g : UnitFixingMatrix R d)
    (m : FiniteFreeAlgebra R d) :
    StructureIso m (conjugationAction laws g m) where
  matrix := g.1⁻¹
  map_unit := by
    intro k
    simpa [unitFixingSubgroup] using (g⁻¹).2 k
  map_mul := by
    intro i j k
    change (∑ l, m.coeff i j l * g.1⁻¹ k l) =
      ∑ p, ∑ q, g.1⁻¹ p i * g.1⁻¹ q j *
        (∑ l, ∑ a, ∑ b,
          g.1⁻¹ k l * m.coeff a b l * g.1 a p * g.1 b q)
    have hcontract (a i : Fin d) :
        (∑ p, g.1 a p * g.1⁻¹ p i) = if a = i then 1 else 0 := by
      simpa [Matrix.mul_apply] using unitFixingMatrix_mul_inv_entry_sum g a i
    have hbilin (l : Fin d) :
        (∑ p, ∑ q, g.1⁻¹ p i * g.1⁻¹ q j *
          (∑ a, ∑ b, g.1 a p * g.1 b q * m.coeff a b l)) = m.coeff i j l := by
      rw [sum_bilinear_change]
      simp_rw [hcontract]
      simp
    have hrotate :
        (∑ p, ∑ q, g.1⁻¹ p i * g.1⁻¹ q j *
          (∑ l, ∑ a, ∑ b,
            g.1⁻¹ k l * m.coeff a b l * g.1 a p * g.1 b q)) =
        ∑ l, g.1⁻¹ k l *
          (∑ p, ∑ q, g.1⁻¹ p i * g.1⁻¹ q j *
            (∑ a, ∑ b, g.1 a p * g.1 b q * m.coeff a b l)) := by
      calc
        _ = ∑ p, ∑ q, ∑ l, ∑ a, ∑ b,
            (g.1⁻¹ p i * g.1⁻¹ q j) *
              (g.1⁻¹ k l * m.coeff a b l * g.1 a p * g.1 b q) := by
          simp only [Finset.mul_sum]
        _ = ∑ p, ∑ l, ∑ q, ∑ a, ∑ b,
            (g.1⁻¹ p i * g.1⁻¹ q j) *
              (g.1⁻¹ k l * m.coeff a b l * g.1 a p * g.1 b q) := by
          rw [sum_rotate5_second]
          apply Finset.sum_congr rfl
          intro p hp
          exact sum_rotate4_four_to_two (fun l a b q =>
            (g.1⁻¹ p i * g.1⁻¹ q j) *
              (g.1⁻¹ k l * m.coeff a b l * g.1 a p * g.1 b q))
        _ = ∑ l, ∑ p, ∑ q, ∑ a, ∑ b,
            g.1⁻¹ k l *
              (g.1⁻¹ p i * g.1⁻¹ q j *
                (g.1 a p * g.1 b q * m.coeff a b l)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => by ring
        _ = _ := by simp only [Finset.mul_sum]
    calc
      (∑ l, m.coeff i j l * g.1⁻¹ k l) =
          ∑ l, g.1⁻¹ k l * m.coeff i j l :=
            Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = ∑ l, g.1⁻¹ k l *
          (∑ p, ∑ q, g.1⁻¹ p i * g.1⁻¹ q j *
            (∑ a, ∑ b, g.1 a p * g.1 b q * m.coeff a b l)) := by
            simp only [hbilin]
      _ = ∑ p, ∑ q, g.1⁻¹ p i * g.1⁻¹ q j *
          (∑ l, ∑ a, ∑ b,
            g.1⁻¹ k l * m.coeff a b l * g.1 a p * g.1 b q) := hrotate.symm

private lemma StructureIso.target_eq_of_matrix_eq {R : Type u} [CommRing R]
    {d : ℕ} [NeZero d] {A B C : FiniteFreeAlgebra R d}
    (e : StructureIso A B) (f : StructureIso A C)
    (hm : e.matrix = f.matrix) : B = C := by
  have recover (D : FiniteFreeAlgebra R d)
      (q : StructureIso A D) (i j k : Fin d) :
      D.coeff i j k =
        ∑ a, ∑ b, (q.matrix⁻¹ : Matrix (Fin d) (Fin d) R) a i *
          (q.matrix⁻¹ : Matrix (Fin d) (Fin d) R) b j *
            (∑ l, A.coeff a b l * (q.matrix : Matrix (Fin d) (Fin d) R) k l) := by
    calc
      D.coeff i j k =
          ∑ a, ∑ b, (q.matrix⁻¹ : Matrix (Fin d) (Fin d) R) a i *
            (q.matrix⁻¹ : Matrix (Fin d) (Fin d) R) b j *
              (∑ p, ∑ q', (q.matrix : Matrix (Fin d) (Fin d) R) p a *
                (q.matrix : Matrix (Fin d) (Fin d) R) q' b * D.coeff p q' k) :=
        by simpa only [Matrix.GeneralLinearGroup.coe_inv] using
          (sum_bilinear_change_inv q.matrix D.coeff i j k).symm
      _ = ∑ a, ∑ b, (q.matrix⁻¹ : Matrix (Fin d) (Fin d) R) a i *
          (q.matrix⁻¹ : Matrix (Fin d) (Fin d) R) b j *
            (∑ l, A.coeff a b l * (q.matrix : Matrix (Fin d) (Fin d) R) k l) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        congr 1
        exact (q.map_mul a b k).symm
  have hcoeff : B.coeff = C.coeff := by
    funext i j k
    rw [recover B e i j k, recover C f i j k, hm]
  cases B with
  | mk bcoeff bassoc bcomm bunit =>
    cases C with
    | mk ccoeff cassoc ccomm cunit =>
      simp only [FiniteFreeAlgebra.mk.injEq]
      exact hcoeff

private lemma freeAlgebraStructure_ext {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    {A B : FiniteFreeAlgebra R d}
    (h : ∀ i j k, A.coeff i j k = B.coeff i j k) : A = B := by
  cases A
  cases B
  obtain rfl : _ = _ := funext₃ h
  rfl

private lemma conjugationAction_one {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (m : FiniteFreeAlgebra R d) : conjugationAction laws 1 m = m := by
  apply freeAlgebraStructure_ext
  intro i j k
  simp [conjugationAction, conjugationCoefficients, Matrix.one_apply]

private lemma conjugationAction_mul {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (g h : UnitFixingMatrix R d) (m : FiniteFreeAlgebra R d) :
    conjugationAction laws (g * h) m =
      conjugationAction laws h (conjugationAction laws g m) := by
  let e₁ := conjugationIso laws g m
  let e₂ := conjugationIso laws h (conjugationAction laws g m)
  let e₃ := conjugationIso laws (g * h) m
  let ecomp : StructureIso m
      (conjugationAction laws h (conjugationAction laws g m)) := e₁.comp e₂
  have hm : ecomp.matrix = e₃.matrix := by
    simp [ecomp, e₁, e₂, e₃, StructureIso.comp, conjugationIso,
      mul_inv_rev]
  exact (StructureIso.target_eq_of_matrix_eq
    (A := m) (B := conjugationAction laws h (conjugationAction laws g m))
    (C := conjugationAction laws (g * h) m) ecomp e₃ hm).symm

private lemma freeAlgebra_map_conjugation {R S : Type u} [CommRing R] [CommRing S]
    {d : ℕ} [NeZero d] (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (φ : R →+* S) (g : UnitFixingMatrix R d)
    (m : FiniteFreeAlgebra R d) :
    (conjugationAction laws g m).map φ =
      conjugationAction laws (g.map φ) (m.map φ) := by
  apply freeAlgebraStructure_ext
  intro i j k
  have hinv (a b : Fin d) :
      ((g.1 : Matrix (Fin d) (Fin d) R).map φ)⁻¹ a b =
        φ (((g.1⁻¹ : Matrix (Fin d) (Fin d) R)) a b) := by
    have hGL := Matrix.GeneralLinearGroup.map_inv φ g.1
    have hval := congrArg (fun z : Matrix.GeneralLinearGroup (Fin d) S =>
      (z : Matrix (Fin d) (Fin d) S)) hGL.symm
    rw [Matrix.GeneralLinearGroup.coe_inv] at hval
    have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) S => M a b) hval
    have hmap : (g.1 : Matrix (Fin d) (Fin d) R).map φ =
        (Matrix.GeneralLinearGroup.map φ g.1 : Matrix (Fin d) (Fin d) S) := by
      ext x y
      simp [Matrix.GeneralLinearGroup.map_apply]
    rw [hmap]
    simpa only [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply,
      Matrix.GeneralLinearGroup.coe_inv, UnitFixingMatrix.map] using hentry
  simp [conjugationAction, FiniteFreeAlgebra.map,
    conjugationCoefficients, UnitFixingMatrix.map,
    Matrix.GeneralLinearGroup.map_apply, hinv, map_sum, map_mul]

private lemma conjugationOnPointsOf_one {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})
    (x : T ⟶ scheme.{u} d) :
    conjugationOnPointsOf rep laws T 1 x = x := by
  apply rep.equiv T |>.injective
  simp [conjugationOnPointsOf, conjugationAction_one]

private lemma conjugationOnPointsOf_mul {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})
    (g h : UnitFixingMatrix Γ(T, ⊤) d)
    (x : T ⟶ scheme.{u} d) :
    conjugationOnPointsOf rep laws T (g * h) x =
      conjugationOnPointsOf rep laws T h (conjugationOnPointsOf rep laws T g x) := by
  apply rep.equiv T |>.injective
  simp only [conjugationOnPointsOf, Equiv.apply_symm_apply]
  exact conjugationAction_mul laws g h _

private lemma conjugationOnPointsOf_natural {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    {T U : Scheme.{u}} (f : T ⟶ U)
    (g : UnitFixingMatrix Γ(U, ⊤) d) (x : U ⟶ scheme.{u} d) :
    conjugationOnPointsOf rep laws T (g.map f.appTop.hom) (f ≫ x) =
      f ≫ conjugationOnPointsOf rep laws U g x := by
  apply rep.equiv T |>.injective
  simp only [conjugationOnPointsOf, Equiv.apply_symm_apply]
  show conjugationAction laws (g.map f.appTop.hom) (rep.equiv T (f ≫ x)) =
    rep.equiv T (f ≫ conjugationOnPointsOf rep laws U g x)
  rw [← rep.naturality f x, ← rep.naturality f (conjugationOnPointsOf rep laws U g x)]
  simp only [conjugationOnPointsOf, Equiv.apply_symm_apply]
  exact (freeAlgebra_map_conjugation laws f.appTop.hom g (rep.equiv U x)).symm

private def algebraActionArrowEquiv {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    {A B : FiniteFreeAlgebra R d} :
    StructureIso A B ≃
      {g : UnitFixingMatrix R d // conjugationAction laws g A = B} where
  toFun e := by
    let g : UnitFixingMatrix R d := ⟨e.matrix⁻¹, by
      intro k
      exact e.inv.map_unit k⟩
    have hmat : (conjugationIso laws g A).matrix = e.matrix := by
      simp [g, conjugationIso]
    exact ⟨g, StructureIso.target_eq_of_matrix_eq
      (A := A) (B := conjugationAction laws g A) (C := B)
      (conjugationIso laws g A) e hmat⟩
  invFun q := by
    rcases q with ⟨g, h⟩
    refine { matrix := g.1⁻¹, map_unit := ?_, map_mul := ?_ }
    · exact (conjugationIso laws g A).map_unit
    · intro i j k
      have hcoeff : (conjugationAction laws g A).coeff = B.coeff :=
        congrArg FiniteFreeAlgebra.coeff h
      simp_rw [← hcoeff]
      exact (conjugationIso laws g A).map_mul i j k
  left_inv e := by
    apply StructureIso.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp

private abbrev SchemePointMor (T X : Scheme.{u}) :=
  @Quiver.Hom (Scheme.{u}) (inferInstance) T X

private def pointEquiv {B : BigFppfSite.{u}} {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (F : Presheaf B d) (T : B.Schemesᵒᵖ) :
    F.functor.obj T ≃ SchemePointMor T.unop.1 (scheme.{u} d) :=
  (F.objectEquiv T).trans (rep.equiv T.unop.1).symm

private lemma pointEquiv_map {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (F : Presheaf B d)
    {T U : B.Schemesᵒᵖ} (f : T ⟶ U) (x : F.functor.obj T) :
    pointEquiv rep F U ((F.functor.map f).obj x) =
      B.inclusion.map f.unop ≫ pointEquiv rep F T x := by
  let schemeF := B.inclusion.map f.unop
  let φ := schemeF.appTop.hom
  have hobj : F.objectEquiv U ((F.functor.map f).obj x) =
      (F.objectEquiv T x).map φ := by
    simpa [schemeF, φ] using F.map_object f (F.objectEquiv T x)
  apply rep.equiv U.unop.1 |>.injective
  have hleft : rep.equiv U.unop.1 (pointEquiv rep F U ((F.functor.map f).obj x)) =
      F.objectEquiv U ((F.functor.map f).obj x) :=
    Equiv.apply_symm_apply _ _
  have hrep : rep.equiv T.unop.1 (pointEquiv rep F T x) = F.objectEquiv T x :=
    Equiv.apply_symm_apply _ _
  have hright : rep.equiv U.unop.1
      (schemeF ≫ pointEquiv rep F T x) = (F.objectEquiv T x).map φ := by
    calc
      _ = (rep.equiv T.unop.1 (pointEquiv rep F T x)).map φ :=
        (rep.naturality schemeF (pointEquiv rep F T x)).symm
      _ = (F.objectEquiv T x).map φ := congrArg _ hrep
  rw [hleft, hright, hobj]

private def freePointArrowEquiv {B : BigFppfSite.{u}} {d : ℕ}
    [NeZero d] (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (F : Presheaf B d) (T : B.Schemesᵒᵖ)
    (x y : F.functor.obj T) :
    (@Quiver.Hom _ (Grpd.str' (F.functor.obj T)).toCategory.toQuiver x y) ≃
      {g : UnitFixingMatrix Γ(T.unop.1, ⊤) d //
        conjugationOnPointsOf rep laws T.unop.1 g (pointEquiv rep F T x) =
          pointEquiv rep F T y} where
  toFun e := by
    let q := (algebraActionArrowEquiv (R := Γ(T.unop.1, ⊤)) laws)
      (F.arrowEquiv T x y e)
    refine ⟨q.1, ?_⟩
    apply rep.equiv T.unop.1 |>.injective
    simpa [pointEquiv, conjugationOnPointsOf] using q.2
  invFun q := by
    have h : conjugationAction laws q.1 (F.objectEquiv T x) = F.objectEquiv T y := by
      have hh := congrArg (rep.equiv T.unop.1) q.2
      simpa [pointEquiv, conjugationOnPointsOf] using hh
    exact (F.arrowEquiv T x y).symm
      ((algebraActionArrowEquiv (R := Γ(T.unop.1, ⊤)) laws).symm ⟨q.1, h⟩)
  left_inv e := by
    apply (F.arrowEquiv T x y).injective
    apply (algebraActionArrowEquiv (R := Γ(T.unop.1, ⊤)) laws).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
  right_inv q := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

private lemma freePointArrowEquiv_matrix {B : BigFppfSite.{u}}
    {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (F : Presheaf B d) (T : B.Schemesᵒᵖ)
    (x y : F.functor.obj T)
    (e : @Quiver.Hom _ (Grpd.str' (F.functor.obj T)).toCategory.toQuiver x y) :
    ((freePointArrowEquiv rep laws F T x y e).1).1 = (F.arrowEquiv T x y e).matrix⁻¹ := by
  simp [freePointArrowEquiv, algebraActionArrowEquiv]

private lemma freePointArrowEquiv_symm_matrix {B : BigFppfSite.{u}}
    {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (F : Presheaf B d) (T : B.Schemesᵒᵖ)
    (x y : F.functor.obj T)
    (q : {g : UnitFixingMatrix Γ(T.unop.1, ⊤) d //
      conjugationOnPointsOf rep laws T.unop.1 g (pointEquiv rep F T x) =
        pointEquiv rep F T y}) :
    (F.arrowEquiv T x y ((freePointArrowEquiv rep laws F T x y).symm q)).matrix =
      q.1.1⁻¹ := by
  simp [freePointArrowEquiv, algebraActionArrowEquiv]

private lemma freePointArrowEquiv_map_matrix {B : BigFppfSite.{u}}
    {d : ℕ} [NeZero d] (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (F : Presheaf B d) {T U : B.Schemesᵒᵖ} (f : T ⟶ U)
    (x y : F.functor.obj T)
    (e : @Quiver.Hom _ (Grpd.str' (F.functor.obj T)).toCategory.toQuiver x y) :
    (freePointArrowEquiv rep laws F U ((F.functor.map f).obj x) ((F.functor.map f).obj y)
      ((F.functor.map f).map e)).1.1.1 =
    (UnitFixingMatrix.map (B.inclusion.map f.unop).appTop.hom
      (freePointArrowEquiv rep laws F T x y e).1).1.1 := by
  simp [UnitFixingMatrix.map, freePointArrowEquiv_matrix, F.map_arrow,
    Matrix.GeneralLinearGroup.map_inv]

private lemma conjugationPreservesAlgebraLaws_aux {d : ℕ} [NeZero d] :
    ConjugationPreservesAlgebraLaws.{u} d := by
  intro R _ g m
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro i j k n
    simp only [conjugationCoefficients, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [sum_rotate7]
    conv_rhs => rw [sum_rotate7]
    simp_rw [conjugation_assoc_contract_left, conjugation_assoc_contract_right]
    conv_lhs => rw [sum_rotate6]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hleft (b d₁ z w : Fin d) :
        (∑ c, g.1⁻¹ n b * m.coeff z w c * g.1 z i * g.1 w j *
          m.coeff c d₁ b * g.1 d₁ k) =
        (g.1⁻¹ n b * g.1 z i * g.1 w j * g.1 d₁ k) *
          (∑ c, m.coeff z w c * m.coeff c d₁ b) := by
      calc
        _ = ∑ c, (g.1⁻¹ n b * g.1 z i * g.1 w j * g.1 d₁ k) *
            (m.coeff z w c * m.coeff c d₁ b) := by
              apply Finset.sum_congr rfl
              intro c hc
              ring
        _ = _ := by rw [Finset.mul_sum]
    have hL :
        (∑ b, ∑ c, ∑ d₁, ∑ z, ∑ w,
          g.1⁻¹ n b * m.coeff z w c * g.1 z i * g.1 w j *
            m.coeff c d₁ b * g.1 d₁ k) =
        ∑ b, ∑ d₁, ∑ z, ∑ w,
          (g.1⁻¹ n b * g.1 z i * g.1 w j * g.1 d₁ k) *
            (∑ c, m.coeff z w c * m.coeff c d₁ b) := by
      rw [sum_rotate5_second]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d₁ _ =>
        Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => hleft b d₁ z w
    have hright (e c d₁ z : Fin d) :
        (∑ b, g.1⁻¹ n e * m.coeff z b e * g.1 z i *
          m.coeff c d₁ b * g.1 c j * g.1 d₁ k) =
        (g.1⁻¹ n e * g.1 z i * g.1 c j * g.1 d₁ k) *
          (∑ b, m.coeff z b e * m.coeff c d₁ b) := by
      calc
        _ = ∑ b, (g.1⁻¹ n e * g.1 z i * g.1 c j * g.1 d₁ k) *
            (m.coeff z b e * m.coeff c d₁ b) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
        _ = _ := by rw [Finset.mul_sum]
    have hR :
        (∑ c, ∑ d₁, ∑ e, ∑ z, ∑ b,
          g.1⁻¹ n e * m.coeff z b e * g.1 z i *
            m.coeff c d₁ b * g.1 c j * g.1 d₁ k) =
        ∑ c, ∑ d₁, ∑ e, ∑ z,
          (g.1⁻¹ n e * g.1 z i * g.1 c j * g.1 d₁ k) *
            (∑ b, m.coeff z b e * m.coeff c d₁ b) :=
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d₁ _ =>
        Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun z _ => hright e c d₁ z
    rw [hL]
    simp_rw [m.assoc]
    conv_lhs => rw [sum_rotate4_four_to_two]
    conv_rhs => rw [sum_rotate5_first]
    rw [hR]
    conv_rhs => rw [sum_rotate4_third_to_first]
  · intro i j k
    simp only [conjugationCoefficients]
    apply Finset.sum_congr rfl
    intro l hl
    conv_lhs => rw [Finset.sum_comm]
    simp_rw [m.comm]
    ring_nf
  · intro i j
    simp only [conjugationCoefficients]
    have hg : ∀ k, g.1 k 0 = if k = 0 then 1 else 0 := by
      simpa [unitFixingSubgroup] using g.2
    calc
      ∑ l, ∑ p, ∑ q, g.1⁻¹ j l * m.coeff p q l * g.1 p i * g.1 q 0 =
          ∑ l, g.1⁻¹ j l * g.1 l i := by
        simp [hg, m.unit_coeff, mul_comm, mul_left_comm, mul_assoc]
      _ = if i = j then 1 else 0 := by
        simpa [eq_comm] using gl_inv_mul_entry_sum g.1⁻¹ j i

@[instance_reducible] private def actionPointGroupoid {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (T : Scheme.{u}) :
    Groupoid (T ⟶ scheme.{u} d) where
  Hom x y := {g : UnitFixingMatrix Γ(T, ⊤) d // conjugationOnPointsOf rep laws T g x = y}
  id x := ⟨1, conjugationOnPointsOf_one rep laws T x⟩
  comp f g := ⟨f.1 * g.1, by
    rw [conjugationOnPointsOf_mul, f.2, g.2]
  ⟩
  inv := fun {x y} f => ⟨f.1⁻¹, by
    have h := conjugationOnPointsOf_mul rep laws T f.1 f.1⁻¹ x
    rw [mul_inv_cancel, conjugationOnPointsOf_one] at h
    simpa [f.2] using h.symm
  ⟩
  id_comp _ := Subtype.ext (by simp)
  comp_id _ := Subtype.ext (by simp)
  assoc _ _ _ := Subtype.ext (by simp [mul_assoc])
  inv_comp _ := Subtype.ext (by simp)
  comp_inv _ := Subtype.ext (by simp)

private lemma actionPointGroupoid_map_eq {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (T : Scheme.{u}) :
    letI : Groupoid (T ⟶ scheme.{u} d) :=
      actionPointGroupoid rep laws T
    letI : Category (T ⟶ scheme.{u} d) :=
      (actionPointGroupoid rep laws T).toCategory
    ∀ {x x' y y' : T ⟶ scheme.{u} d}
      (hx : x = x') (hy : y = y') (e : x' ⟶ y') (e' : x ⟶ y),
      (e'.1.1 : Matrix.GeneralLinearGroup (Fin d) Γ(T, ⊤)) = e.1.1 →
        e' = eqToHom hx ≫ e ≫ eqToHom hy.symm := by
  intro x x' y y' hx hy e e' h
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Subtype.ext (Subtype.ext h)

private lemma actionPointGroupoid_id_matrix {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (T : Scheme.{u}) :
    letI : Groupoid (T ⟶ scheme.{u} d) :=
      actionPointGroupoid rep laws T
    letI : Category (T ⟶ scheme.{u} d) :=
      (actionPointGroupoid rep laws T).toCategory
    ∀ (x : T ⟶ scheme.{u} d),
      (𝟙 x : x ⟶ x).1.1 = (1 : Matrix.GeneralLinearGroup (Fin d) Γ(T, ⊤)) := by
  intro x
  rfl

private lemma actionPointGroupoid_comp_matrix {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (T : Scheme.{u}) :
    letI : Groupoid (T ⟶ scheme.{u} d) :=
      actionPointGroupoid rep laws T
    letI : Category (T ⟶ scheme.{u} d) :=
      (actionPointGroupoid rep laws T).toCategory
    ∀ {x y z : T ⟶ scheme.{u} d}
      (f : @Quiver.Hom _ (actionPointGroupoid rep laws T).toCategory.toQuiver x y)
      (g : @Quiver.Hom _ (actionPointGroupoid rep laws T).toCategory.toQuiver y z),
      (@CategoryStruct.comp _ (actionPointGroupoid rep laws T).toCategory.toCategoryStruct
        x y z f g).1.1 = f.1.1 * g.1.1 := by
  intro x y z f g
  rfl

/-- Base change of the action groupoid: precomposition on points, and extension of the matrix
entries along the induced map on global sections on arrows. -/
private def actionPullback {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    {T U : B.Schemesᵒᵖ} (f : T ⟶ U) :
    @Functor (T.unop.1 ⟶ scheme.{u} d) (actionPointGroupoid rep laws T.unop.1).toCategory
      (U.unop.1 ⟶ scheme.{u} d) (actionPointGroupoid rep laws U.unop.1).toCategory := by
  let φ := (B.inclusion.map f.unop).appTop.hom
  letI : Groupoid (T.unop.1 ⟶ scheme.{u} d) :=
    actionPointGroupoid rep laws T.unop.1
  letI : Groupoid (U.unop.1 ⟶ scheme.{u} d) :=
    actionPointGroupoid rep laws U.unop.1
  exact {
    obj := fun x => (B.inclusion.map f.unop) ≫ x
    map := fun {x y} e => ⟨UnitFixingMatrix.map φ e.1, by
      calc
        conjugationOnPointsOf rep laws U.unop.1 (UnitFixingMatrix.map φ e.1)
            ((B.inclusion.map f.unop) ≫ x) =
            (B.inclusion.map f.unop) ≫ conjugationOnPointsOf rep laws T.unop.1 e.1 x :=
          conjugationOnPointsOf_natural rep laws (B.inclusion.map f.unop) e.1 x
        _ = (B.inclusion.map f.unop) ≫ y := congrArg _ e.2⟩
    map_id _ := Subtype.ext (unitFixingMatrix_map_one φ)
    map_comp e₁ e₂ := Subtype.ext (unitFixingMatrix_map_mul φ e₁.1 e₂.1)
  }

private lemma actionPullback_id {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (T : B.Schemesᵒᵖ) :
    actionPullback rep laws (𝟙 T) =
      @Functor.id _ (actionPointGroupoid rep laws T.unop.1).toCategory := by
  let : Groupoid (T.unop.1 ⟶ scheme.{u} d) :=
    actionPointGroupoid rep laws T.unop.1
  have hobj (x : T.unop.1 ⟶ scheme.{u} d) :
      (actionPullback rep laws (𝟙 T)).obj x = x := by
    simp [actionPullback, Category.id_comp]
  refine CategoryTheory.Functor.ext hobj fun x y e =>
    actionPointGroupoid_map_eq rep laws T.unop.1 (hobj x) (hobj y) _ _ ?_
  simp [actionPullback, UnitFixingMatrix.map]

private lemma actionPullback_comp {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    {T U V : B.Schemesᵒᵖ} (f : T ⟶ U) (g : U ⟶ V) :
    actionPullback rep laws (f ≫ g) =
      @Functor.comp _ (actionPointGroupoid rep laws T.unop.1).toCategory
        _ (actionPointGroupoid rep laws U.unop.1).toCategory
        _ (actionPointGroupoid rep laws V.unop.1).toCategory
        (actionPullback rep laws f) (actionPullback rep laws g) := by
  let : Groupoid (T.unop.1 ⟶ scheme.{u} d) :=
    actionPointGroupoid rep laws T.unop.1
  let : Groupoid (U.unop.1 ⟶ scheme.{u} d) :=
    actionPointGroupoid rep laws U.unop.1
  let : Groupoid (V.unop.1 ⟶ scheme.{u} d) :=
    actionPointGroupoid rep laws V.unop.1
  have hmap : B.inclusion.map (f ≫ g).unop =
      B.inclusion.map g.unop ≫ B.inclusion.map f.unop := by
    rw [← B.inclusion.map_comp]
    rfl
  have hobj (x : T.unop.1 ⟶ scheme.{u} d) :
      (B.inclusion.map (f ≫ g).unop) ≫ x =
        (B.inclusion.map g.unop) ≫ ((B.inclusion.map f.unop) ≫ x) := by
    rw [hmap]
    exact Category.assoc _ _ _
  refine CategoryTheory.Functor.ext hobj fun x y e =>
    actionPointGroupoid_map_eq rep laws _ (hobj x) (hobj y) _ _ ?_
  ext i j
  simp only [actionPullback, Functor.comp_map, UnitFixingMatrix.map,
    Matrix.GeneralLinearGroup.map_apply]
  have hring : (B.inclusion.map (f ≫ g).unop).appTop.hom =
      (B.inclusion.map g.unop).appTop.hom.comp
        (B.inclusion.map f.unop).appTop.hom := by
    have hr := congrArg (fun q => q.appTop.hom) hmap
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hr
  exact congrArg (fun q => q (e.1.1 i j)) hring

private def actionGroupoidPresheaf (B : BigFppfSite.{u})
    {d : ℕ} [NeZero d] (laws : ConjugationPreservesAlgebraLaws.{u} d) :
    ActionGroupoidPresheaf B d laws where
  action_one := conjugationOnPointsOf_one (representation.{u} d) laws
  action_mul := conjugationOnPointsOf_mul (representation.{u} d) laws
  action_naturality := conjugationOnPointsOf_natural (representation.{u} d) laws
  groupoid T := actionPointGroupoid (representation.{u} d) laws T.unop.1
  pullback f := actionPullback (representation.{u} d) laws f
  pullback_obj _ _ := rfl
  arrowEquiv T x y := Equiv.refl _
  arrowEquiv_id _ _ := rfl
  arrowEquiv_comp := by
    intro T x y z f g
    rfl
  pullback_id := actionPullback_id (representation.{u} d) laws
  pullback_comp := actionPullback_comp (representation.{u} d) laws
  pullback_arrow := by
    intro T U f x y e
    apply Subtype.ext
    rfl

private abbrev canonicalActionGroupoid (B : BigFppfSite.{u}) (d : ℕ) [NeZero d] :
    ActionGroupoidPresheaf B d (conjugationPreservesAlgebraLaws_aux (d := d)) :=
  actionGroupoidPresheaf B conjugationPreservesAlgebraLaws_aux

private def pointGroupoidForward {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (F : Presheaf B d) (T : B.Schemesᵒᵖ) :
    @CategoryTheory.Functor (F.functor.obj T) (Grpd.str' (F.functor.obj T)).toCategory
      (SchemePointMor T.unop.1 (scheme.{u} d))
      (actionPointGroupoid rep laws T.unop.1).toCategory := by
  letI instF : Groupoid (F.functor.obj T) := Grpd.str' (F.functor.obj T)
  let E := pointEquiv rep F T
  letI instP : Groupoid (SchemePointMor T.unop.1
      (scheme.{u} d)) := actionPointGroupoid rep laws T.unop.1
  letI : Category (SchemePointMor T.unop.1
    (scheme.{u} d)) := instP.toCategory
  exact {
    obj := E
    map := fun {x y} (e : @Quiver.Hom _
        (Grpd.str' (F.functor.obj T)).toCategory.toQuiver x y) =>
      freePointArrowEquiv rep laws F T x y e
    map_id := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      calc
        _ = (F.arrowEquiv T x x (𝟙 x)).matrix⁻¹ := freePointArrowEquiv_matrix _ _ _ _ _ _ _
        _ = 1 := by simp [F.arrowEquiv_id]
        _ = (𝟙 (E x) : @Quiver.Hom _
            (actionPointGroupoid rep laws T.unop.1).toCategory.toQuiver (E x) (E x)).1.1 := by
          rw [actionPointGroupoid_id_matrix rep laws T.unop.1]
    map_comp := by
      intro x y z f g
      apply Subtype.ext
      apply Subtype.ext
      let qf := freePointArrowEquiv rep laws F T x y f
      let qg := freePointArrowEquiv rep laws F T y z g
      let qcomp := @CategoryStruct.comp _ instP.toCategory.toCategoryStruct
        (E x) (E y) (E z) qf qg
      calc
        _ = (F.arrowEquiv T x z (f ≫ g)).matrix⁻¹ :=
          freePointArrowEquiv_matrix _ _ _ _ _ _ _
        _ = (F.arrowEquiv T x y f).matrix⁻¹ *
            (F.arrowEquiv T y z g).matrix⁻¹ := by
          rw [F.arrowEquiv_comp, mul_inv_rev]
        _ = ((freePointArrowEquiv rep laws F T x y f).1).1 *
            ((freePointArrowEquiv rep laws F T y z g).1).1 := by
          rw [freePointArrowEquiv_matrix, freePointArrowEquiv_matrix]
        _ = qcomp.1.1 := by
          rw [actionPointGroupoid_comp_matrix rep laws T.unop.1 qf qg]
  }

private def pointGroupoidBackward {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (F : Presheaf B d) (T : B.Schemesᵒᵖ) :
    @CategoryTheory.Functor (SchemePointMor T.unop.1 (scheme.{u} d))
      (actionPointGroupoid rep laws T.unop.1).toCategory
      (F.functor.obj T) (Grpd.str' (F.functor.obj T)).toCategory := by
  letI instF : Groupoid (F.functor.obj T) := Grpd.str' (F.functor.obj T)
  let E := pointEquiv rep F T
  letI instP : Groupoid (SchemePointMor T.unop.1
      (scheme.{u} d)) := actionPointGroupoid rep laws T.unop.1
  letI : Category (SchemePointMor T.unop.1
    (scheme.{u} d)) := instP.toCategory
  exact {
    obj := E.symm
    map := fun {x y} (e : @Quiver.Hom _
        (actionPointGroupoid rep laws T.unop.1).toCategory.toQuiver x y) =>
      let q : {g : UnitFixingMatrix Γ(T.unop.1, ⊤) d //
          conjugationOnPointsOf rep laws T.unop.1 g
            (pointEquiv rep F T (E.symm x)) = pointEquiv rep F T (E.symm y)} :=
        ⟨e.1, by simpa [E] using e.2⟩
      (freePointArrowEquiv rep laws F T (E.symm x) (E.symm y)).symm q
    map_id := by
      intro x
      apply (F.arrowEquiv T (E.symm x) (E.symm x)).injective
      apply StructureIso.ext
      simp [freePointArrowEquiv, algebraActionArrowEquiv, F.arrowEquiv_id,
        actionPointGroupoid_id_matrix]
    map_comp := by
      intro x y z f g
      apply (F.arrowEquiv T (E.symm x) (E.symm z)).injective
      apply StructureIso.ext
      simp [freePointArrowEquiv, algebraActionArrowEquiv,
        F.arrowEquiv_comp, mul_inv_rev, actionPointGroupoid_comp_matrix]
  }

private lemma freePoint_eqToHom_comp_matrix {B : BigFppfSite.{u}} {d : ℕ}
    [NeZero d] (F : Presheaf B d) (T : B.Schemesᵒᵖ)
    {x x' y y' : F.functor.obj T} (hx : x = x') (hy : y = y')
    (e : @Quiver.Hom _ (Grpd.str' (F.functor.obj T)).toCategory.toQuiver x' y') :
    (F.arrowEquiv T x y (eqToHom hx ≫ e ≫ eqToHom hy.symm)).matrix =
      (F.arrowEquiv T x' y' e).matrix := by
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private def pointGroupoidIso {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d)
    (F : Presheaf B d) (T : B.Schemesᵒᵖ) :
    F.functor.obj T ≅ @Grpd.of (SchemePointMor T.unop.1
      (scheme.{u} d)) (actionPointGroupoid rep laws T.unop.1) where
  hom := pointGroupoidForward rep laws F T
  inv := pointGroupoidBackward rep laws F T
  hom_inv_id := by
    let : Category (SchemePointMor T.unop.1
      (scheme.{u} d)) :=
        (actionPointGroupoid rep laws T.unop.1).toCategory
    change pointGroupoidForward rep laws F T ⋙ pointGroupoidBackward rep laws F T = 𝟭 _
    have hobj (x : F.functor.obj T) :
        (pointGroupoidForward rep laws F T ⋙ pointGroupoidBackward rep laws F T).obj x =
          (𝟭 (F.functor.obj T)).obj x := by
      simp [pointGroupoidForward, pointGroupoidBackward]
    refine CategoryTheory.Functor.ext hobj (by
      intro x y e
      let xx := (pointGroupoidForward rep laws F T ⋙ pointGroupoidBackward rep laws F T).obj x
      let yy := (pointGroupoidForward rep laws F T ⋙ pointGroupoidBackward rep laws F T).obj y
      apply (F.arrowEquiv T xx yy).injective
      apply StructureIso.ext
      simp only [Functor.comp_obj, Functor.comp_map, pointGroupoidForward,
        pointGroupoidBackward, xx, yy]
      change (F.arrowEquiv T
        ((pointEquiv rep F T).symm ((pointEquiv rep F T) x))
        ((pointEquiv rep F T).symm ((pointEquiv rep F T) y))
        ((freePointArrowEquiv rep laws F T
          ((pointEquiv rep F T).symm ((pointEquiv rep F T) x))
          ((pointEquiv rep F T).symm ((pointEquiv rep F T) y))).symm
          ⟨(freePointArrowEquiv rep laws F T x y e).1, by
            simpa using (freePointArrowEquiv rep laws F T x y e).2⟩)).matrix = _
      rw [freePointArrowEquiv_symm_matrix]
      rw [freePointArrowEquiv_matrix]
      simpa only [inv_inv, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
        Functor.id_map, pointGroupoidForward, pointGroupoidBackward] using
          (freePoint_eqToHom_comp_matrix F T (hobj x) (hobj y) e).symm)
  inv_hom_id := by
    let : Category (SchemePointMor T.unop.1
      (scheme.{u} d)) :=
        (actionPointGroupoid rep laws T.unop.1).toCategory
    change pointGroupoidBackward rep laws F T ⋙ pointGroupoidForward rep laws F T = 𝟭 _
    have hobj (x : SchemePointMor T.unop.1
        (scheme.{u} d)) :
        (pointGroupoidBackward rep laws F T ⋙ pointGroupoidForward rep laws F T).obj x = x := by
      simp [pointGroupoidForward, pointGroupoidBackward]
    refine CategoryTheory.Functor.ext hobj fun x y e => ?_
    refine actionPointGroupoid_map_eq rep laws T.unop.1 (hobj x) (hobj y) _ _ ?_
    simp only [Functor.comp_map]
    ext i j
    simp [pointGroupoidForward, pointGroupoidBackward,
      freePointArrowEquiv, algebraActionArrowEquiv, Equiv.apply_symm_apply]

/-- The action-groupoid functor attached to an identification of the points of the scheme of
structure constants with free algebra structures. -/
private def actionGroupoidFunctor {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (laws : ConjugationPreservesAlgebraLaws.{u} d) :
    B.Schemesᵒᵖ ⥤ Grpd.{u, u} where
  obj T := @Grpd.of (T.unop.1 ⟶ scheme.{u} d) (actionPointGroupoid rep laws T.unop.1)
  map f := actionPullback rep laws f
  map_id := actionPullback_id rep laws
  map_comp := actionPullback_comp rep laws

private def pointGroupoidNaturalIso {B : BigFppfSite.{u}} {d : ℕ} [NeZero d]
    (rep : Representation.{u} d) (F : Presheaf B d) :
    F.functor ≅ actionGroupoidFunctor rep (conjugationPreservesAlgebraLaws_aux (d := d)) := by
  refine NatIso.ofComponents (fun T => pointGroupoidIso rep
    (conjugationPreservesAlgebraLaws_aux (d := d)) F T) ?_
  intro T U f
  let E := pointEquiv rep F T
  let E' := pointEquiv rep F U
  let : Groupoid (F.functor.obj T) := Grpd.str' (F.functor.obj T)
  let : Groupoid (F.functor.obj U) := Grpd.str' (F.functor.obj U)
  let laws := conjugationPreservesAlgebraLaws_aux (d := d)
  let instT : Groupoid (SchemePointMor T.unop.1 (scheme.{u} d)) :=
    actionPointGroupoid rep laws T.unop.1
  let instU : Groupoid (SchemePointMor U.unop.1 (scheme.{u} d)) :=
    actionPointGroupoid rep laws U.unop.1
  let : Category (SchemePointMor T.unop.1
    (scheme.{u} d)) := instT.toCategory
  let : Category (SchemePointMor U.unop.1
    (scheme.{u} d)) := instU.toCategory
  have hobj (x : F.functor.obj T) :
      (F.functor.map f ⋙ pointGroupoidForward rep laws F U).obj x =
      (pointGroupoidForward rep laws F T ⋙ actionPullback rep laws f).obj x := by
      change E' ((F.functor.map f).obj x) =
        (actionPullback rep laws f).obj (E x)
      simp [actionPullback, E, E', pointEquiv_map]
  refine CategoryTheory.Functor.ext hobj fun x y e =>
    actionPointGroupoid_map_eq rep laws U.unop.1 (by exact hobj _) (by exact hobj _) _ _ ?_
  ext i j
  change (freePointArrowEquiv rep laws F U ((F.functor.map f).obj x)
      ((F.functor.map f).obj y) ((F.functor.map f).map e)).1.1.1 i j =
    (UnitFixingMatrix.map (B.inclusion.map f.unop).appTop.hom
      (freePointArrowEquiv rep laws F T x y e).1).1.1 i j
  exact congrArg (fun M : Matrix (Fin d) (Fin d) Γ(U.unop.1, ⊤) => M i j)
    (freePointArrowEquiv_map_matrix rep laws F f x y e)

/-- Conjugation defines an action on the scheme of structure constants, and `FA_d` is
naturally isomorphic to its action-groupoid functor, by the representing equivalence on objects
and the inverse matrices on arrows. -/
@[stacks 05YP]
public theorem presheaf_actionGroupoid
    (B : BigFppfSite.{u}) (d : ℕ) [NeZero d]
    (F : Presheaf B d) :
    ∃ (laws : ConjugationPreservesAlgebraLaws.{u} d)
      (P : ActionGroupoidPresheaf B d laws)
      (η : F.functor ≅ P.toFunctor),
      (∀ (T : B.Schemesᵒᵖ) (x : F.functor.obj T),
        (η.hom.app T).obj x =
          ((representation.{u} d).equiv T.unop.1).symm
            (F.objectEquiv T x)) ∧
      (∀ (T : B.Schemesᵒᵖ) (x y : F.functor.obj T) (e : x ⟶ y),
        (P.arrowEquiv T _ _ ((η.hom.app T).map e)).1.1 =
          (F.arrowEquiv T x y e).matrix⁻¹) := by
  refine ⟨conjugationPreservesAlgebraLaws_aux, ?_⟩
  refine ⟨canonicalActionGroupoid B d, pointGroupoidNaturalIso (representation.{u} d) F, ?_⟩
  constructor
  · intro T x
    show (pointGroupoidIso (representation.{u} d)
      (conjugationPreservesAlgebraLaws_aux (d := d)) F T).hom.obj x = _
    rfl
  · intro T x y e
    show ((freePointArrowEquiv (representation.{u} d)
      (conjugationPreservesAlgebraLaws_aux (d := d)) F T x y e).1).1 = _
    exact freePointArrowEquiv_matrix _ _ _ _ _ _ _

/-- Conjugation by a unit-fixing matrix preserves the associativity, commutativity and unit
relations defining the scheme of structure constants, so it acts on free `d`-dimensional algebra
structures. -/
public alias conjugationPreservesAlgebraLaws := conjugationPreservesAlgebraLaws_aux

/-- The identity matrix acts as the identity on the points of the scheme of structure
constants. -/
public theorem conjugationOnPoints_one {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u}) (x : T ⟶ scheme.{u} d) :
    conjugationOnPoints laws T 1 x = x :=
  conjugationOnPointsOf_one (representation.{u} d) laws T x

/-- Conjugation is a right action on the points of the scheme of structure constants: in the
column-matrix convention the first matrix acts first. -/
public theorem conjugationOnPoints_mul {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})
    (g h : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    conjugationOnPoints laws T (g * h) x =
      conjugationOnPoints laws T h (conjugationOnPoints laws T g x) :=
  conjugationOnPointsOf_mul (representation.{u} d) laws T g h x

/-- Conjugation commutes with base change, so it is an action of the functor of points of the
unit-fixing group on the functor of points of the scheme of structure constants. -/
public theorem conjugationOnPoints_naturality {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) {T U : Scheme.{u}} (f : T ⟶ U)
    (g : UnitFixingMatrix Γ(U, ⊤) d) (x : U ⟶ scheme.{u} d) :
    conjugationOnPoints laws T (g.map f.appTop.hom) (f ≫ x) =
      f ≫ conjugationOnPoints laws U g x :=
  conjugationOnPointsOf_natural (representation.{u} d) laws f g x

end AlgebraicGeometry.FiniteFreeAlgebra

end
