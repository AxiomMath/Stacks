module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Segre

/-!
# Iterated first Chern class caps: peeling off the innermost cap, and closed pushforward

`Stacks.Chow.iteratedChernCapOnChow` applies a list of first Chern class cap operators with the
head of the list applied last. For a constant list the innermost operator can be peeled off just
as well, and an iterated cap commutes with proper pushforward along a morphism whenever each
single cap does. These are the two manipulations the additivity of the first Chern class needs.

## Main results

* `Stacks.Chow.iteratedChernCapOnChow_replicate_succ` — `ξ^{n+1} = ξ^n ∘ ξ`.
* `Stacks.Chow.properChowPushforward_iteratedChernCapOnChow` — `ι_* ∘ ξ_Q^n = ξ_G^n ∘ ι_*`
  when `ι_* ∘ ξ_Q = ξ_G ∘ ι_*`.
* `Stacks.Chow.properChowPushforward_properChowPushforward` — proper pushforward on Chow groups
  is functorial (Stacks 02R5 on classes).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-! ### Transport, read as heterogeneous equality -/

/-- A transported class is heterogeneously equal to the original. -/
theorem chowGroupCast_heq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP] {d e : ℤ}
    (h : d = e) (x : chowGroup C sP d) : chowGroupCast C sP h x ≍ x := by
  subst h; rfl

/-- Heterogeneously equal arguments in equal degrees have heterogeneously equal images under a
degree-indexed family of additive maps. -/
theorem heq_apply_of_degree {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (g h : ℤ → ℤ)
    (F : ∀ d : ℤ, chowGroup C p (g d) →+ chowGroup C q (h d)) {d₁ d₂ : ℤ} (hd : d₁ = d₂)
    {x : chowGroup C p (g d₁)} {y : chowGroup C p (g d₂)} (hxy : x ≍ y) : F d₁ x ≍ F d₂ y := by
  subst hd; cases hxy; rfl

/-- Two elements of one Chow group are equal once heterogeneously equal. -/
theorem chowGroup_eq_of_heq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP] {d : ℤ}
    {x y : chowGroup C sP d} (h : x ≍ y) : x = y := eq_of_heq h

/-- A single cap operator, at heterogeneously equal arguments in equal degrees. -/
theorem capOnChow_heq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (O : ChernCapOperator C sP) {d₁ d₂ : ℤ} (hd : d₁ = d₂) {x : chowGroup C sP (d₁ + 1)}
    {y : chowGroup C sP (d₂ + 1)} (hxy : x ≍ y) :
    O.capOnChow C sP d₁ x ≍ O.capOnChow C sP d₂ y :=
  heq_apply_of_degree C sP sP (fun d => d + 1) (fun d => d) (fun d => O.capOnChow C sP d) hd hxy

/-- An iterated cap, at heterogeneously equal arguments in equal degrees. -/
theorem iteratedChernCapOnChow_heq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (Os : List (ChernCapOperator C sP)) {d₁ d₂ : ℤ} (hd : d₁ = d₂)
    {x : chowGroup C sP (d₁ + (Os.length : ℤ))} {y : chowGroup C sP (d₂ + (Os.length : ℤ))}
    (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP Os d₁ x ≍ iteratedChernCapOnChow C sP Os d₂ y :=
  heq_apply_of_degree C sP sP (fun d => d + (Os.length : ℤ)) (fun d => d)
    (fun d => iteratedChernCapOnChow C sP Os d) hd hxy

/-- Iterated caps at two lists that are equal, at heterogeneously equal arguments. -/
theorem iteratedChernCapOnChow_heq_of_eq {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] {Os Os' : List (ChernCapOperator C sP)} (hO : Os = Os') (d : ℤ)
    {x : chowGroup C sP (d + (Os.length : ℤ))} {y : chowGroup C sP (d + (Os'.length : ℤ))}
    (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP Os d x ≍ iteratedChernCapOnChow C sP Os' d y := by
  subst hO; cases hxy; rfl

/-- Proper pushforward, at heterogeneously equal arguments in equal degrees. -/
theorem properChowPushforward_heq {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)
    {d₁ d₂ : ℤ} (hd : d₁ = d₂) {x : chowGroup C sX d₁} {y : chowGroup C sX d₂} (hxy : x ≍ y) :
    properChowPushforward C sX sY p hp d₁
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp d₁) x ≍
      properChowPushforward C sX sY p hp d₂
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp d₂) y :=
  heq_apply_of_degree C sX sY (fun d => d) (fun d => d)
    (fun d => properChowPushforward C sX sY p hp d
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp d)) hd hxy

/-- The defining equation of an iterated cap at a constant list of positive length: the head
is applied last. -/
theorem iteratedChernCapOnChow_replicate_succ_heq {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (O : ChernCapOperator C sP) (n : ℕ) (d : ℤ)
    (x : chowGroup C sP (d + ((List.replicate (n + 1) O).length : ℤ)))
    (y : chowGroup C sP (d + 1 + ((List.replicate n O).length : ℤ))) (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP (List.replicate (n + 1) O) d x =
      O.capOnChow C sP d (iteratedChernCapOnChow C sP (List.replicate n O) (d + 1) y) := by
  change chowGroupDegreeCast C sP _ ((O.capOnChow C sP d).comp
    (iteratedChernCapOnChow C sP (List.replicate n O) (d + 1))) x = _
  rw [chowGroupDegreeCast_apply]
  change O.capOnChow C sP d (iteratedChernCapOnChow C sP (List.replicate n O) (d + 1) _) = _
  congr 2
  exact chowGroup_eq_of_heq C sP ((chowGroupCast_heq C sP _ x).trans hxy)

/-- The defining equation of an iterated cap at a constant list of positive length, with the
argument transported to the degree `d + 1 + n`. -/
private theorem iteratedChernCapOnChow_replicate_succ_cast {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (O : ChernCapOperator C sP) (n : ℕ) (d : ℤ)
    (x : chowGroup C sP (d + ((List.replicate (n + 1) O).length : ℤ))) :
    iteratedChernCapOnChow C sP (List.replicate (n + 1) O) d x =
      O.capOnChow C sP d (iteratedChernCapOnChow C sP (List.replicate n O) (d + 1)
        (chowGroupCast C sP (by simp; ring) x)) :=
  iteratedChernCapOnChow_replicate_succ_heq C sP O n d x _ (chowGroupCast_heq C sP _ x).symm

/-- An iterated cap at the empty list is heterogeneously the identity. -/
theorem iteratedChernCapOnChow_replicate_zero_heq {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (O : ChernCapOperator C sP) (d : ℤ)
    (x : chowGroup C sP (d + ((List.replicate 0 O).length : ℤ))) :
    iteratedChernCapOnChow C sP (List.replicate 0 O) d x ≍ x := by
  change chowGroupDegreeCast C sP _ (AddMonoidHom.id _) x ≍ x
  rw [chowGroupDegreeCast_apply]
  exact chowGroupCast_heq C sP _ x

/-- **Peeling off the innermost cap.** `ξ^{n+1}(y) = ξ^n(ξ(y))`, heterogeneously. -/
theorem iteratedChernCapOnChow_replicate_succ_heq' {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (O : ChernCapOperator C sP) (n : ℕ) (d : ℤ)
    (x : chowGroup C sP (d + ((List.replicate (n + 1) O).length : ℤ)))
    (y : chowGroup C sP (d + (n : ℤ) + 1)) (hxy : x ≍ y)
    (z : chowGroup C sP (d + ((List.replicate n O).length : ℤ)))
    (hz : z ≍ O.capOnChow C sP (d + (n : ℤ)) y) :
    iteratedChernCapOnChow C sP (List.replicate (n + 1) O) d x =
      iteratedChernCapOnChow C sP (List.replicate n O) d z := by
  induction n generalizing d with
  | zero =>
    rw [iteratedChernCapOnChow_replicate_succ_cast C sP O 0 d x]
    refine chowGroup_eq_of_heq C sP ?_
    refine HEq.trans ?_ (iteratedChernCapOnChow_replicate_zero_heq C sP O d z).symm
    refine HEq.trans ?_ hz.symm
    refine capOnChow_heq C sP O (by simp) ?_
    exact (iteratedChernCapOnChow_replicate_zero_heq C sP O _ _).trans
      ((chowGroupCast_heq C sP _ x).trans hxy)
  | succ n ih =>
    rw [iteratedChernCapOnChow_replicate_succ_cast C sP O (n + 1) d x,
      iteratedChernCapOnChow_replicate_succ_cast C sP O n d z]
    congr 1
    refine ih (d + 1) _ (chowGroupCast C sP (by push_cast; ring) y)
      ((chowGroupCast_heq C sP _ x).trans (hxy.trans (chowGroupCast_heq C sP _ y).symm)) _ ?_
    refine (chowGroupCast_heq C sP _ z).trans (hz.trans ?_)
    exact capOnChow_heq C sP O (by push_cast; ring) (chowGroupCast_heq C sP _ y).symm

/-- **Proper pushforward on Chow groups is functorial** (Stacks 02R5, read on classes). -/
theorem properChowPushforward_properChowPushforward {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ) (x : chowGroup C sX k) :
    properChowPushforward C sY sZ g hg k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sY sZ g hg k)
        (properChowPushforward C sX sY f hf k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY f hf k) x) =
      properChowPushforward C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sZ (f ≫ g)
          (by rw [Category.assoc, hg, hf]) k) x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    simp only [properChowPushforward]
    exact congrArg _ (properPushforward_properPushforward C sX sY sZ f g hf hg k c)

/-- **Iterated caps commute with proper pushforward** along a morphism with which the single
caps commute. -/
theorem properChowPushforward_iteratedChernCapOnChow {PQ PG : Scheme.{u}} (sPQ : PQ ⟶ C.S)
    [LocallyOfFiniteType sPQ] (sPG : PG ⟶ C.S) [LocallyOfFiniteType sPG] (ι : PQ ⟶ PG)
    [IsProper ι] (hι : ι ≫ sPG = sPQ) (OQ : ChernCapOperator C sPQ)
    (OG : ChernCapOperator C sPG)
    (hcap : ∀ (d : ℤ) (y : chowGroup C sPQ (d + 1)),
      properChowPushforward C sPQ sPG ι hι d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d)
          (OQ.capOnChow C sPQ d y) =
        OG.capOnChow C sPG d (properChowPushforward C sPQ sPG ι hι (d + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _) y))
    (n : ℕ) (d : ℤ) (y : chowGroup C sPQ (d + ((List.replicate n OQ).length : ℤ)))
    (y' : chowGroup C sPG (d + ((List.replicate n OG).length : ℤ)))
    (hy : y' ≍ properChowPushforward C sPQ sPG ι hι _
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _) y) :
    properChowPushforward C sPQ sPG ι hι d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d)
        (iteratedChernCapOnChow C sPQ (List.replicate n OQ) d y) =
      iteratedChernCapOnChow C sPG (List.replicate n OG) d y' := by
  induction n generalizing d with
  | zero =>
    refine chowGroup_eq_of_heq C sPG ?_
    refine HEq.trans ?_ (iteratedChernCapOnChow_replicate_zero_heq C sPG OG d y').symm
    refine HEq.trans ?_ hy.symm
    exact properChowPushforward_heq C sPQ sPG ι hι (by simp)
      (iteratedChernCapOnChow_replicate_zero_heq C sPQ OQ d y)
  | succ n ih =>
    rw [iteratedChernCapOnChow_replicate_succ_cast C sPQ OQ n d y,
      iteratedChernCapOnChow_replicate_succ_cast C sPG OG n d y', hcap]
    congr 1
    refine ih (d + 1) _ _ ((chowGroupCast_heq C sPG _ y').trans (hy.trans ?_))
    exact properChowPushforward_heq C sPQ sPG ι hι (by simp; ring)
      (chowGroupCast_heq C sPQ _ y).symm

end Stacks.Chow

end
