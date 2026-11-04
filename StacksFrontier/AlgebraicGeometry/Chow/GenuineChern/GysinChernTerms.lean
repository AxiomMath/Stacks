module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.GysinFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FlatPullbackChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleGysin
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ZeroSchemeCartesianSquare

/-!
# The summands of the relation of Stacks 02U6 commute with Gysin pullback

Let `π : P ⟶ X` be flat of relative dimension `r - 1` with `r = n + 1`, let `𝒪(1)` be an
invertible module on `P`, and let `(ℒ, s, i : D ⟶ X)` be a triple as in Definition 02T8. The zero
scheme of `π^*s` is `P_D = Z(π^*s) ⊆ P`, with the morphism `π_D : P_D ⟶ D` of Remark 0B6Y, and the
Gysin map of `(π^*ℒ, π^*s)` is `(i')^* : A_{m+1}(P) ⟶ A_m(P_D)`.

`Stacks.Chow.isChernCapFamily_gysin` is [Stacks, Tag 0B7G] for these data, given the hypothesis
`Stacks.Chow.ChernTermsCompatibleWithGysin`: `(i')^*` carries each summand
`c₁(𝒪(1))^i ∩ π^*(-)` of the relation over `X` to the summand `c₁(𝒪(1)|_{P_D})^i ∩ π_D^*(-)` over
`D`, precomposed with `i^*`. This file proves that hypothesis, as in the source: by
[Stacks, Tag 0B71] for the flat morphism `π`
(`Stacks.Chow.gysinSystemOfInvertible_onChow_flatPullbackChow`) and `i` applications of
[Stacks, Tag 0B72] (`Stacks.Chow.GenuineChern.gysinChowOfInvertible_firstChernClassCapChow`).

## Main results

* `Stacks.Chow.GenuineChern.iteratedChernCapOnChow_heq_of_lowering` — iterated caps commute with a
  degree-lowering family of maps with which single caps commute.
* `Stacks.Chow.GenuineChern.chernTermsCompatibleWithGysin_of_invertible` — the compatibility
  hypothesis of Stacks 0B7G for the Gysin system of an invertible module.

## References

* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- A degree-lowering family of additive maps sends heterogeneously equal arguments in equal
degrees to heterogeneously equal images. -/
private theorem heq_apply_succ {P Z : Scheme.{u}} {sP : P ⟶ C.S} [LocallyOfFiniteType sP]
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
    (G : ∀ m : ℤ, chowGroup C sP (m + 1) →+ chowGroup C sZ m)
    {m₁ m₂ : ℤ} (h : m₁ = m₂) {a : chowGroup C sP (m₁ + 1)} {b : chowGroup C sP (m₂ + 1)}
    (hab : a ≍ b) : G m₁ a ≍ G m₂ b :=
  heq_apply_of_degree C sP sZ (fun m ↦ m + 1) (fun m ↦ m) G h hab

/-- **Iterated caps commute with a degree-lowering family** `G_m : A_{m+1}(P) ⟶ A_m(Z)` with which
single caps commute: if `G (c ∩ y) = c' ∩ G y` for one cap, then
`G (c^n ∩ y) = c'^n ∩ G y`. -/
theorem iteratedChernCapOnChow_heq_of_lowering {P Z : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (G : ∀ m : ℤ, chowGroup C sP (m + 1) →+ chowGroup C sZ m)
    (OP : ChernCapOperator C sP) (OZ : ChernCapOperator C sZ)
    (hξ : ∀ (e : ℤ) (y : chowGroup C sP (e + 1 + 1)) (y' : chowGroup C sZ (e + 1)),
      y' ≍ G (e + 1) y → G e (OP.capOnChow C sP (e + 1) y) ≍ OZ.capOnChow C sZ e y')
    (n : ℕ) (e : ℤ) (y : chowGroup C sP (e + 1 + ((List.replicate n OP).length : ℤ)))
    (y' : chowGroup C sZ (e + ((List.replicate n OZ).length : ℤ)))
    (hy : ∀ z : chowGroup C sP (e + ((List.replicate n OZ).length : ℤ) + 1), z ≍ y →
      y' ≍ G _ z) :
    G e (iteratedChernCapOnChow C sP (List.replicate n OP) (e + 1) y) ≍
      iteratedChernCapOnChow C sZ (List.replicate n OZ) e y' := by
  induction n generalizing e with
  | zero =>
    refine HEq.trans ?_ (iteratedChernCapOnChow_replicate_zero_heq C sZ OZ e y').symm
    refine (heq_apply_succ C G (m₂ := e + ((List.replicate 0 OZ).length : ℤ)) (by simp)
      ((iteratedChernCapOnChow_replicate_zero_heq C sP OP (e + 1) y).trans
        (chowGroupCast_heq C sP (by simp) y).symm)).trans ?_
    exact (hy _ (chowGroupCast_heq C sP _ y)).symm
  | succ n ih =>
    rw [iteratedChernCapOnChow_replicate_succ_heq C sP OP n (e + 1) y
      (chowGroupCast C sP (by simp; ring) y) (chowGroupCast_heq C sP _ y).symm,
      iteratedChernCapOnChow_replicate_succ_heq C sZ OZ n e y'
      (chowGroupCast C sZ (by simp; ring) y') (chowGroupCast_heq C sZ _ y').symm]
    refine hξ e _ _ (ih (e + 1) _ _ fun z hz ↦ ?_).symm
    refine (chowGroupCast_heq C sZ _ y').trans ((hy (chowGroupCast C sP (by simp; ring) z)
      ((chowGroupCast_heq C sP _ z).trans (hz.trans (chowGroupCast_heq C sP _ y)))).trans ?_)
    exact heq_apply_succ C G (by simp; ring) (chowGroupCast_heq C sP _ z)

/-- Transport along an equality of degrees is heterogeneously the identity. -/
theorem chowGroupDegreeEquiv_heq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    {d e : ℤ} (h : d = e) (x : chowGroup C sP d) : chowGroupDegreeEquiv C sP h x ≍ x := by
  subst h; rfl

variable {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (π : P ⟶ X)
  [LocallyOfFiniteType π] [Flat π] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (n + 1 - 1))
  (O : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property O]

/-- **The compatibility hypothesis of Stacks 0B7G, for the Gysin map of an invertible module.**
Gysin pullback along `i' : Z(π^*s) ⟶ P` carries the summand `c₁(𝒪)^i ∩ π^*(-)` of the relation
over `X` to the summand `c₁(𝒪|_{Z(π^*s)})^i ∩ π_D^*(-)` over `D = Z(s)`, precomposed with the
Gysin pullback along `i`: Stacks 0B71 for `π` followed by `i` applications of Stacks 0B72. -/
theorem chernTermsCompatibleWithGysin_of_invertible :
    ChernTermsCompatibleWithGysin C sX (π ≫ sX) π rfl L s ((Scheme.Modules.pullback π).obj L)
      (AlgebraicGeometry.pullbackGlobalSections π L s) (zeroSchemePullbackHom π L s)
      (zeroSchemePullbackHom_comp π L s C sX (π ≫ sX) rfl) (n + 1) hπ
      (relativeDimension_zeroSchemePullbackHom π L s (n + 1 - 1) hπ)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ k)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ k)
      (invertibleChernCapOperator C (π ≫ sX) O fun k ↦
        firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k _ O)
      (invertibleChernCapOperator C ((pullbackZeroScheme π L s).subschemeι ≫ π ≫ sX)
        ((Scheme.Modules.pullback (pullbackZeroScheme π L s).subschemeι).obj O) fun k ↦
        firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k _ _)
      (fun k ↦ gysinOfInvertibleDescends C sX L s k)
      (fun k ↦ gysinOfInvertibleDescends C (π ≫ sX) _ _ k) := by
  intro k i hi x
  set Z := pullbackZeroScheme π L s with hZ
  set OP := invertibleChernCapOperator C (π ≫ sX) O fun k ↦
    firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k _ O
    with hOP
  set OZ := invertibleChernCapOperator C (Z.subschemeι ≫ π ≫ sX)
    ((Scheme.Modules.pullback Z.subschemeι).obj O) (fun k ↦
      firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k _ _)
    with hOZ
  set G : ∀ m : ℤ, chowGroup C (π ≫ sX) (m + 1) →+ chowGroup C (Z.subschemeι ≫ π ≫ sX) m :=
    fun m ↦ gysinChowOfInvertible C (π ≫ sX) m ((Scheme.Modules.pullback π).obj L)
      (AlgebraicGeometry.pullbackGlobalSections π L s) with hGdef
  -- Stacks 0B72 for one cap
  have hξ : ∀ (e : ℤ) (y : chowGroup C (π ≫ sX) (e + 1 + 1))
      (y' : chowGroup C (Z.subschemeι ≫ π ≫ sX) (e + 1)), y' ≍ G (e + 1) y →
      G e (OP.capOnChow C (π ≫ sX) (e + 1) y) ≍ OZ.capOnChow C (Z.subschemeι ≫ π ≫ sX) e y' := by
    intro e y y' hy
    obtain rfl := eq_of_heq hy
    exact heq_of_eq (gysinChowOfInvertible_firstChernClassCapChow C (π ≫ sX) e
      ((Scheme.Modules.pullback π).obj L) (AlgebraicGeometry.pullbackGlobalSections π L s) O y)
  refine chowGroup_eq_of_heq C _ ?_
  simp only [projectiveBundleChernTerm, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, projectiveBundlePullback]
  refine HEq.trans ?_ (iteratedChernCapOnChow_heq_of_lowering C (π ≫ sX) (Z.subschemeι ≫ π ≫ sX)
    G OP OZ hξ i (k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) (chowGroupCast C _ (by simp; omega)
      (flatPullbackChow C (π ≫ sX) sX π rfl (n + 1 - 1) hπ (k + 1 - ((n + 1 - i : ℕ) : ℤ))
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) x)) _ ?_)
  · refine heq_apply_succ C G (by omega) ?_
    refine (chowGroupCast_heq C _ _ _).trans (iteratedChernCapOnChow_heq C _ _ (by omega) ?_)
    exact (chowGroupCast_heq C _ _ _).trans (chowGroupCast_heq C _ _ _).symm
  · intro z hz
    refine (chowGroupCast_heq C _ _ _).trans ?_
    have h0B71 := gysinSystemOfInvertible_onChow_flatPullbackChow C sX π (n + 1 - 1) hπ
      (k - ((n + 1 - i : ℕ) : ℤ)) L s (π ≫ sX) rfl
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (zeroSchemePullbackHom_comp π L s C sX (π ≫ sX) rfl)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (chowGroupCast C sX
        (show k + 1 - ((n + 1 - i : ℕ) : ℤ) = k - ((n + 1 - i : ℕ) : ℤ) + 1 by omega) x)
    refine HEq.trans (heq_of_eq h0B71.symm) ?_
    refine heq_apply_succ C G (by simp only [List.length_replicate]; omega) ?_
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    refine HEq.trans ?_ hz.symm
    refine HEq.trans ?_ (chowGroupCast_heq C _ _ _).symm
    exact flatPullbackChow_heq C (π ≫ sX) sX π rfl (n + 1 - 1) hπ
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ k) (by omega)
      (chowGroupCast_heq C sX _ x)

end Stacks.Chow.GenuineChern

end
