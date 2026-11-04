module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LargerClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExteriorProductIntersection

/-!
# The Gysin map of a morphism of smooth schemes, on classes `c ∩ [Y]`

Let `k` be a field and `f : X ⟶ Y` a morphism of schemes smooth over `k`. Its Gysin map
`f^! : CH^i(Y) ⟶ CH^i(X)` (Stacks 0FF3, `Stacks.Chow.codimensionGysin`) is formed on the pieces
`X_{d,e} = X_d ∩ f⁻¹(Y_e)`. On a piece, the two properties Stacks 0FF6 (`f^!` commutes with every
bivariant class) and Stacks 0FF7 (`f^![Y_e] = [X_{d,e}]`) determine it, because every class of
`CH_*(Y_e)` is `c ∩ [Y_e]` for some `c ∈ A^*(Y_e)` (Stacks 0FC2):

  `f^!(c ∩ [Y_e]) = res(c) ∩ [X_{d,e}]`.

This file records that formula and deduces from it that on a piece where `f` is flat of relative
dimension `t`, the Gysin map is flat pullback (Stacks 0FF4 in the form it is used).

## Main results

* `Stacks.Chow.dimPartPieceGysin_chowCohomologyCapFundamentalClass`:
  `f^!(c ∩ [Y_e]) = res(c) ∩ [X_{d,e}]` on the piece `X_{d,e}`.
* `Stacks.Chow.dimPartPieceGysin_heq_flatPullbackChow`: on a piece where `f` is flat of relative
  dimension `t`, `f^! = f^*`.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase fieldGysinSystem)


/-! ### Restriction of Chow cohomology classes -/

section Restriction

variable {C : ChowSituation.{u}}

/-- Transport along an equality of the structure morphism of the source is heterogeneously the
identity. -/
theorem bivariantClassCongrBase_heq_self {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB sB' : B ⟶ C.S}
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sB']
    {G : GysinSystem C} (v : A ⟶ B) [LocallyOfFiniteType v] (hsA : sA = sA') (hsB : sB = sB')
    {hv : v ≫ sB = sA} {hv' : v ≫ sB' = sA'} (p : ℤ) (c : BivariantClass C G sA sB v hv p) :
    bivariantClassCongrBase C G v hsA hsB (hv := hv) (hv' := hv') p c ≍ c := by
  subst hsA hsB
  rfl

/-- The operation on test schemes of a Chow cohomology class transported along an equality of
structure morphisms is the operation of the class. -/
theorem idRule_bivariantClassCongrBase_heq_of_bivariantClass {G : GysinSystem C} {Y : Scheme.{u}} {s
    s' : Y ⟶ C.S}
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (hs : s = s') (p : ℤ)
    (c : BivariantClass C G s s (𝟙 Y) (Category.id_comp s) p) {T : Scheme.{u}} (n : T ⟶ Y)
    [LocallyOfFiniteType n] (k : ℤ) (α : chowGroup C (n ≫ s') k) (α' : chowGroup C (n ≫ s) k)
    (hα : α ≍ α') :
    (bivariantClassCongrBase C G (𝟙 Y) hs hs (hv := Category.id_comp s)
        (hv' := Category.id_comp s') p c).idRule C s' G n k α ≍ c.idRule C s G n k α' := by
  subst hs
  cases hα
  rfl

/-- **Restriction is transitive**: restricting `c ∈ A^p(Y)` along `g : W ⟶ Y` and then along
`h : V ⟶ W` is restricting it along `h ≫ g`. -/
theorem chowCohomologyRestrictionOfEq_restrictionOfEq {Y W V : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (g : W ⟶ Y) [LocallyOfFiniteType g] (h : V ⟶ W)
    [LocallyOfFiniteType h] (hg : g ≫ sY = sW) (hh : h ≫ sW = sV) (hhg : (h ≫ g) ≫ sY = sV)
    (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    chowCohomologyRestrictionOfEq C sV sW hh (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p
        (chowCohomologyRestrictionOfEq C sW sY hg (gysinSystemOfInvertible C)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c) =
      chowCohomologyRestrictionOfEq C sV sY hhg (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c := by
  subst hg hh
  simp only [chowCohomologyRestrictionOfEq, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  refine eq_of_heq (HEq.trans ?_ (bivariantClassCongrBase_heq_self _ _ _ _ _).symm)
  refine (bivariantClassCongrBase_heq_self _ _ _ _ _).trans ?_
  exact chowCohomologyRestriction_chowCohomologyRestriction sY g h c

/-- Restriction along equal morphisms. -/
theorem chowCohomologyRestrictionOfEq_congr {Y W : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] {g g' : W ⟶ Y}
    [LocallyOfFiniteType g] [LocallyOfFiniteType g'] (hgg : g = g') (hg : g ≫ sY = sW)
    (hg' : g' ≫ sY = sW) (p : ℤ)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    chowCohomologyRestrictionOfEq C sW sY hg (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c =
      chowCohomologyRestrictionOfEq C sW sY hg' (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c := by
  subst hgg
  rfl

/-- **Restriction along the identity is the identity.** -/
theorem chowCohomologyRestrictionOfEq_id {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    chowCohomologyRestrictionOfEq C sY sY (Category.id_comp sY) (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c = c := by
  refine BivariantClass.eq_of_idRule_eq C sY _ _ _ fun {T} n _ k α ↦ ?_
  have h := chowCohomologyRestriction_idRule C sY (𝟙 Y) c n k
    (chowGroupCongr C (by rw [Category.id_comp]) k α)
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq h).trans ?_))
  · simp only [chowCohomologyRestrictionOfEq, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom]
    exact idRule_bivariantClassCongrBase_heq_of_bivariantClass (Category.id_comp sY) p _ n k α _
      (chowGroupCongr_heq _ _ _ _).symm
  · exact IdentityCapRule.heq_congr (op := c.idRule C sY (gysinSystemOfInvertible C))
      (hg := Category.comp_id n) (hk := rfl)
      (hα := (chowGroupCongr_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _))

/-- **`c ∩ [W]` restricts to `c ∩ [V]`** along an open immersion `j : V ⟶ W`, for a class
`res_g(c)` restricted from `Y`. -/
theorem chowGroupRestrict_capFundamentalClass_restrictionOfEq {Y W V : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (g : W ⟶ Y) [LocallyOfFiniteType g]
    (hg : g ≫ sY = sW) (j : V ⟶ W) [IsOpenImmersion j] (hj : j ≫ sW = sV) (N : ℤ)
    (hdim : schemeDeltaDimension C sW ≤ (N : EInt)) (p : ℤ)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    chowGroupRestrict C sW sV j hj (N - p)
        (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sW N p
          (chowCohomologyRestrictionOfEq C sW sY hg (gysinSystemOfInvertible C)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c)) =
      chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sV N p
        (chowCohomologyRestrictionOfEq C sV sY (f := j ≫ g) (by rw [Category.assoc, hg, hj])
          (gysinSystemOfInvertible C) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p
          c) := by
  rw [← chowCohomologyCap_fundamentalChowClass, ← chowCohomologyCap_fundamentalChowClass,
    chowGroupRestrict_chowCohomologyCap_restrictionOfEq C (gysinSystemOfInvertible C)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) sY sW sV p g hg j hj c N,
    chowGroupRestrict_fundamentalChowClass C sW sV j hj N hdim]

end Restriction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- Every class of `CH_{e-i}(Y_e)` is `c ∩ [Y_e]` for some `c ∈ A^i(Y_e)`. -/
private theorem exists_chowCohomologyCapFundamentalClass_eq {Z : Scheme.{u}}
    (s : Z ⟶ (fieldChowSituation k).S) [Smooth s] (e : ℕ) (i : ℤ)
    (β : chowGroup (fieldChowSituation k) (partBase s e) ((e : ℤ) - i)) :
    ∃ c, chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k)
      (partBase s e) e i c = β :=
  Stacks.WeilCohomology.capFundamentalClassSurjective k (partBase s e) e
    (relativeDimension_partBase s e) i β

/-- Restricting `c ∩ [Y_e]` along an open immersion `j : V ⟶ Y_e` gives `res_j(c) ∩ [V]`. -/
private theorem chowGroupRestrict_capFundamentalClass_partBase {V : Scheme.{u}}
    (sV : V ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sV] (e : ℕ)
    (j : V ⟶ (dimPart sY e).toScheme) [IsOpenImmersion j] (hj : j ≫ partBase sY e = sV) (i : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k) (gysinSystemOfInvertible _)
      (partBase sY e) i) :
    chowGroupRestrict (fieldChowSituation k) (partBase sY e) sV j hj ((e : ℤ) - i)
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (gysinSystemOfInvertible _)
          (partBase sY e) e i c) =
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (gysinSystemOfInvertible _) sV e i
        (chowCohomologyRestrictionOfEq (fieldChowSituation k) sV (partBase sY e) hj
          (gysinSystemOfInvertible _) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) i
          c) := by
  have h := chowGroupRestrict_capFundamentalClass_restrictionOfEq (partBase sY e) (partBase sY e)
    sV (𝟙 _) (Category.id_comp _) j hj e
    (Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension (partBase sY e)
      (relativeDimension_partBase sY e)) i c
  rw [chowCohomologyRestrictionOfEq_id] at h
  rw [h]
  congr 1

/-- **`f^!(c ∩ [Y_e]) = res(c) ∩ [X_{d,e}]`** on the piece `X_{d,e}`, by Stacks 0FF6 and
Stacks 0FF7 for the Gysin map of `f` restricted to the piece. -/
theorem dimPartPieceGysin_chowCohomologyCapFundamentalClass (d e : ℕ) (j : ℤ)
    (c : chowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) (partBase sY e) j) :
    dimPartPieceGysin sX sY hf d e j
        (chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k)
          (partBase sY e) e j c) ≍
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k)
        (dimPartPieceBase sX sY f d e) d j
        (chowCohomologyRestrictionOfEq (fieldChowSituation k) (dimPartPieceBase sX sY f d e)
          (partBase sY e) (dimPartPieceHom_comp_partBase sX sY hf d e) (fieldGysinSystem k)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) j c) :=
  (chowGroupDegreeEquiv_heq _ _ _ _).trans
    (BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq _ _
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) _ _ j
      (dimPartPieceHom_comp_partBase sX sY hf d e) ((e : ℤ) - d)
      (dimPartPieceGysinClass sX sY hf d e) c
      (dimPartPieceGysinClass_bivariantCommute sX sY hf d e j c) e
      (dimPartPieceGysinClass_capTargetHom_fundamentalChowClass sX sY hf d e) (by ring))

/-- **On a piece where `f` is flat, the Gysin map is flat pullback.** If the restriction
`f_{d,e} : X_{d,e} ⟶ Y_e` of `f` is flat of relative dimension `t`, with `t + e = d`, then
`f^!β = f_{d,e}^*β` for `β ∈ CH_{e-j}(Y_e)`. -/
theorem dimPartPieceGysin_heq_flatPullbackChow (d e : ℕ) (j : ℤ)
    [Flat (dimPartPieceHom sX sY f d e)] {t : ℕ}
    (ht : RelativeDimension (dimPartPieceHom sX sY f d e) t) (htd : t + e = d)
    (β : chowGroup (fieldChowSituation k) (partBase sY e) ((e : ℤ) - j)) :
    dimPartPieceGysin sX sY hf d e j β ≍
      flatPullbackChow (fieldChowSituation k) (dimPartPieceBase sX sY f d e) (partBase sY e)
        (dimPartPieceHom sX sY f d e) (dimPartPieceHom_comp_partBase sX sY hf d e) t ht
        ((e : ℤ) - j) (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        β := by
  obtain ⟨c, rfl⟩ := exists_chowCohomologyCapFundamentalClass_eq sY e j β
  refine (dimPartPieceGysin_chowCohomologyCapFundamentalClass sX sY hf d e j c).trans ?_
  refine (chowCohomologyCapFundamentalClass_heq_of_eq _ (by omega) _ _).trans
    (flatPullbackChow_chowCohomologyCapFundamentalClass' (partBase sY e)
      (dimPartPieceBase sX sY f d e) (dimPartPieceHom sX sY f d e)
      (dimPartPieceHom_comp_partBase sX sY hf d e) ht (relativeDimension_partBase sY e) j c).symm

/-! ### Functoriality -/

section Functoriality

variable {Z : Scheme.{u}} (sZ : Z ⟶ (fieldChowSituation k).S) [Smooth sZ] {g : Y ⟶ Z}
  [LocallyOfFiniteType g] (hg : g ≫ sZ = sY)

omit [LocallyOfFiniteType f] in
/-- The restriction `f_{d,e} : X_{d,e} ⟶ Y_e` of `f`, followed by the inclusion of `Y_e`, is the
inclusion of `X_{d,e}` followed by `f`. -/
@[reassoc]
theorem dimPartPieceHom_ι (d e : ℕ) :
    dimPartPieceHom sX sY f d e ≫ (dimPart sY e).ι =
      (dimPartPiece sX sY f d e).ι ≫ (dimPart sX d).ι ≫ f := by
  simp [dimPartPieceHom, dimPartPieceToPreimage, morphismRestrict_ι, morphismRestrict_ι_assoc]

include hf hg in
/-- **Stacks 0FF5 for the Gysin maps of morphisms of smooth schemes, on classes graded by
codimension: `(g ∘ f)^! = f^! ∘ g^!`.** -/
theorem codimensionGysin_comp (i : ℤ) (γ : codimensionChowGroup k sZ i) :
    codimensionGysin sX sZ (f := f ≫ g) (by rw [Category.assoc, hg, hf]) i γ =
      codimensionGysin sX sY hf i (codimensionGysin sY sZ hg i γ) := by
  have hfg : (f ≫ g) ≫ sZ = sX := by rw [Category.assoc, hg, hf]
  funext d
  refine (chowGroupDimPartPieceEquiv sX sY (f := f) d (d - i)).injective (funext fun e ↦ ?_)
  obtain ⟨e⟩ := e
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin sX sY hf]
  -- the pieces `V_c = X_{d,e} ∩ X'_{d,c}`, `X'_{d,c} = X_d ∩ (g ∘ f)⁻¹(Z_c)`
  set W := dimPartPiece sX sY f d e with hWdef
  have hdec : IsClopenDecomposition fun c : ULift.{u} ℕ ↦
      (W.ι ⁻¹ᵁ dimPartPiece sX sZ (f ≫ g) d c.down).ι.opensRange := by
    have h := (isClopenDecomposition_dimPartPiece sX sZ (f := f ≫ g) d).preimage W.ι
    simp only [Scheme.Opens.opensRange_ι] at h ⊢
    exact h
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) (dimPartPieceBase sX sY f d e)
    (fun c : ULift.{u} ℕ ↦ (W.ι ⁻¹ᵁ dimPartPiece sX sZ (f ≫ g) d c.down).ι ≫
      dimPartPieceBase sX sY f d e)
    (fun c ↦ (W.ι ⁻¹ᵁ dimPartPiece sX sZ (f ≫ g) d c.down).ι) (fun _ ↦ rfl) hdec
    (d - i)).injective (funext fun c ↦ ?_)
  obtain ⟨c⟩ := c
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
  set W' := dimPartPiece sX sZ (f ≫ g) d c with hW'def
  set V := W.ι ⁻¹ᵁ W' with hVdef
  have hgys : (gysinSystemOfInvertible (fieldChowSituation k)).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _
  let ℓ : V.toScheme ⟶ W'.toScheme := W.ι ∣_ W'
  have hℓ : ℓ ≫ W'.ι = V.ι ≫ W.ι := morphismRestrict_ι _ _
  have : IsOpenImmersion ℓ := by dsimp only [ℓ]; infer_instance
  clear_value ℓ
  have hℓbase : ℓ ≫ dimPartPieceBase sX sZ (f ≫ g) d c = V.ι ≫ dimPartPieceBase sX sY f d e := by
    show ℓ ≫ W'.ι ≫ partBase sX d = V.ι ≫ W.ι ≫ partBase sX d
    rw [← Category.assoc, hℓ, Category.assoc]
  -- the left-hand side is `res(c_Z) ∩ [V]`
  obtain ⟨cZ, hcZ⟩ := exists_chowCohomologyCapFundamentalClass_eq sZ c i (γ c)
  obtain ⟨cY, hcY⟩ := exists_chowCohomologyCapFundamentalClass_eq sY e i
    (codimensionGysin sY sZ hg i γ e)
  have hdimW := Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension
    (dimPartPieceBase sX sY f d e) (relativeDimension_dimPartPieceBase sX sY (f := f) d e)
  have hdimW' := Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension
    (dimPartPieceBase sX sZ (f ≫ g) d c) (relativeDimension_dimPartPieceBase sX sZ (f := f ≫ g) d c)
  rw [chowGroupRestrict_comp, chowGroupRestrict_congr _ _ _ (V.ι ≫ W.ι) _ _ (ℓ ≫ W'.ι) hℓ.symm
      (by rw [Category.assoc]; exact hℓbase),
    ← chowGroupRestrict_comp (sU := dimPartPieceBase sX sZ (f ≫ g) d c) (j := W'.ι) (hj := rfl)
      (i := ℓ) (hi := hℓbase),
    chowGroupRestrict_codimensionGysin sX sZ hfg i γ d c, ← hcZ,
    eq_of_heq (dimPartPieceGysin_chowCohomologyCapFundamentalClass sX sZ hfg d c i cZ),
    chowGroupRestrict_capFundamentalClass_restrictionOfEq _ _ _ _ _ _ _ _ hdimW' i cZ,
    ← hcY, eq_of_heq (dimPartPieceGysin_chowCohomologyCapFundamentalClass sX sY hf d e i cY),
    chowGroupRestrict_capFundamentalClass_restrictionOfEq _ _ _ _ _ _ _ _ hdimW i cY]
  congr 1
  -- the classes agree, through `Y'_{e,c} = Y_e ∩ g⁻¹(Z_c)`
  set Y' := dimPartPiece sY sZ g e c with hY'def
  have hpt : ∀ v : W.toScheme, (dimPart sY e).ι (dimPartPieceHom sX sY f d e v) =
      f ((dimPart sX d).ι (W.ι v)) := fun v ↦ by
    rw [← Scheme.Hom.comp_apply, dimPartPieceHom_ι]
    rfl
  have hle : V ≤ dimPartPieceHom sX sY f d e ⁻¹ᵁ Y' := by
    intro v hv
    show g ((dimPart sY e).ι (dimPartPieceHom sX sY f d e v)) ∈ dimPart sZ c
    rw [hpt]
    exact hv
  let ℓ' : V.toScheme ⟶ Y'.toScheme :=
    W.toScheme.homOfLE hle ≫ (dimPartPieceHom sX sY f d e ∣_ Y')
  have hℓ' : ℓ' ≫ Y'.ι = V.ι ≫ dimPartPieceHom sX sY f d e := by
    simp only [ℓ', Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have : LocallyOfFiniteType ℓ' := by dsimp only [ℓ']; infer_instance
  clear_value ℓ'
  have hmor : ℓ' ≫ dimPartPieceHom sY sZ g e c = ℓ ≫ dimPartPieceHom sX sZ (f ≫ g) d c := by
    refine (cancel_mono (dimPart sZ c).ι).1 ?_
    rw [Category.assoc ℓ' (dimPartPieceHom sY sZ g e c) (dimPart sZ c).ι, dimPartPieceHom_ι,
      Category.assoc ℓ (dimPartPieceHom sX sZ (f ≫ g) d c) (dimPart sZ c).ι, dimPartPieceHom_ι,
      ← Category.assoc ℓ', hℓ', ← Category.assoc ℓ, hℓ, Category.assoc, Category.assoc,
      dimPartPieceHom_ι_assoc]
    try simp only [Category.assoc]
    rfl
  -- on `Y'`, `res(c_Y) = res(c_Z)` by Stacks 0FC2
  have hYc : chowCohomologyRestrictionOfEq (fieldChowSituation k) (dimPartPieceBase sY sZ g e c)
      (partBase sY e) (f := Y'.ι) rfl (gysinSystemOfInvertible _) hgys i cY =
      chowCohomologyRestrictionOfEq (fieldChowSituation k) (dimPartPieceBase sY sZ g e c)
        (partBase sZ c) (dimPartPieceHom_comp_partBase sY sZ hg e c) (gysinSystemOfInvertible _)
        hgys i cZ := by
    refine (chowCohomologyCapFundamentalClass_bijective_of_smooth_field k
      (dimPartPieceBase sY sZ g e c) e (relativeDimension_dimPartPieceBase sY sZ (f := g) e c)
      i).1 ?_
    have h1 := chowGroupRestrict_capFundamentalClass_partBase sY (dimPartPieceBase sY sZ g e c) e
      Y'.ι rfl i cY
    rw [hcY, chowGroupRestrict_codimensionGysin sY sZ hg i γ e c, ← hcZ,
      eq_of_heq (dimPartPieceGysin_chowCohomologyCapFundamentalClass sY sZ hg e c i cZ)] at h1
    exact h1.symm
  have hbaseV : (ℓ' ≫ Y'.ι) ≫ partBase sY e = V.ι ≫ dimPartPieceBase sX sY f d e := by
    rw [hℓ', Category.assoc, dimPartPieceHom_comp_partBase sX sY hf d e]
  rw [chowCohomologyRestrictionOfEq_congr _ _ hℓ'.symm _ hbaseV,
    ← chowCohomologyRestrictionOfEq_restrictionOfEq _ _ _ Y'.ι ℓ' rfl
      (by rw [← hbaseV, Category.assoc]), hYc,
    chowCohomologyRestrictionOfEq_restrictionOfEq _ _ _ _ ℓ' _
      (by rw [← hbaseV, Category.assoc])
      (by rw [Category.assoc, dimPartPieceHom_comp_partBase sY sZ hg e c, ← hbaseV,
        Category.assoc]),
    chowCohomologyRestrictionOfEq_congr _ _ hmor]

omit [LocallyOfFiniteType f] in
/-- **The Gysin map of the identity is the identity**, on classes graded by codimension. -/
theorem codimensionGysin_id (i : ℤ) (γ : codimensionChowGroup k sX i) :
    codimensionGysin sX sX (f := 𝟙 X) (Category.id_comp sX) i γ = γ := by
  funext d
  refine (chowGroupDimPartPieceEquiv sX sX (f := 𝟙 X) d (d - i)).injective (funext fun e ↦ ?_)
  obtain ⟨e⟩ := e
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin sX sX (Category.id_comp sX) i γ d e]
  by_cases hed : e = d
  · subst hed
    obtain ⟨c, hc⟩ := exists_chowCohomologyCapFundamentalClass_eq sX e i (γ e)
    rw [← hc, eq_of_heq (dimPartPieceGysin_chowCohomologyCapFundamentalClass sX sX
      (Category.id_comp sX) e e i c)]
    rw [chowGroupRestrict_capFundamentalClass_partBase sX _ e
      (dimPartPiece sX sX (𝟙 X) e e).ι rfl]
    congr 1
    refine chowCohomologyRestrictionOfEq_congr _ _ ?_ _ _ _ _
    refine (cancel_mono (dimPart sX e).ι).1 ?_
    rw [dimPartPieceHom_ι, Category.comp_id]
  · have : IsEmpty (dimPartPiece sX sX (𝟙 X) d e).toScheme := by
      refine ⟨fun v ↦ ?_⟩
      have h0 : (dimPartPiece sX sX (𝟙 X) d e).ι v ∈
          ((dimPartPiece sX sX (𝟙 X) d e : Set _)) :=
        (dimPartPiece sX sX (𝟙 X) d e).range_ι ▸ Set.mem_range_self v
      have he : (dimPart sX d).ι ((dimPartPiece sX sX (𝟙 X) d e).ι v) ∈ dimPart sX e := by
        simpa using h0
      have hd : (dimPart sX d).ι ((dimPartPiece sX sX (𝟙 X) d e).ι v) ∈ (dimPart sX d : Set X) :=
        (dimPart sX d).range_ι ▸ Set.mem_range_self _
      exact Set.disjoint_left.1 (TopologicalSpace.Opens.coe_disjoint.2
        ((Stacks.WeilCohomology.isClopenDecomposition_dimPart sX).disjoint d e (Ne.symm hed)))
        hd he
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _

end Functoriality

end Stacks.Chow

end
