module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackCovering.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Additivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PositivityComponents
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PositivityDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PositivityZeroDim

/-!
# Positivity of the intersection number of ample invertible modules

[Stacks, Tag 0BEV]: let `k` be a field, let `X` be a scheme proper over `k`, let `i : Z ⟶ X` be a
closed subscheme of dimension `d` and let `𝓛_1, …, 𝓛_d` be ample invertible `𝒪_X`-modules. Then

`(𝓛_1 ⋯ 𝓛_d · Z) > 0`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor`: a nonempty
  effective Cartier divisor on an integral scheme of finite type over a field has dimension one
  less.
* `AlgebraicGeometry.intersectionNumber_update_tensorPower`: replacing one entry of the family by
  its `n`-th tensor power multiplies the intersection number by `n`.
* `AlgebraicGeometry.intersectionNumber_pos`: **[Stacks, Tag 0BEV]**.
* `AlgebraicGeometry.selfIntersectionNumber_pos`, `AlgebraicGeometry.degreeWithRespectTo_pos`:
  the self-intersection and degree forms.

## References

* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
* [Stacks Project, Tag 0BES](https://stacks.math.columbia.edu/tag/0BES)
* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
* [Stacks Project, Tag 0BER](https://stacks.math.columbia.edu/tag/0BER)
* [Stacks Project, Tag 0BEW](https://stacks.math.columbia.edu/tag/0BEW)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerOneIso tensorPowerSuccIso)

universe u

namespace AlgebraicGeometry

/-! ### The dimension of an effective Cartier divisor -/

/-- A nonempty effective Cartier divisor on an integral scheme of finite type over a field has
dimension one less than the scheme. -/
public theorem topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor (k : Type u) [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] [IsIntegral Y]
    (D : Y.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    [Nonempty D.subscheme] {d : ℕ} (hdim : topologicalKrullDim Y = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim D.subscheme = (d : WithBot ℕ∞) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  rw [topologicalKrullDim_eq_iSup_trdeg_residueField k D.subscheme (D.subschemeι ≫ g)]
  have hvalue (ξ : genericPoints D.subscheme) :
      letI : Algebra k (D.subscheme.residueField ξ.1) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ g).appTop ≫
          D.subscheme.Γevaluation ξ.1).hom.toAlgebra
      (Cardinal.toENat (Algebra.trdeg k (D.subscheme.residueField ξ.1)) : WithBot ℕ∞) =
        (d : WithBot ℕ∞) := by
    let : Algebra k (Y.residueField (D.subschemeι ξ.1)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
        Y.Γevaluation (D.subschemeι ξ.1)).hom.toAlgebra
    let : Algebra k (D.subscheme.residueField ξ.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ g).appTop ≫
        D.subscheme.Γevaluation ξ.1).hom.toAlgebra
    rw [← trdeg_residueField_of_surjectiveOnStalks k g D.subschemeι ξ.1]
    have hlocal := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD ξ.1
      ⟨⟨closure {ξ.1}, ξ.2⟩, rfl⟩
    have hformula := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y g
      (D.subschemeι ξ.1)
    rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y g
      (D.subschemeι ξ.1), hdim, hlocal] at hformula
    refine ENat.WithBot.add_one_cancel.mp ?_
    simpa only [Nat.cast_add, Nat.cast_one] using hformula.symm
  simp_rw [hvalue]
  have : Nonempty (genericPoints D.subscheme) := by
    obtain ⟨x⟩ := ‹Nonempty D.subscheme›
    exact ⟨genericPoints.ofComponent
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩
  simp

/-! ### Replacing one module by a tensor power -/

/-- Additivity applied to `𝓛_j ≅ 𝓛_j' ⊗ 𝒪`, where `𝓛_j'` is the `j`-th entry of `M` and `𝒪` is its
zeroth tensor power. -/
private theorem intersectionNumber_eq_update_zeroPower_add (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L M : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)]
    (j : Fin d) (hoff : ∀ q, q ≠ j → M q = L q) (e : L j ≅ M j) :
    haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Function.update M j (tensorPower X.presheaf X.ringCatSheaf.2 (M j) 0) q) :=
      isInvertible_update M j _
    intersectionNumber k f i d hd L = intersectionNumber k f i d hd M +
      intersectionNumber k f i d hd
        (Function.update M j (tensorPower X.presheaf X.ringCatSheaf.2 (M j) 0)) := by
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update M j (tensorPower X.presheaf X.ringCatSheaf.2 (M j) 0) q) :=
    isInvertible_update M j _
  exact intersectionNumber_tensor k f i d hd j L M
    (Function.update M j (tensorPower X.presheaf X.ringCatSheaf.2 (M j) 0)) hoff
    (fun q hq => (Function.update_of_ne hq _ _).trans (hoff q hq))
    (e ≪≫ (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
        X.ringCatSheaf.2 (M j)).symm ≪≫ eqToIso (congrArg
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
              (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj (M j)).obj)
          ((Stacks.SheafOfModules.Invertible.tensorPower_zero X.presheaf
              X.ringCatSheaf.2 (M j)).symm.trans (Function.update_self j _ M).symm)))

/-- Replacing one entry of the family by its zeroth tensor power makes the intersection number
zero. -/
public theorem intersectionNumber_update_zeroPower (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] (j : Fin d) :
    haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) 0) q) :=
      isInvertible_update L j _
    intersectionNumber k f i d hd
      (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) 0)) = 0 := by
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) 0) q) :=
    isInvertible_update L j _
  have h := intersectionNumber_eq_update_zeroPower_add k f i d hd L L j (fun _ _ => rfl)
    (Iso.refl _)
  omega

/-- The intersection number is unchanged by replacing one entry of the family by an isomorphic
module. -/
public theorem intersectionNumber_eq_of_iso_at (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L M : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)]
    (j : Fin d) (hoff : ∀ q, q ≠ j → M q = L q) (e : L j ≅ M j) :
    intersectionNumber k f i d hd L = intersectionNumber k f i d hd M := by
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update M j (tensorPower X.presheaf X.ringCatSheaf.2 (M j) 0) q) :=
    isInvertible_update M j _
  have h0 := intersectionNumber_update_zeroPower k f i d hd M j
  have hL := intersectionNumber_eq_update_zeroPower_add k f i d hd L M j hoff e
  omega

/-- Replacing one entry of the family by its `n`-th tensor power multiplies the intersection
number by `n`. -/
public theorem intersectionNumber_update_tensorPower (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    (j : Fin d) (n : ℕ) :
    haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) (n : ℤ)) q) :=
      isInvertible_update L j _
    intersectionNumber k f i d hd
        (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) (n : ℤ))) =
      n * intersectionNumber k f i d hd L := by
  have hupd : ∀ m : ℕ, ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) (m : ℤ)) q) :=
    fun m => isInvertible_update L j _
  have hsucc : ∀ m : ℕ,
      intersectionNumber k f i d hd
          (Function.update L j
            (tensorPower X.presheaf X.ringCatSheaf.2 (L j) ((m + 1 : ℕ) : ℤ)))
        = intersectionNumber k f i d hd
            (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) (m : ℤ))) +
          intersectionNumber k f i d hd L := by
    intro m
    refine intersectionNumber_tensor k f i d hd j
      (Function.update L j
        (tensorPower X.presheaf X.ringCatSheaf.2 (L j) ((m + 1 : ℕ) : ℤ)))
      (Function.update L j (tensorPower X.presheaf X.ringCatSheaf.2 (L j) (m : ℤ))) L
      (fun q hq => (Function.update_of_ne hq _ _).trans (Function.update_of_ne hq _ _).symm)
      (fun q hq => (Function.update_of_ne hq _ _).symm)
      (eqToIso (Function.update_self j _ L) ≪≫
        eqToIso (congrArg (tensorPower X.presheaf X.ringCatSheaf.2 (L j))
          (show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by push_cast; ring)) ≪≫
        (tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 (L j) (m : ℤ)).symm ≪≫
        eqToIso (congrArg
          (fun A : X.Modules => ((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
              (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).obj (L j))
          (Function.update_self j _ L).symm))
  induction n with
  | zero => simpa using intersectionNumber_update_zeroPower k f i d hd L j
  | succ m ih => rw [hsucc m, ih]; push_cast; ring

/-! ### Tag 0BEV -/

/-- The induction behind [Stacks, Tag 0BEV], with the dimension led so that the inductive
hypothesis is available for every closed subscheme of `X`. -/
private theorem intersectionNumber_pos_aux (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] :
    ∀ (d : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (hdim : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
      [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)],
      (∀ j, Scheme.Modules.IsAmple X (L j)) →
      0 < intersectionNumber k f i d hdim.le L := by
  classical
  intro d
  induction d with
  | zero =>
      intro Z i _ hdim L _ _
      exact intersectionNumber_pos_of_topologicalKrullDim_eq_zero k f i hdim L
  | succ d ih =>
      intro Z i _ hdim L _ hL
      refine intersectionNumber_pos_of_pos_topDimComponents k f i (d + 1) hdim L fun W => ?_
      have : IsIntegral W.1.subscheme := W.2.1
      have hdimW : topologicalKrullDim W.1.subscheme = ((d + 1 : ℕ) : WithBot ℕ∞) := by
        refine W.2.2.2.trans ?_
        rwa [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i]
      have hposdim : 0 < topologicalKrullDim W.1.subscheme := by
        rw [hdimW]
        exact_mod_cast Nat.succ_pos d
      have hMample : Scheme.Modules.IsAmple W.1.subscheme
          ((Scheme.Modules.pullback W.1.subschemeι).obj (L 0)) :=
        Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
          (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
            W.1.subschemeι (L 0)
            (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X (L 0) (hL 0))
            (Or.inl ⟨inferInstance, inferInstance⟩))
      obtain ⟨n, D, hn, hDcartier, hDne, ⟨e⟩⟩ :=
        exists_effectiveCartierDivisor_tensorPower_of_isAmple k (W.1.subschemeι ≫ f) hposdim
          ((Scheme.Modules.pullback W.1.subschemeι).obj (L 0)) hMample
      have hDdim : topologicalKrullDim D.subscheme = (d : WithBot ℕ∞) :=
        topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k
          (W.1.subschemeι ≫ f) D hDcartier hdimW
      set N : Fin (d + 1) → X.Modules :=
        Function.update L 0 (tensorPower X.presheaf X.ringCatSheaf.2 (L 0) (n : ℤ))
      have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
        isInvertible_update L 0 _
      have hNsucc : ∀ t : Fin d, N t.succ = L t.succ := fun t =>
        Function.update_of_ne (Fin.succ_ne_zero t) _ _
      have hNiso : (Scheme.Modules.pullback W.1.subschemeι).obj (N 0) ≅
          (Stacks.Divisors.invertibleSheaf D : W.1.subscheme.Modules) := by
        refine Iso.trans ?_ e
        exact eqToIso (congrArg (Scheme.Modules.pullback W.1.subschemeι).obj
            (Function.update_self (0 : Fin (d + 1)) _ L)) ≪≫
          Scheme.Modules.pullbackTensorPowerIso W.1.subschemeι (L 0) n
      have : Stacks.Divisors.IsEffectiveCartierDivisor D := hDcartier
      have hBEU := intersectionNumber_eq_of_isEffectiveCartierDivisor k f W.1.subschemeι d
        (le_of_eq hdimW) N D (le_of_eq hDdim) hNiso
      have hrec : 0 < intersectionNumber k f (D.subschemeι ≫ W.1.subschemeι) d
          (le_of_eq hDdim) (fun t : Fin d => N t.succ) := by
        have hNsucc' : (fun t : Fin d => N t.succ) = fun t : Fin d => L t.succ :=
          funext hNsucc
        have := ih (D.subschemeι ≫ W.1.subschemeι) hDdim (fun t : Fin d => L t.succ)
          (fun t => hL t.succ)
        simpa only [hNsucc'] using this
      have hNpos : 0 < intersectionNumber k f W.1.subschemeι (d + 1) (le_of_eq hdimW) N := by
        rwa [hBEU]
      have hmul := intersectionNumber_update_tensorPower k f W.1.subschemeι (d + 1)
        (le_of_eq hdimW) L 0 n
      have hprod : (0 : ℤ) <
          (n : ℤ) * intersectionNumber k f W.1.subschemeι (d + 1) (le_of_eq hdimW) L := by
        rwa [← hmul]
      exact (mul_pos_iff_of_pos_left (show (0 : ℤ) < (n : ℤ) by exact_mod_cast hn)).mp hprod

/-- **[Stacks, Tag 0BEV].** Let `k` be a field, let `X` be a scheme proper over `k`, let
`i : Z ⟶ X` be a closed subscheme of dimension `d` and let `𝓛_1, …, 𝓛_d` be ample invertible
`𝒪_X`-modules.  Then the intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` is positive. -/
@[stacks 0BEV]
public theorem intersectionNumber_pos (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hdim : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hL : ∀ j, Scheme.Modules.IsAmple X (L j)) :
    0 < intersectionNumber k f i d hdim.le L :=
  intersectionNumber_pos_aux k f d i hdim L hL

/-- **[Stacks, Tag 0BEV] for the self-intersection number** `(𝓛^d · Z)` of a single ample
invertible module. -/
@[stacks 0BEV "the self-intersection number of a single ample module"]
public theorem selfIntersectionNumber_pos (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hdim : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < selfIntersectionNumber k f i d hdim.le L :=
  intersectionNumber_pos k f i d hdim (fun _ => L) fun _ => hL

/-- **[Stacks, Tag 0BEV] for the degree** `deg_𝓛(Z)` of [Stacks, Tag 0BEW]: the degree of a
closed subscheme with respect to an ample invertible module is positive. -/
@[stacks 0BEV "the degree deg_L(Z) of Tag 0BEW is positive"]
public theorem degreeWithRespectTo_pos (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hdim : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < degreeWithRespectTo k f i d hdim L hL :=
  selfIntersectionNumber_pos k f i d hdim L hL

end AlgebraicGeometry

end
