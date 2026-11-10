module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointAdapted
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.GoodTraceExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison

/-!
# Non-divisibility of the Kummer point class, from purity and the level comparison

Let `X` be proper over a field `k`, `k̄` an algebraically closed extension, `Y = X_k̄` connected
and smooth of relative dimension `d`, `ℓ` a prime invertible in `k̄`, and `x = s(pt)` a
`k`-rational point of `X`. This file reduces the non-divisibility of the Kummer point class of
étale coordinates centred at `x` (`Stacks.EtaleCohomology.RationalPointKummerClassNondivisible`,
the input `hgen` of
`Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_top`)
to three statements:

* `Stacks.EtaleCohomology.TopCohomologyPointClass ℓ k̄`: in `H^{2d}(Y, ℤ/ℓ)` the point-class map
  of a purity class of a point is bijective;
* `Stacks.EtaleCohomology.KummerFlag.KummerFlagPurity k̄ ℓ`: at level `ℓ`, the Kummer flag class of
  an étale coordinate system centred at a `k̄`-point `y` is a purity class of `y`;
* `Stacks.EtaleCohomology.KummerFlag.KummerPointClassLevelReduction k̄ ℓ`: a Kummer point class at
  level `ℓⁿ⁺¹` (root `ζ`) which is `ℓ` times a class has vanishing reduction, the Kummer point
  class at level `ℓ` (root `ζ^{ℓⁿ}`) of the same flag.

The argument (`Stacks.EtaleCohomology.rationalPointKummerClassNondivisible_of_kummerFlagPurity`):
the coordinates of the chart pulled back to `U = pr⁻¹(V) ⊆ Y` define an étale `ψ : U ⟶ 𝔸^d_k̄`
(base change of the chart), whose coordinates vanish exactly at the unique point `y` of `Y` over
`x`. At level `ℓ` the Kummer flag class is a purity class of `y`, so by
`TopCohomologyPointClass` (with `Y` its own compactification) the Kummer point class is the
image of the nonzero adapted map under an injective map, hence nonzero
(`Stacks.EtaleCohomology.KummerFlag.kummerPointClass_ne_zero_of_injective`). By the level
comparison, divisibility by `ℓ` at level `ℓⁿ⁺¹` would make it zero.

## Main definitions

* `Stacks.EtaleCohomology.KummerFlag.KummerFlagPurity`: at level `ℓ`, the Kummer flag class of
  étale coordinates centred at a point is a purity class of that point.
* `Stacks.EtaleCohomology.KummerFlag.KummerPointClassLevelReduction`: a Kummer point class at
  level `ℓⁿ⁺¹` which is `ℓ` times a class reduces to zero at level `ℓ`.

## Main results

* `Stacks.EtaleCohomology.KummerFlag.kummerPointClass_ne_zero_of_injective`: a Kummer point class
  is nonzero once the point-class map of its flag class is injective.
* `Stacks.EtaleCohomology.rationalPointKummerClassNondivisible_of_kummerFlagPurity`: the Kummer
  point class of a rational point is not divisible by `ℓ`, given the three statements above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

namespace KummerFlag

/-- **The Kummer flag class of étale coordinates is a purity class** (level `ℓ`). Let `K` be
algebraically closed, `ℓ` a prime invertible in `K` and `ζ` a primitive `ℓ`-th root of unity.
For an affine irreducible `U` over `K` and an étale `ψ : U ⟶ 𝔸^d_K` over `K` whose coordinates
`ψ_m` vanish simultaneously exactly at one point `y`, the flag `D` of the divisor data of the
`ψ_m` (`Stacks.EtaleCohomology.KummerFlag.functionDatum`) has a nonzero canonical map
`Λ_U ⟶ E_0 ⋯ E_{d-1} Λ_U`, and there is a closed immersion `i : T ⟶ U` of a point étale over
`K`, with `E_0 ⋯ E_{d-1} Λ_U ≅ i_* Λ_T`, through which the Kummer flag class is a purity class
of degree `2d` for `i`. (The divisor of each `ψ_m` is smooth, its Kummer divisor class is its
cycle class, and purity classes compose along the flag.) -/
def KummerFlagPurity (K : Type u) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (U : Scheme.{u}) [IsAffine U] [IrreducibleSpace U] (fU : U ⟶ Spec (.of K)) (d : ℕ)
    (ψ : U ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K))), Etale ψ →
    ψ ≫ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) = fU →
    ∀ y : U, (∀ x : U, (∀ m : Fin d, x ∉ U.basicOpen
        (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ↔ x = y) →
    ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)),
      flagUnit (N := ℓ) (fun m => functionDatum
        (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ≠ 0 ∧
      ∃ (T : Scheme.{u}) (i : T ⟶ U) (_ : IsClosedImmersion i) (_ : IrreducibleSpace T)
        (_ : SmoothOfRelativeDimension 0 (i ≫ fU))
        (e : flagSheaf (N := ℓ) (fun m => functionDatum
            (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m)))) ≅
          (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)),
        IsPurityClass i (unitSheaf (X := U) ℓ) ((Ext.mk₀ e.inv).comp
          (kummerFlagClass hζ hℓ fU (fun m => functionDatum
            (ψ.appTop (AffineSpace.coord (Spec (.of K)) (ULift.up m))))) (zero_add _))

/-- **Reduction of Kummer point classes from level `ℓⁿ⁺¹` to level `ℓ`.** For an open immersion
`n : U ⟶ Y` of `K`-schemes, a flag `D` of divisor data on `U`, a primitive `ℓʳ⁺¹`-th root of
unity `ζ` and `ζ' = ζ^{ℓʳ}`, maps `z`, `z'` adapted to the canonical maps at levels `ℓʳ⁺¹` and
`ℓ`, where the intersection of the closed parts of `D` is closed in `Y` (`Y = U ∪ O` with no point
of `U ∩ O` on every closed part, so that adapted maps are unique,
`Stacks.EtaleCohomology.KummerFlag.existsUnique_isAdapted`): if the Kummer point class of `(D, z)`
in `H^{2d}(Y, ℤ/ℓʳ⁺¹)` is `ℓ` times a class, then the
Kummer point class of `(D, z')` in `H^{2d}(Y, ℤ/ℓ)` vanishes. (Reduction
`H^{2d}(Y, ℤ/ℓʳ⁺¹) → H^{2d}(Y, ℤ/ℓ)` carries the first class to the second, Kummer classes
being compatible with `μ_{ℓʳ⁺¹} → μ_ℓ`, `t ↦ t^{ℓʳ}`, and it kills `ℓ H^{2d}(Y, ℤ/ℓʳ⁺¹)`.) -/
def KummerPointClassLevelReduction (K : Type u) [Field K] (ℓ : ℕ) : Prop :=
  ∀ (Y U O : Scheme.{u}) (fY : Y ⟶ Spec (.of K)) (n : U ⟶ Y) [IsOpenImmersion n]
    (o : O ⟶ Y) [IsOpenImmersion o] [PreconnectedSpace U] {d : ℕ} (D : Fin d → DivisorDatum U)
    [∀ m, PreconnectedSpace (D m).V],
    (∀ y : Y, y ∈ Set.range n.base ∨ y ∈ Set.range o.base) →
    (∀ x : U, n.base x ∈ Set.range o.base → ∃ m, x ∉ Set.range (D m).i.base) → ∀
    (r : ℕ) {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ (ℓ ^ (r + 1)))
    (hN : IsUnit (((ℓ ^ (r + 1) : ℕ)) : K)) (hζ' : IsPrimitiveRoot ζ' ℓ) (hℓ : IsUnit (ℓ : K)),
    ζ ^ (ℓ ^ r) = ζ' →
    ∀ (z : unitSheaf (X := Y) (ℓ ^ (r + 1)) ⟶
        (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).obj
          (flagSheaf (N := ℓ ^ (r + 1)) D)),
      IsAdapted n (flagUnit (N := ℓ ^ (r + 1)) D) z →
    ∀ (z' : unitSheaf (X := Y) ℓ ⟶
        (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj (flagSheaf (N := ℓ) D)),
      IsAdapted n (flagUnit (N := ℓ) D) z' →
      (∃ w, kummerPointClass hζ hN fY n D z = ℓ • w) → kummerPointClass hζ' hℓ fY n D z' = 0

section NonZero

attribute [local instance] moduleCat_hasLimitsOfSize

/-- The adjunction map of `L ⊣ R` commutes with precomposition in degree zero. -/
theorem extMap_mk₀_comp {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasExt C] [HasExt D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] {A A' : C} (a : A' ⟶ A) (M : D)
    (q : ℕ) (x : Ext A (R.obj M) q) :
    Stacks.ExtAdjunction.extMap adj A' M q ((Ext.mk₀ a).comp x (zero_add q)) =
      (Ext.mk₀ (L.map a)).comp (Stacks.ExtAdjunction.extMap adj A M q x) (zero_add q) := by
  rw [Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.comp_assoc _ _ _ _ _ (by omega)

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type u} [Field K] {W U T : Scheme.{u}}
  (g : W ⟶ Spec (.of K)) (n : U ⟶ W) [IsOpenImmersion n] {d : ℕ} (D : Fin d → DivisorDatum U)
  {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)) (i : T ⟶ U)
  (e : flagSheaf (N := ℓ) D ≅ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
    (unitSheaf (X := T) ℓ))

/-- **A Kummer point class is nonzero once the point-class map of its flag class is
injective.** Let `n : U ⟶ W` be an open immersion (read as `m = n`), `D` a flag on `U` with
`E_0 ⋯ E_{d-1} Λ_U ≅ i_* Λ_T`, `A ≅ Λ_W`, and suppose `z ↦ z ∘ m_!(γ)` is injective on
`Ext⁰_W(Λ_W, m_! i_* Λ_T)`, `γ` the Kummer flag class read in `Ext^{2d}_U(i_* Λ_T, m⁻¹ A)`.
If the canonical map `Λ_U ⟶ E_0 ⋯ E_{d-1} Λ_U` is nonzero, the Kummer point class through any
adapted `z'` is nonzero: it is the image of the nonzero `z' ∘ n_!(e)`, up to `A ≅ Λ_W`. -/
theorem kummerPointClass_ne_zero_of_injective (m : U ⟶ W) [IsOpenImmersion m] (hm : m = n)
    (A : EtaleModules.{u, 0} (ZMod ℓ) W) (ε : unitSheaf (X := W) ℓ ≅ A)
    (hinj : Function.Injective (fun z : Ext.{u + 1} (unitSheaf (X := W) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) m).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))) 0 =>
      z.comp (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) m) _ A
        (2 * d) (((Ext.mk₀ e.inv).comp (kummerFlagClass hζ hℓ (n ≫ g) D) (zero_add _)).comp
          (Ext.mk₀ ((restrictionUnitSheafIso (N := ℓ) m).symm ≪≫
            (etaleModuleRestriction.{u, 0} (ZMod ℓ) m).mapIso ε).hom) (add_zero _)))
        (zero_add _)))
    (z' : unitSheaf (X := W) ℓ ⟶
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj (flagSheaf (N := ℓ) D))
    (hz' : IsAdapted n (flagUnit (N := ℓ) D) z') (hflag : flagUnit (N := ℓ) D ≠ 0) :
    kummerPointClass hζ hℓ g n D z' ≠ 0 := by
  subst hm
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  intro h0
  let L := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) m
  let R := etaleModuleRestriction.{u, 0} (ZMod ℓ) m
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) m
  let x := (kummerFlagClass hζ hℓ (m ≫ g) D).comp
    (Ext.mk₀ (restrictionUnitSheafIso (N := ℓ) m).inv) (add_zero _)
  have key : (Ext.mk₀ (z' ≫ L.map e.hom)).comp (Stacks.ExtAdjunction.extMap adj _ A (2 * d)
      (((Ext.mk₀ e.inv).comp (kummerFlagClass hζ hℓ (m ≫ g) D) (zero_add _)).comp
        (Ext.mk₀ ((restrictionUnitSheafIso (N := ℓ) m).symm ≪≫ R.mapIso ε).hom) (add_zero _)))
      (zero_add _) =
      (kummerPointClass hζ hℓ g m D z').comp (Ext.mk₀ ε.hom) (add_zero _) := by
    have h1 : ((Ext.mk₀ e.inv).comp (kummerFlagClass hζ hℓ (m ≫ g) D) (zero_add _)).comp
        (Ext.mk₀ ((restrictionUnitSheafIso (N := ℓ) m).symm ≪≫ R.mapIso ε).hom) (add_zero _) =
        ((Ext.mk₀ e.inv).comp x (zero_add _)).comp (Ext.mk₀ (R.map ε.hom)) (add_zero _) := by
      simp only [x, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
        Ext.comp_assoc_of_third_deg_zero]
    rw [h1, Stacks.ExtAdjunction.extMap_naturality_mk₀, extMap_mk₀_comp, kummerPointClass,
      ← Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, Category.assoc,
      ← L.map_comp, e.hom_inv_id, L.map_id, Category.comp_id]
  have hz0 : (Ext.mk₀ (z' ≫ L.map e.hom) : Ext _ _ 0) = 0 := by
    apply hinj
    change _ = (0 : Ext _ _ 0).comp _ (zero_add _)
    rw [Ext.zero_comp]
    exact key.trans (by rw [h0, Ext.zero_comp])
  have hz'0 : z' = 0 := by
    have : z' ≫ L.map e.hom = 0 := (Ext.mk₀_bijective _ _).1 (hz0.trans (Ext.mk₀_zero _ _).symm)
    simpa using (cancel_mono (L.map e.hom)).1 (this.trans zero_comp.symm)
  apply hflag
  have hiso : IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) m).unit.app
      (flagSheaf (N := ℓ) D)) :=
    NatIso.isIso_app_of_isIso _ _
  have h4 : flagUnit (N := ℓ) D = (restrictionUnitSheafIso (N := ℓ) m).inv ≫ R.map z' ≫
      inv ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) m).unit.app (flagSheaf (N := ℓ) D)) := by
    unfold IsAdapted at hz'
    simp only [R, hz', Category.assoc, IsIso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [h4, hz'0, Functor.map_zero, zero_comp, comp_zero]

end NonZero

end KummerFlag

section Main

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (ℓ d : ℕ)

/-- **Over a rational point the geometric fibre is one point**: two points of `X_k̄` lying over
`x = s(pt)` are equal, the fibre being `Spec k̄ ×_k Spec k = Spec k̄`. -/
theorem eq_of_mem_range_of_mem_range (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    {y y' : (Limits.pullback f (specAlgebraMap k kbar) : Scheme.{u})}
    (hy : (pullback.fst f (specAlgebraMap k kbar)).base y ∈ Set.range s.base)
    (hy' : (pullback.fst f (specAlgebraMap k kbar)).base y' ∈ Set.range s.base) : y = y' := by
  let pr := pullback.fst f (specAlgebraMap k kbar)
  have h1 := IsPullback.of_hasPullback pr s
  have h3 := h1.paste_horiz (IsPullback.of_hasPullback f (specAlgebraMap k kbar)).flip
  rw [hs] at h3
  have := h3.isIso_fst_of_isIso
  have hinj : Function.Injective
      (pullback.fst pr s ≫ pullback.snd f (specAlgebraMap k kbar)).base :=
    (Scheme.homeoOfIso
      (asIso (pullback.fst pr s ≫ pullback.snd f (specAlgebraMap k kbar)))).injective
  obtain ⟨p, rfl⟩ := mem_range_fst_of_isPullback h1 y hy
  obtain ⟨p', rfl⟩ := mem_range_fst_of_isPullback h1 y' hy'
  rw [hinj (Subsingleton.elim _ _ : (pullback.fst pr s ≫
    pullback.snd f (specAlgebraMap k kbar)).base p = _)]

variable {d}

/-- **The base change of a chart is étale**: for `π : V ⟶ 𝔸^d_k` étale over `k`, the functions
`pr^♯ π^♯ T_m` on `U = pr⁻¹(V) ⊆ X_k̄` are the coordinates of an étale `ψ : U ⟶ 𝔸^d_k̄` over `k̄`,
the base change of `π`. -/
theorem exists_etale_affineSpace_fieldBaseChange (V : X.Opens)
    (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))) (hπ : Etale π)
    (hover : π ≫ (𝔸(ULift.{u} (Fin d); Spec (.of k)) ↘ Spec (.of k)) = V.ι ≫ f) :
    ∃ ψ : (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).toScheme ⟶
        𝔸(ULift.{u} (Fin d); Spec (.of kbar)), Etale ψ ∧
      ψ ≫ (𝔸(ULift.{u} (Fin d); Spec (.of kbar)) ↘ Spec (.of kbar)) =
        (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι ≫
          pullback.snd (Over.mk f).hom (specAlgebraMap k kbar) ∧
      ∀ m : Fin d, ψ.appTop (AffineSpace.coord (Spec (.of kbar)) (ULift.up m)) =
        (fieldBaseChangeProj (Over.mk f) kbar ∣_ V).appTop
          (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m))) := by
  let s' := specAlgebraMap k kbar
  let pr := pullback.fst f s'
  let UY := pr ⁻¹ᵁ V
  have hbig : IsPullback (pr ∣_ V) (UY.ι ≫ pullback.snd f s') (V.ι ≫ f) s' :=
    (isPullback_morphismRestrict pr V).paste_vert (IsPullback.of_hasPullback f s')
  have hA := AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) s'
  let ψ : UY.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of kbar)) :=
    hA.lift (pr ∣_ V ≫ π) (UY.ι ≫ pullback.snd f s') (by rw [Category.assoc, hover]; exact hbig.w)
  have hsq : IsPullback (pr ∣_ V) ψ π (AffineSpace.map _ s') :=
    IsPullback.of_bot (by rw [hA.lift_snd, hover]; exact hbig) (hA.lift_fst _ _ _).symm hA
  refine ⟨ψ, MorphismProperty.of_isPullback (P := @Etale) hsq hπ, hA.lift_snd _ _ _, fun m => ?_⟩
  rw [← AffineSpace.map_appTop_coord (n := ULift.{u} (Fin d)) s' (ULift.up m),
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hA.lift_fst, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  rfl

/-- **The common zero set of the coordinates of a chart is closed in `X_k̄`**: it lies over `x`, so
`X_k̄ = pr⁻¹(V) ∪ O` with `O` the complement of the fibre of `x`, and no point of `pr⁻¹(V) ∩ O`
lies on every closed part of the flag. -/
theorem exists_opens_support_chartDatum [IsSeparated f] (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _)
    (V : X.Opens) (hV : IsAffineOpen V) (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k)))
    (hv₀ : ∃ v : V, V.ι.base v ∈ Set.range s.base)
    (hzero : ∀ v : V, (∀ m : Fin d, v ∉ V.toScheme.basicOpen
        (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))) →
      V.ι.base v ∈ Set.range s.base) :
    ∃ O : (fieldBaseChange (Over.mk f) kbar).Opens,
      (∀ y, y ∈ Set.range (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι.base ∨
        y ∈ Set.range O.ι.base) ∧
      ∀ x, (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι.base x ∈ Set.range O.ι.base →
        ∃ m, x ∉ Set.range (chartDatum f kbar d V hV π m).i.base := by
  let pr := fieldBaseChangeProj (Over.mk f) kbar
  let U := pr ⁻¹ᵁ V
  have : IsAffineHom pr :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip
      inferInstance
  have : IsAffine U.toScheme := hV.preimage _
  let φ : Fin d → Γ(U.toScheme, ⊤) := fun m =>
    (pr ∣_ V).appTop (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))
  have : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  have hZc : IsClosed (pr.base ⁻¹' Set.range s.base) :=
    s.isClosedEmbedding.isClosed_range.preimage pr.continuous
  let O : (fieldBaseChange (Over.mk f) kbar).Opens := ⟨_, hZc.isOpen_compl⟩
  obtain ⟨v₀, hv₀⟩ := hv₀
  refine ⟨O, fun y => by
      by_cases hy : pr.base y ∈ Set.range s.base
      · left
        rw [Scheme.Opens.range_ι]
        obtain ⟨t, ht⟩ := hy
        obtain ⟨t₀, ht₀⟩ := hv₀
        change pr.base y ∈ V
        rw [← ht, Subsingleton.elim t t₀, ht₀]
        exact v₀.2
      · right
        rw [Scheme.Opens.range_ι]
        exact hy, fun x hx => by
      by_contra hcon
      push Not at hcon
      rw [Scheme.Opens.range_ι] at hx
      apply hx
      have h1 : ∀ m : Fin d, (pr ∣_ V).base x ∉ V.toScheme.basicOpen
          (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m))) := by
        intro m hm
        have hxm := hcon m
        change x ∈ Set.range (KummerFlag.zeroSchemeι (φ m)).base at hxm
        rw [KummerFlag.range_zeroSchemeι] at hxm
        apply hxm
        change x ∈ U.toScheme.basicOpen ((pr ∣_ V).appTop
          (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m))))
        rw [← Scheme.preimage_basicOpen_top]
        exact hm
      change pr.base (U.ι.base x) ∈ Set.range s.base
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
      exact hzero _ h1⟩

/-- **A map adapted to the Kummer flag of a chart exists.** -/
theorem exists_isAdapted_chartDatum [IsSeparated f] (N : ℕ) [NeZero N] (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _)
    (V : X.Opens) (hV : IsAffineOpen V) (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k)))
    (hv₀ : ∃ v : V, V.ι.base v ∈ Set.range s.base)
    (hzero : ∀ v : V, (∀ m : Fin d, v ∉ V.toScheme.basicOpen
        (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))) →
      V.ι.base v ∈ Set.range s.base) :
    ∃ z, KummerFlag.IsAdapted (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι
      (KummerFlag.flagUnit (N := N) (chartDatum f kbar d V hV π)) z := by
  obtain ⟨O, hcov, hZ⟩ := exists_opens_support_chartDatum f kbar s hs V hV π hv₀ hzero
  exact (KummerFlag.existsUnique_isAdapted (N := N) _ O.ι _ hcov hZ).exists

variable (d)

/-- **The Kummer point class of a rational point is not divisible by `ℓ`**
(`Stacks.EtaleCohomology.RationalPointKummerClassNondivisible`), for `X` proper over `k`, given
that the class of a point generates `H^{2d}(X_k̄, ℤ/ℓ)` (`TopCohomologyPointClass`), that the
Kummer flag class of étale coordinates is a purity class (`KummerFlagPurity`), and the level
comparison (`KummerPointClassLevelReduction`). At level `ℓ` the Kummer point class is nonzero
(`Stacks.EtaleCohomology.KummerFlag.kummerPointClass_ne_zero_of_injective`, with `X_k̄` its own
compactification); by the level comparison, divisibility by `ℓ` at level `ℓⁿ⁺¹` would kill it. -/
theorem rationalPointKummerClassNondivisible_of_kummerFlagPurity [IsAlgClosed kbar]
    [Fact ℓ.Prime] [IsProper f]
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hTop : TopCohomologyPointClass ℓ kbar) (hA : KummerFlag.KummerFlagPurity kbar ℓ)
    (hB : KummerFlag.KummerPointClassLevelReduction kbar ℓ) :
    RationalPointKummerClassNondivisible f kbar ℓ d := by
  intro n ζ hζ hN s hs V hV π hπ hover hv₀ hiff z hz hdiv
  have hℓp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓp.ne_zero⟩
  let pr := fieldBaseChangeProj (Over.mk f) kbar
  let U := pr ⁻¹ᵁ V
  have : IsAffineHom pr :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip
      inferInstance
  have : IsAffine U.toScheme := hV.preimage _
  let fY := pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)
  have : Smooth fY := SmoothOfRelativeDimension.smooth d fY
  have : IsProper fY :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _)
      ‹IsProper f›
  have : CompactSpace (fieldBaseChange (Over.mk f) kbar) := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := fY) Set.univ isOpen_univ isCompact_univ⟩
  have : IrreducibleSpace (fieldBaseChange (Over.mk f) kbar) :=
    irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace fY
  obtain ⟨v₀, t₀, ht₀⟩ := hv₀
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (V.ι.base v₀)
    (default : Spec (.of kbar)) (f := f) (g := specAlgebraMap k kbar) (Subsingleton.elim _ _)
  have hy₀U : y₀ ∈ U := by
    change (pullback.fst f (specAlgebraMap k kbar)).base y₀ ∈ V
    rw [hy₀]
    exact v₀.2
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace
    ((IrreducibleSpace.isIrreducible_univ _).2.subset_irreducible ⟨y₀, hy₀U⟩ U.isOpen
      subset_rfl (Set.subset_univ _))
  have hζ' : IsPrimitiveRoot (ζ ^ (ℓ ^ n)) ℓ := hζ.pow (pow_pos hℓp.pos _) (pow_succ ℓ n)
  obtain ⟨z', hz'⟩ := exists_isAdapted_chartDatum f kbar ℓ s hs V hV π ⟨v₀, t₀, ht₀⟩
    (fun v => (hiff v).1)
  have : ∀ m, PreconnectedSpace (chartDatum f kbar d V hV π m).V :=
    fun m => KummerFlag.preconnectedSpace_basicOpen _
  have : PreconnectedSpace U.toScheme :=
    ⟨(IrreducibleSpace.isIrreducible_univ _).isPreirreducible.isPreconnected⟩
  obtain ⟨O, hcov, hZ⟩ := exists_opens_support_chartDatum f kbar s hs V hV π ⟨v₀, t₀, ht₀⟩
    (fun v => (hiff v).1)
  have h0 : KummerFlag.kummerPointClass hζ' hℓ fY U.ι (chartDatum f kbar d V hV π) z' = 0 :=
    hB (fieldBaseChange (Over.mk f) kbar) U.toScheme O.toScheme fY U.ι O.ι
      (chartDatum f kbar d V hV π) hcov hZ n hζ hN hζ' hℓ rfl z hz z' hz' hdiv
  obtain ⟨ψ, hψ, hψover, hψc⟩ := exists_etale_affineSpace_fieldBaseChange f kbar V π hπ hover
  have hD : (fun m : Fin d => KummerFlag.functionDatum
      (ψ.appTop (AffineSpace.coord (Spec (.of kbar)) (ULift.up m)))) =
      chartDatum f kbar d V hV π := by
    funext m
    rw [hψc]
    rfl
  have hprv : pr.base y₀ ∈ Set.range s.base := by
    change (pullback.fst f (specAlgebraMap k kbar)).base y₀ ∈ _
    rw [hy₀]
    exact ⟨t₀, ht₀⟩
  let y₀' : U.toScheme := ⟨y₀, hy₀U⟩
  have hzs : ∀ x : U.toScheme, (∀ m : Fin d, x ∉ U.toScheme.basicOpen
      (ψ.appTop (AffineSpace.coord (Spec (.of kbar)) (ULift.up m)))) ↔ x = y₀' := by
    intro x
    have h1 : (∀ m : Fin d, x ∉ U.toScheme.basicOpen
        (ψ.appTop (AffineSpace.coord (Spec (.of kbar)) (ULift.up m)))) ↔
        (∀ m : Fin d, (pr ∣_ V).base x ∉ V.toScheme.basicOpen
          (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))) := by
      refine forall_congr' fun m => ?_
      rw [hψc, ← Scheme.preimage_basicOpen_top]
      rfl
    have h2 : V.ι.base ((pr ∣_ V).base x) = pr.base (U.ι.base x) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    refine h1.trans ((hiff ((pr ∣_ V).base x)).trans ?_)
    rw [h2]
    exact ⟨fun hx => Subtype.ext (eq_of_mem_range_of_mem_range f kbar s hs hx hprv),
      by rintro rfl; exact hprv⟩
  obtain ⟨hflag, T, i, hi, hT, hTs, e, hpur⟩ :=
    hD ▸ hA U.toScheme (U.ι ≫ fY) d ψ hψ hψover y₀' hzs hζ' hℓ
  have : IsLocallyNoetherian (fieldBaseChange (Over.mk f) kbar) :=
    LocallyOfFiniteType.isLocallyNoetherian fY
  have : IsNoetherian (fieldBaseChange (Over.mk f) kbar) := ⟨⟩
  let jc := CompactificationOf.ofProper fY
  have : IsOpenImmersion (U.ι ≫ jc.immersion) :=
    inferInstanceAs (IsOpenImmersion (U.ι ≫ 𝟙 _))
  have : @IsOpenImmersion U.toScheme (fieldBaseChange (Over.mk f) kbar)
      (U.ι ≫ jc.immersion) :=
    inferInstanceAs (IsOpenImmersion (U.ι ≫ 𝟙 _))
  let ε : unitSheaf (X := fieldBaseChange (Over.mk f) kbar) ℓ ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf ℓ) :=
    ((etaleModuleExtensionByZeroIdIso (ZMod ℓ) _).app _).symm
  have hγ := hpur.comp_mk₀
    ((KummerFlag.restrictionUnitSheafIso (N := ℓ) (U.ι ≫ jc.immersion)).symm ≪≫
    (etaleModuleRestriction.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).mapIso ε)
  have hbij := (hTop d _ fY jc).2 U.toScheme T U.ι i _ hγ
  exact KummerFlag.kummerPointClass_ne_zero_of_injective fY U.ι (chartDatum f kbar d V hV π)
    hζ' hℓ i e (U.ι ≫ jc.immersion) (Category.comp_id _) _ ε hbij.1 z' hz' hflag h0

end Main

end Stacks.EtaleCohomology

end
