module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLocallyConstantDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.StratumPurityDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.DenseOpenSmoothDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteOverFieldRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.StratumShortExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness

/-!
# Poincaré duality on a smooth proper curve at the skyscraper sheaf of a closed point

Let `Y` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k`, `Λ = ℤ/ℓ`, `t : H²(Y, Λ) → Λ` an injective trace and `z` a closed point of `Y`, with
`ι : Spec k → Y` the corresponding closed immersion. Given local purity (a purity class of `z`
in degree `2` on a neighbourhood of `z`), duality holds on `Y` at the skyscraper `ι_* Λ`:

`Ext^i(Λ_Y, ι_* Λ) × Ext^{2-i}(ι_* Λ, Λ_Y) → H²(Y, Λ) → Λ` is perfect.

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_of_isFinite_of_isSepClosed`:
  `Ext^q(Λ, K) = 0` for `q > 0` on a scheme finite over a separably closed field.
* `Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_of_isAffine_of_curve`:
  `Ext^q(Λ, K) = 0` for `q > 1` on an affine curve over an algebraically closed field.
* `AlgebraicGeometry.isAffine_of_opens_ne_top_of_isProper_curve`: a proper open subscheme of a
  proper curve is affine.
* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_directImage_point`: Poincaré duality
  at the skyscraper sheaf of a closed point of a smooth proper curve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace AlgebraicGeometry

/-- The inclusion of an open of a scheme of finite type over a field, composed with the structure
morphism, is quasi-compact. -/
private theorem quasiCompact_opens_ι_comp_of_locallyOfFiniteType {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (U : Y.Opens) :
    QuasiCompact (U.ι ≫ f) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := ⟨⟩
  infer_instance

/-- An open subscheme of a curve has topological Krull dimension at most one. -/
private theorem topologicalKrullDim_opens_le_one {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsCurve k f] (U : Y.Opens) : topologicalKrullDim U ≤ 1 :=
  IsCurve.topologicalKrullDim_eq_one (k := k) (f := f) ▸ topologicalKrullDim_le_of_etale U.ι

/-- **A proper open subscheme of a proper curve is affine.** Let `f : Y → Spec k` be a curve which
is proper over `k`, and `U ≠ Y` a nonempty open. Then `U` is affine. -/
theorem isAffine_of_opens_ne_top_of_isProper_curve {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] (U : Y.Opens) (hU : U ≠ ⊤)
    [Nonempty U] : IsAffine U := by
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have hdim := topologicalKrullDim_opens_le_one f U
  have := quasiCompact_opens_ι_comp_of_locallyOfFiniteType f U
  refine
    Stacks.AffineNoProperComponent.isAffine_of_topologicalKrullDim_le_one_of_forall_not_isProper
      k (U.ι ≫ f) hdim fun Z _ hP ↦ ?_
  have hZ : Z.1 = Set.univ :=
    Set.eq_univ_of_univ_subset (Z.2.2 (IrreducibleSpace.isIrreducible_univ U) (Set.subset_univ _))
  have : Surjective (Stacks.AffineNoProperComponent.componentIdealSheafData Z).subschemeι := by
    rw [surjective_iff, ← Set.range_eq_univ,
      Stacks.AffineNoProperComponent.range_subschemeι_componentIdealSheafData, hZ]
  have : UniversallyClosed (U.ι ≫ f) := UniversallyClosed.of_comp_surjective
    (Stacks.AffineNoProperComponent.componentIdealSheafData Z).subschemeι (U.ι ≫ f)
  have : IsProper (U.ι ≫ f) := ⟨⟩
  have : IsProper U.ι := IsProper.of_comp U.ι f
  have hcl : IsClosed (U : Set Y) := by
    have h := U.ι.isClosedMap.isClosed_range
    rwa [Scheme.Opens.range_ι] at h
  obtain ⟨x⟩ := ‹Nonempty U›
  have : (U : Set Y) = Set.univ := (IsClopen.eq_univ ⟨hcl, U.isOpen⟩ ⟨x.1, x.2⟩)
  exact hU (SetLike.coe_injective (by simpa using this))

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`Ext^q(Λ_Z, K) = 0` for `q > 0`** on a scheme `Z` finite over a separably closed field. -/
theorem subsingleton_ext_unitSheaf_of_isFinite_of_isSepClosed {K : Type u} [Field K]
    [IsSepClosed K] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g]
    (M : EtaleModules.{u, 0} (ZMod ℓ) Z) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Ext (unitSheaf (X := Z) ℓ) M q) := by
  have h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Z (ZMod ℓ)).obj M) q) :=
    subsingleton_etaleCohomology_of_isFinite_of_isSepClosed g _ q hq
  exact (extForgetSheafHAddEquiv (ZMod ℓ) Z M q).toEquiv.subsingleton

/-- **`Ext^q(Λ_T, K) = 0` for `q > 1`** on an affine separated scheme of finite type and dimension
at most one over an algebraically closed field (Tag 03SC (2)). -/
theorem subsingleton_ext_unitSheaf_of_isAffine_of_curve {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] [IsAffine T] (hdim : topologicalKrullDim T ≤ 1)
    (K : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Ext (unitSheaf (X := T) ℓ) K q) := by
  have hp : ℓ.Prime := Fact.out
  let S : TorsionSheafSituation.{u, 0} :=
    { k := k
      X := T
      structureMorphism := g
      dimension_le_one := hdim
      F := (etaleModuleUnderlyingAbelian T (ZMod ℓ)).obj K
      isTorsion := by
        intro U x
        refine ⟨⊤, T.smallEtaleTopology.top_mem U, fun V h _ => ⟨ℓ, hp.pos, ?_⟩⟩
        change ℓ • (K.obj.map h.op x : K.obj.obj (Opposite.op V)) = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul] }
  have h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian T (ZMod ℓ)).obj K) q) :=
    S.isAffineVanishingAboveDegreeOne ‹IsAffine T› q hq
  exact (extForgetSheafHAddEquiv (ZMod ℓ) T K q).toEquiv.subsingleton

/-- **A pairing between trivial groups is perfect**: if `Ext^i(O, F)` and `Ext^j(F, D)` are both
trivial, the duality map in degrees `(i, j)` is bijective. -/
theorem bijective_dualityPairing_of_subsingleton {C : Type*} [Category C] [Abelian C]
    [HasExt.{u + 1} C] {O D F : C} {N i j : ℕ} {A : Type*} [AddCommGroup A] (t : Ext O D N →+ A)
    (h : i + j = N) (hi : Subsingleton (Ext O F i)) (hj : Subsingleton (Ext F D j)) :
    Function.Bijective (Ext.dualityPairing O D N t F h) := by
  refine ⟨fun x y _ => Subsingleton.elim x y, fun φ => ⟨0, ?_⟩⟩
  ext y
  rw [Subsingleton.elim y 0, map_zero, map_zero]

section Point

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

/-- `Λ_N ≅ n^{-1} Λ_Y` for an open immersion `n : N → Y`. -/
def unitSheafIsoRestrictionOfIsOpenImmersion {N Z : Scheme.{u}} (n : N ⟶ Z) [IsOpenImmersion n] :
    unitSheaf (X := N) ℓ ≅ (etaleModuleRestriction.{u, 0} (ZMod ℓ) n).obj (unitSheaf (X := Z) ℓ) :=
  ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) n).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).symm ≪≫
    (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod ℓ) n).app (unitSheaf (X := Z) ℓ)

include f in
/-- **`Ext^q_Y(j_{V!} Λ_V, Λ_Y) = 0` for `q > 1`** for a nonempty open `V ≠ Y` of a smooth proper
curve over an algebraically closed field. -/
theorem subsingleton_ext_two_extensionByZeroOfRestriction_of_ne_top (V : Y.Opens) (hV : V ≠ ⊤)
    [Nonempty V] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Ext ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) V.ι).obj
      (unitSheaf (X := Y) ℓ)) (unitSheaf (X := Y) ℓ) q) := by
  have : IsAffine V := isAffine_of_opens_ne_top_of_isProper_curve f V hV
  have hdim := topologicalKrullDim_opens_le_one f V
  have := quasiCompact_opens_ι_comp_of_locallyOfFiniteType f V
  have : IsSeparated V.ι := AlgebraicGeometry.IsSeparated.isSeparated_of_mono V.ι
  have : Subsingleton (Ext (unitSheaf (X := V) ℓ)
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj (unitSheaf (X := Y) ℓ)) q) :=
    subsingleton_ext_unitSheaf_of_isAffine_of_curve (V.ι ≫ f) hdim _ q hq
  have : Subsingleton (Ext ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj
      (unitSheaf (X := Y) ℓ)) ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj
        (unitSheaf (X := Y) ℓ)) q) :=
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := (etaleModuleRestriction.{u, 0}
      (ZMod ℓ) V.ι).obj (unitSheaf (X := Y) ℓ))
      (unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) V.ι).hom q).1.subsingleton
  exact (Stacks.ExtAdjunction.extMap_bijective (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V.ι)
    _ _ q).2.subsingleton

/-- An additive map out of a group of prime order which is not zero is injective. -/
theorem injective_of_prime_card {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B)
    {p : ℕ} [hp : Fact p.Prime] (hA : Nat.card A = p) (hφ : φ ≠ 0) : Function.Injective φ := by
  have : Fact (Nat.card A).Prime := hA ▸ hp
  rcases φ.ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact (AddMonoidHom.ker_eq_bot_iff φ).1 h
  · exact absurd
      (AddMonoidHom.ext fun x => (AddMonoidHom.mem_ker).1 (h ▸ AddSubgroup.mem_top x)) hφ

/-- **A pairing into `ℤ/p` between groups of order `p` is perfect** as soon as it is nonzero on one
pair `(x, y)`. -/
private theorem bijective_dualityPairing_of_natCard_eq_prime {C : Type*} [Category C] [Abelian C]
    [HasExt.{u + 1} C] {O D F : C} {N i j p : ℕ} [hp : Fact p.Prime] (t : Ext O D N →+ ZMod p)
    [Module (ZMod p) (Ext F D j)] (h : i + j = N) (hi : Nat.card (Ext O F i) = p)
    (hj : Nat.card (Ext F D j) = p) (x : Ext O F i) (y : Ext F D j) (hxy : t (x.comp y h) ≠ 0) :
    Function.Bijective (Ext.dualityPairing O D N t F h) := by
  have : Finite (Ext F D j) := Nat.finite_of_card_ne_zero (hj.trans_ne hp.out.ne_zero)
  have : Finite (Ext F D j →+ ZMod p) := Nat.finite_of_card_ne_zero (by
    rw [ExtensionTorsor.natCard_addMonoidHom_zmod, hj]
    exact hp.out.ne_zero)
  refine (injective_of_prime_card _ hi fun h0 => hxy ?_).bijective_of_nat_card_le ?_
  · have := DFunLike.congr_fun (DFunLike.congr_fun h0 x) y
    rwa [Ext.dualityPairing_apply] at this
  · rw [ExtensionTorsor.natCard_addMonoidHom_zmod, hj, hi]

/-- **`Ext^q(C, Λ_Y)` at the skyscraper of a point.** For `C = n_! i_* (i ≫ n)^{-1} Λ_Y` and a
purity class `γ` of `i` in degree `2`, `Ext²(C, Λ_Y)` has `ℓ` elements and `Ext^q(C, Λ_Y) = 0`
for `q ≠ 2`. -/
private theorem natCard_ext_extensionByZero_directImage_point {N T : Scheme.{u}} (n : N ⟶ Y)
    [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i] [IsClosedImmersion (i ≫ n)]
    (g : T ⟶ Spec (.of k)) [IsFinite g] [ConnectedSpace T]
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) n).obj (unitSheaf (X := Y) ℓ)) 2)
    (hγ : IsPurityClass i _ γ) :
    Nat.card (Ext
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
            ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
        (unitSheaf (X := Y) ℓ) 2) = ℓ ∧
      (∀ q, q < 2 → Subsingleton (Ext
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
              ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
                ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
          (unitSheaf (X := Y) ℓ) q)) ∧
      ∀ q, 2 < q → Subsingleton (Ext
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
              ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
                ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
          (unitSheaf (X := Y) ℓ) q) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let ΛY := unitSheaf (X := Y) ℓ
  let ΛT := unitSheaf (X := T) ℓ
  let G := (etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
    ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj ΛY)
  let iS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) i
  let eG : G ≅ ΛT := unitSheafRestrictionIdInverseImageIso ℓ (i ≫ n)
  have hT0 : Nat.card (Ext ΛT ΛT 0) = ℓ :=
    (Nat.card_congr (Ext.homEquiv₀ (X := ΛT) (Y := ΛT))).trans (natCard_end_unitSheaf (X := T) ℓ)
  have hGb : ∀ m,
      Function.Bijective (fun y : Ext ΛT ΛT m => (Ext.mk₀ eG.hom).comp y (zero_add m)) :=
    Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso eG.hom
  let adjN := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) n
  have hβ : ∀ q, Function.Bijective (Stacks.ExtAdjunction.extMap adjN (iS.obj G) ΛY q) :=
    Stacks.ExtAdjunction.extMap_bijective adjN (iS.obj G) ΛY
  refine ⟨((Nat.card_eq_of_bijective _ (hβ 2)).symm.trans
      (Nat.card_eq_of_bijective _ (hγ.1 G 0)).symm).trans
        ((Nat.card_eq_of_bijective _ (hGb 0)).symm.trans hT0),
    fun q hq => have := hγ.2 G q hq; (hβ q).2.subsingleton, fun q hq => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have := subsingleton_ext_unitSheaf_of_isFinite_of_isSepClosed g ΛT m (by omega)
  have : Subsingleton (Ext G ΛT m) := (hGb m).2.subsingleton
  have : Subsingleton (Ext (iS.obj G) ((etaleModuleRestriction.{u, 0} (ZMod ℓ) n).obj ΛY)
    (m + 2)) := (hγ.1 G m).2.subsingleton
  exact (hβ (m + 2)).2.subsingleton

/-- **`Ext^q(Λ_Y, C)` at the skyscraper of a point.** For `C = n_! i_* (i ≫ n)^{-1} Λ_Y` with `T`
connected and finite over `k`, `Ext⁰(Λ_Y, C)` has `ℓ` elements and `Ext^q(Λ_Y, C) = 0` for
`q > 0`. -/
private theorem natCard_ext_unitSheaf_extensionByZero_directImage_point {N T : Scheme.{u}}
    (n : N ⟶ Y) [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i] [IsClosedImmersion (i ≫ n)]
    (g : T ⟶ Spec (.of k)) [IsFinite g] [ConnectedSpace T] :
    Nat.card (Ext (unitSheaf (X := Y) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
            ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
        0) = ℓ ∧
      ∀ q, 0 < q → Subsingleton (Ext (unitSheaf (X := Y) ℓ)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
            ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
              ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
                ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
          q) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let ΛY := unitSheaf (X := Y) ℓ
  let ΛT := unitSheaf (X := T) ℓ
  let G := (etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
    ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj ΛY)
  let C := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G)
  let eG : G ≅ ΛT := unitSheafRestrictionIdInverseImageIso ℓ (i ≫ n)
  let ι := i ≫ n
  let e₁ : C ≅ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).obj G :=
    (etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i (𝟙 T) n ι
        (IsPullback.of_vert_isIso_mono ⟨by simp [ι]⟩)).app G ≪≫
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).mapIso
        ((etaleModuleExtensionByZeroIdIso (ZMod ℓ) T).app G)
  let adjι := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) ι
  have hα : ∀ q, Function.Bijective (fun x : Ext ΛY C q =>
      ((Ext.mk₀ (unitSheafInverseImageIsoOfClosed ι).inv).comp
        ((Stacks.ExtAdjunction.extMap adjι ΛY G q) (x.comp (Ext.mk₀ e₁.hom) (add_zero q)))
          (zero_add q)).comp (Ext.mk₀ eG.hom) (add_zero q)) := fun q =>
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso eG.hom q).comp
      ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q).comp
        ((Stacks.ExtAdjunction.extMap_bijective adjι ΛY G q).comp
          (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso e₁.hom q)))
  refine ⟨(Nat.card_eq_of_bijective _ (hα 0)).trans
    ((Nat.card_congr (Ext.homEquiv₀ (X := ΛT) (Y := ΛT))).trans
      (natCard_end_unitSheaf (X := T) ℓ)), fun q hq => ?_⟩
  have := subsingleton_ext_unitSheaf_of_isFinite_of_isSepClosed g ΛT q hq
  exact (hα q).1.subsingleton

include f in
/-- **A nonvanishing trace at the skyscraper of a point.** Let `V ≠ Y` be a nonempty open with
`V ∪ n(N) = Y` and `n(i(T)) = n(N) ∖ V`, and `C = n_! i_* (i ≫ n)^{-1} Λ_Y`. For every injective
trace `t` on `H²(Y, Λ)` there are `x ∈ Ext⁰(Λ_Y, C)` and `w ∈ Ext²(C, Λ_Y)` with
`t (x ∘ w) ≠ 0`. -/
private theorem exists_trace_comp_ne_zero_point (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    {N T : Scheme.{u}} (n : N ⟶ Y) [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i]
    (V : Y.Opens) (hVt : V ≠ ⊤) [Nonempty V]
    (hi : Set.range (i ≫ n).base = Set.range n.base \ (V : Set Y))
    (htop : V ⊔ n.opensRange = ⊤) :
    ∃ (x : Ext (unitSheaf (X := Y) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
            ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
        0)
      (w : Ext
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
            ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
        (unitSheaf (X := Y) ℓ) 2),
      t (x.comp w (zero_add 2)) ≠ 0 := by
  have hp : ℓ.Prime := Fact.out
  let ΛY := unitSheaf (X := Y) ℓ
  obtain ⟨S, hS, ⟨e₁'⟩, ⟨e₂'⟩, ⟨e₃'⟩⟩ :=
    exists_shortExact_extensionByZero_sup_stratum (ZMod ℓ) V n i hi ΛY
  rw [htop] at e₂'
  have := isIso_etaleModuleExtensionByZeroAdj_counit_app_top (ZMod ℓ) ΛY
  let eY : S.X₂ ≅ ΛY := e₂' ≪≫
    asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (⊤ : Y.Opens).ι).counit.app ΛY)
  have : Subsingleton (Ext S.X₁ ΛY 2) :=
    have := subsingleton_ext_two_extensionByZeroOfRestriction_of_ne_top (ℓ := ℓ) f V hVt 2
      (by omega)
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := ΛY) e₁'.hom 2).2.subsingleton
  have hY2 : Nat.card (Ext ΛY ΛY 2) = ℓ := natCard_ext_two_unitSheaf f hℓ
  have : Finite (Ext ΛY ΛY 2) := Nat.finite_of_card_ne_zero (hY2.trans_ne hp.ne_zero)
  have : Nontrivial (Ext ΛY ΛY 2) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hY2]
    exact hp.one_lt)
  obtain ⟨z, hz⟩ := exists_ne (0 : Ext ΛY ΛY 2)
  obtain ⟨x₂, hx₂⟩ := (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso eY.inv 2).2 z
  obtain ⟨x₃, hx₃⟩ := Ext.contravariant_sequence_exact₂ hS ΛY x₂ (Subsingleton.elim _ _)
  have hxw : (Ext.mk₀ (eY.inv ≫ S.g ≫ e₃'.hom)).comp ((Ext.mk₀ e₃'.inv).comp x₃ (zero_add 2))
      (zero_add 2) = z := by
    rw [← hx₂, ← hx₃]
    change (Ext.mk₀ (eY.inv ≫ S.g ≫ e₃'.hom)).comp ((Ext.mk₀ e₃'.inv).comp x₃ (zero_add 2))
      (zero_add 2) = (Ext.mk₀ eY.inv).comp ((Ext.mk₀ S.g).comp x₃ (zero_add 2)) (zero_add 2)
    rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  refine ⟨Ext.mk₀ (eY.inv ≫ S.g ≫ e₃'.hom), (Ext.mk₀ e₃'.inv).comp x₃ (zero_add 2), ?_⟩
  rw [hxw]
  exact fun h0 => hz (ht (h0.trans (map_zero t).symm))

include f in
/-- **Poincaré duality at the skyscraper sheaf of a closed point of a smooth proper curve.** Let
`T` be a connected scheme finite over `k`, `i : T → N` a closed immersion into an open `n : N → Y`
with `i ≫ n` a closed immersion, and `γ` a purity class of `i` in degree `2` for `n^{-1} Λ_Y`. If
`V ≠ Y` is a nonempty open with `V ∪ n(N) = Y` and `n(i(T)) = n(N) ∖ V`, then for every injective
trace `t` on `H²(Y, Λ)` duality holds on `Y` at `C = n_! i_* (i ≫ n)^{-1} Λ_Y` (the skyscraper of
the point), and `Ext^q(C, Λ_Y) = 0` for `q > 2`. -/
theorem isDualityPerfect_extensionByZero_directImage_point (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    {N T : Scheme.{u}} (n : N ⟶ Y) [IsOpenImmersion n] (i : T ⟶ N) [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ n)] (g : T ⟶ Spec (.of k)) [IsFinite g] [ConnectedSpace T]
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) n).obj (unitSheaf (X := Y) ℓ)) 2)
    (hγ : IsPurityClass i _ γ) (V : Y.Opens) (hVt : V ≠ ⊤) [Nonempty V]
    (hi : Set.range (i ≫ n).base = Set.range n.base \ (V : Set Y))
    (htop : V ⊔ n.opensRange = ⊤) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ))))) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (𝟙 T)).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) (i ≫ n)).obj (unitSheaf (X := Y) ℓ)))))
        (unitSheaf (X := Y) ℓ) q) := by
  obtain ⟨hD2, hDlow, hDhigh⟩ := natCard_ext_extensionByZero_directImage_point n i g γ hγ
  obtain ⟨hO0, hOq⟩ := natCard_ext_unitSheaf_extensionByZero_directImage_point (ℓ := ℓ) n i g
  obtain ⟨x, w, hxw⟩ := exists_trace_comp_ne_zero_point f hℓ t ht n i V hVt hi htop
  refine ⟨?_, hDhigh⟩
  intro a b hab
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 1) ∨ (a = 2 ∧ b = 0) := by omega
  · exact bijective_dualityPairing_of_natCard_eq_prime t hab hO0 hD2 x w hxw
  · exact bijective_dualityPairing_of_subsingleton t hab (hOq 1 (by omega)) (hDlow 1 (by omega))
  · exact bijective_dualityPairing_of_subsingleton t hab (hOq 2 (by omega)) (hDlow 0 (by omega))

end Point

end Stacks.EtaleCohomology

end
