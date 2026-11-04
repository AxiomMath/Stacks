module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFunctionPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RationalPointChart
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible

/-!
# The Frobenius on top-degree cohomology is multiplication by `q^d`

Let `X` be separated and quasi-compact over the finite field `k` with `q = p^f` elements, `k̄`
an algebraically closed extension, `Y = X_k̄` connected and smooth of relative dimension `d`, and
`ℓ` a prime invertible in `k̄`. Suppose `X` has a `k`-rational point `x`. Then restriction along
`π̄ = π_X × id` is multiplication by `q^d` on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)`
(`Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_top`), given that
`H^{2d}(Y, ℤ/ℓⁿ⁺¹)` is cyclic of order `ℓⁿ⁺¹` and that the Kummer point class of `x` is not
divisible by `ℓ` (`Stacks.EtaleCohomology.RationalPointKummerClassNondivisible`).

The proof: étale coordinates `ψ : V ⟶ 𝐀^d_k` centred at `x` over `k`
(`Stacks.EtaleCohomology.exists_etale_affineSpace_centred_rationalPoint`) pull back to functions
`φ_m = pr^♯ ψ_m` on the affine open `U = pr⁻¹(V)` of `Y`. The map `π̄` preserves `U`, and since it
lies over `π_X = F_X^f`, it raises every `φ_m` to the `q`-th power
(`Stacks.EtaleCohomology.appTop_resLE_geometricFrobeniusBaseChange`). The common zero set of the
`φ_m` is the fibre of `x`, which is closed in `Y`, so the map adapted to the Kummer flag of the
`φ_m` exists and is unique (`Stacks.EtaleCohomology.KummerFlag.existsUnique_isAdapted`), and the
restriction along `π̄` of the Kummer point class `η₀` is `q^d η₀`
(`Stacks.EtaleCohomology.KummerFlag.constantExtRestriction_kummerPointClass_functionDatum`).
Not divisible by `ℓ` in the cyclic group `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` of order `ℓⁿ⁺¹`, `η₀` generates it,
and restriction is additive.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Cyclic

/-- **In a cyclic group of order `ℓⁿ⁺¹`, an element not divisible by `ℓ` generates.** -/
theorem exists_nsmul_eq_of_not_exists_eq_nsmul {ℓ n : ℕ} [hℓ : Fact ℓ.Prime] {H : Type*}
    [AddCommGroup H] (e : H ≃+ ZMod (ℓ ^ (n + 1))) {η : H} (hη : ¬ ∃ w, η = ℓ • w) (z : H) :
    ∃ m : ℕ, z = m • η := by
  have hu : IsUnit (e η) := by
    rw [← ZMod.natCast_zmod_val (e η), ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ.out).2 ?_))
    rintro ⟨c, hc⟩
    apply hη
    refine ⟨e.symm c, e.injective ?_⟩
    rw [map_nsmul, AddEquiv.apply_symm_apply, nsmul_eq_mul, ← ZMod.natCast_zmod_val (e η), hc]
    push_cast
    ring
  obtain ⟨v, hv⟩ := hu
  refine ⟨(e z * ↑v⁻¹).val, e.injective ?_⟩
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, ← hv, Units.inv_mul_cancel_right]

end Cyclic

section Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- The `m`-th power of the absolute Frobenius of `Z` is the identity on points. -/
theorem absoluteFrobenius_pow_base_apply (Z : Scheme.{u}) (hZ : IsInCharacteristic Z p) (m : ℕ)
    (z : Z) : (End.asHom (End.of (absoluteFrobenius Z p hZ) ^ m)).base z = z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, End.mul_def]
    show (End.asHom (End.of (absoluteFrobenius Z p hZ) ^ m)).base
      ((absoluteFrobenius Z p hZ).base z) = z
    rw [absoluteFrobenius_apply, ih]

/-- The `m`-th power of the absolute Frobenius commutes with every morphism `g : A ⟶ B` of schemes
in characteristic `p`. -/
theorem absoluteFrobenius_pow_naturality {A B : Scheme.{u}} (g : A ⟶ B)
    (hA : IsInCharacteristic A p) (hB : IsInCharacteristic B p) (m : ℕ) :
    End.asHom (End.of (absoluteFrobenius A p hA) ^ m) ≫ g =
      g ≫ End.asHom (End.of (absoluteFrobenius B p hB) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ, End.mul_def]
    show (absoluteFrobenius A p hA ≫ End.asHom (End.of (absoluteFrobenius A p hA) ^ m)) ≫ g =
      g ≫ (absoluteFrobenius B p hB ≫ End.asHom (End.of (absoluteFrobenius B p hB) ^ m))
    rw [Category.assoc, ih, ← Category.assoc, absoluteFrobenius_naturality g p hA hB,
      Category.assoc]

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (q : ℕ) [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- `π̄ = π_X × id` preserves the preimage of every open of `X`. -/
theorem preimage_fieldBaseChangeProj_geometricFrobeniusBaseChange (V : X.Opens) :
    geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard ⁻¹ᵁ
        (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V) =
      fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, fieldBaseChangeProj, geometricFrobeniusBaseChange_comp_fst,
    Scheme.Hom.comp_preimage]
  congr 1
  ext x
  show (End.asHom (End.of (absoluteFrobenius X p (isInCharacteristic_of_over (Over.mk f))) ^
    q)).base x ∈ V ↔ x ∈ V
  rw [absoluteFrobenius_pow_base_apply]

/-- **`π̄` raises the pullback of a function on `X` to the `q`-th power.** -/
theorem appTop_resLE_geometricFrobeniusBaseChange (V : X.Opens) (ψ : Γ(V.toScheme, ⊤))
    (hle : fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V ≤
      geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard ⁻¹ᵁ
        (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V)) :
    ((geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard).resLE _ _ hle).appTop
        ((fieldBaseChangeProj (Over.mk f) kbar ∣_ V).appTop ψ) =
      ((fieldBaseChangeProj (Over.mk f) kbar ∣_ V).appTop ψ) ^ (p ^ q) := by
  have hX : IsInCharacteristic X p := isInCharacteristic_of_over (Over.mk f)
  have hV : IsInCharacteristic V.toScheme p := isInCharacteristic_of_hom V.ι p hX
  have h1 : (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard).resLE _ _ hle ≫
      (fieldBaseChangeProj (Over.mk f) kbar ∣_ V) =
        (fieldBaseChangeProj (Over.mk f) kbar ∣_ V) ≫
          End.asHom (End.of (absoluteFrobenius V.toScheme p hV) ^ q) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      absoluteFrobenius_pow_naturality p V.ι hV hX q,
      ← Category.assoc (fieldBaseChangeProj (Over.mk f) kbar ∣_ V), morphismRestrict_ι,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc,
      fieldBaseChangeProj, geometricFrobeniusBaseChange_comp_fst]
    rfl
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h1, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, absoluteFrobenius_pow_appTop_apply, map_pow]

end Frobenius

section Main

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (ℓ d : ℕ)

/-- **The Kummer flag of a chart**: for an affine open `V` of `X` and `π : V ⟶ 𝐀^d_k`, the divisor
data on the affine open `pr⁻¹(V)` of `X_k̄` of the pullbacks `pr^♯ ψ_m` of the coordinates
`ψ_m = π^♯ T_m` (`Stacks.EtaleCohomology.KummerFlag.functionDatum`). -/
def chartDatum (V : X.Opens) (hV : IsAffineOpen V)
    (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))) :
    Fin d → KummerFlag.DivisorDatum (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).toScheme :=
  haveI : IsAffineHom (fieldBaseChangeProj (Over.mk f) kbar) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip
      inferInstance
  haveI : IsAffine (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).toScheme := hV.preimage _
  fun m => KummerFlag.functionDatum ((fieldBaseChangeProj (Over.mk f) kbar ∣_ V).appTop
    (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m))))

/-- **The Kummer point class of a rational point is not divisible by `ℓ`.** For every level
`N = ℓⁿ⁺¹`, every primitive `N`-th root of unity `ζ ∈ k̄`, every `k`-rational point `x = s(pt)` of
`X` and every étale `π : V ⟶ 𝐀^d_k` over `k` on an affine open `V ∋ x` whose coordinates vanish
simultaneously exactly at `x`, the Kummer point class in `H^{2d}(X_k̄, ℤ/N)` of the pulled back
coordinates (`Stacks.EtaleCohomology.chartDatum`) through the adapted map is not `ℓ` times a
class.

It holds by the theory of the cycle class of a point: the Kummer point class of étale coordinates
centred at a `k̄`-point is the class of that point, which generates `H^{2d}(X_k̄, ℤ/N)`. -/
def RationalPointKummerClassNondivisible : Prop :=
  ∀ (n : ℕ) {ζ : kbar} (hζ : IsPrimitiveRoot ζ (ℓ ^ (n + 1)))
    (hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar)) (s : Spec (.of k) ⟶ X), s ≫ f = 𝟙 _ →
    ∀ (V : X.Opens) (hV : IsAffineOpen V)
      (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))), Etale π →
      π ≫ (𝔸(ULift.{u} (Fin d); Spec (.of k)) ↘ Spec (.of k)) = V.ι ≫ f →
      (∃ v : V, V.ι.base v ∈ Set.range s.base) →
      (∀ v : V, (∀ m : Fin d, v ∉ V.toScheme.basicOpen
          (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))) ↔
        V.ι.base v ∈ Set.range s.base) →
      ∀ z : unitSheaf (X := fieldBaseChange (Over.mk f) kbar) (ℓ ^ (n + 1)) ⟶
          (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι).obj
            (KummerFlag.flagSheaf (N := ℓ ^ (n + 1)) (chartDatum f kbar d V hV π)),
        KummerFlag.IsAdapted (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι
          (KummerFlag.flagUnit (N := ℓ ^ (n + 1)) (chartDatum f kbar d V hV π)) z →
        ¬ ∃ w, KummerFlag.kummerPointClass hζ hN
          (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
          (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι (chartDatum f kbar d V hV π) z = ℓ • w

/-- A point in the image of a `k`-rational point `s` lies in every open meeting that image. -/
private theorem mem_of_mem_range_of_rationalPoint {s : Spec (.of k) ⟶ X} {V : X.Opens} {v₀ : V}
    (hv₀ : V.ι.base v₀ ∈ Set.range s.base) {x : X} (hx : x ∈ Set.range s.base) : x ∈ V := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨t₀, ht₀⟩ := hv₀
  rw [Subsingleton.elim t t₀, ht₀]
  exact v₀.2

/-- A point of `pr⁻¹(V)` outside every `D(pr^♯ ψ_m)` lies over the common zero set of the `ψ_m`. -/
private theorem fieldBaseChangeProj_mem_range_of_forall_not_mem_basicOpen {s : Spec (.of k) ⟶ X}
    {V : X.Opens} {π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))}
    (hiff : ∀ v : V, (∀ m : Fin d, v ∉ V.toScheme.basicOpen
      (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))) → V.ι.base v ∈ Set.range s.base)
    (x : (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).toScheme)
    (hx : ∀ m : Fin d, x ∉ (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).toScheme.basicOpen
      ((fieldBaseChangeProj (Over.mk f) kbar ∣_ V).appTop
        (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m))))) :
    (fieldBaseChangeProj (Over.mk f) kbar).base
      ((fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι.base x) ∈ Set.range s.base := by
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
  exact hiff _ fun m hm => hx m (by rwa [← Scheme.preimage_basicOpen_top])

/-- The preimage in a connected smooth `X_k̄` of a nonempty open of a quasi-compact `X` is
irreducible. -/
private theorem irreducibleSpace_preimage_fieldBaseChangeProj [QuasiCompact f]
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (V : X.Opens) (v₀ : V) :
    IrreducibleSpace (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).toScheme := by
  let fY := pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)
  have : Smooth fY := SmoothOfRelativeDimension.smooth d fY
  have : QuasiCompact (Over.mk f).hom := ‹QuasiCompact f›
  have : CompactSpace (fieldBaseChange (Over.mk f) kbar) := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := fY) Set.univ isOpen_univ isCompact_univ⟩
  have : IrreducibleSpace (fieldBaseChange (Over.mk f) kbar) :=
    irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace fY
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (V.ι.base v₀)
    (default : Spec (.of kbar)) (f := f) (g := specAlgebraMap k kbar) (Subsingleton.elim _ _)
  have hy₀U : y₀ ∈ fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V := by
    show (pullback.fst f (specAlgebraMap k kbar)).base y₀ ∈ V
    rw [hy₀]
    exact v₀.2
  exact Subtype.irreducibleSpace ((IrreducibleSpace.isIrreducible_univ _).2.subset_irreducible
    ⟨y₀, hy₀U⟩ (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).isOpen subset_rfl (Set.subset_univ _))

/-- **The Kummer point class of a chart is multiplied by `q^d` under `π̄`**: for a `k`-rational
point `s` in an affine open `V` with coordinates `π` vanishing simultaneously only on the image of
`s`, the Kummer point class of `Stacks.EtaleCohomology.chartDatum` through some adapted map is
multiplied by `q^d` under restriction along `π̄ = π_X × id`. -/
private theorem exists_isAdapted_constantExtRestriction_kummerPointClass_chartDatum [Fintype k]
    [QuasiCompact f] [IsSeparated f] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] {N : ℕ} [NeZero N] {ζ : kbar}
    (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : kbar)) (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) (V : X.Opens) (hV : IsAffineOpen V)
    (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of k))) (v₀ : V)
    (hv₀ : V.ι.base v₀ ∈ Set.range s.base)
    (hiff : ∀ v : V, (∀ m : Fin d, v ∉ V.toScheme.basicOpen
      (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))) → V.ι.base v ∈ Set.range s.base) :
    ∃ z, KummerFlag.IsAdapted (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι
        (KummerFlag.flagUnit (N := N) (chartDatum f kbar d V hV π)) z ∧
      constantExtRestriction (ZMod N) (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
          (2 * d) (KummerFlag.kummerPointClass hζ hN
            (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
            (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι (chartDatum f kbar d V hV π) z) =
        ((p ^ q) ^ d : ℕ) • KummerFlag.kummerPointClass hζ hN
          (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
          (fieldBaseChangeProj (Over.mk f) kbar ⁻¹ᵁ V).ι (chartDatum f kbar d V hV π) z := by
  let pr := fieldBaseChangeProj (Over.mk f) kbar
  let U := pr ⁻¹ᵁ V
  have : IsAffineHom pr :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip
      inferInstance
  have : IsAffine U.toScheme := hV.preimage _
  have : IrreducibleSpace U.toScheme := irreducibleSpace_preimage_fieldBaseChangeProj f kbar d V v₀
  let φ : Fin d → Γ(U.toScheme, ⊤) := fun m =>
    (pr ∣_ V).appTop (π.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up m)))
  have hpre := preimage_fieldBaseChangeProj_geometricFrobeniusBaseChange p f kbar q hcard V
  let g := (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard).resLE U U hpre.ge
  have sq : IsPullback g U.ι U.ι (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) :=
    IsOpenImmersion.isPullback g U.ι U.ι _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by rw [Scheme.Opens.opensRange_ι]; exact hpre)
  have hφ : ∀ m, g.appTop (φ m) = φ m ^ (p ^ q) := fun m =>
    appTop_resLE_geometricFrobeniusBaseChange p f kbar q hcard V _ hpre.ge
  have : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  have hZc : IsClosed (pr.base ⁻¹' Set.range s.base) :=
    s.isClosedEmbedding.isClosed_range.preimage pr.continuous
  let O : (fieldBaseChange (Over.mk f) kbar).Opens := ⟨_, hZc.isOpen_compl⟩
  obtain ⟨z₀, hz₀, huniq⟩ := KummerFlag.existsUnique_isAdapted (N := N) U.ι O.ι
    (fun m => KummerFlag.functionDatum (φ m)) (fun y => by
      by_cases hy : pr.base y ∈ Set.range s.base
      · left
        rw [Scheme.Opens.range_ι]
        exact mem_of_mem_range_of_rationalPoint hv₀ hy
      · right
        rw [Scheme.Opens.range_ι]
        exact hy) (fun x hx => by
      by_contra hcon
      push Not at hcon
      rw [Scheme.Opens.range_ι] at hx
      apply hx
      refine fieldBaseChangeProj_mem_range_of_forall_not_mem_basicOpen f kbar d hiff x
        fun m hm => ?_
      have hxm := hcon m
      change x ∈ Set.range (KummerFlag.zeroSchemeι (φ m)).base at hxm
      rw [KummerFlag.range_zeroSchemeι] at hxm
      exact hxm hm)
  exact ⟨z₀, hz₀, KummerFlag.constantExtRestriction_kummerPointClass_functionDatum hζ hN
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
    (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_snd _ _ _ _ _) U.ι g sq φ
    (pow_pos (Fact.out : p.Prime).pos q) hφ z₀ hz₀ huniq⟩

/-- **The geometric Frobenius on top-degree cohomology is multiplication by `q^d`.** Let `X` be
separated and quasi-compact over the finite field `k` with `q = p^f` elements, `k̄` algebraically
closed, `Y = X_k̄` connected and smooth of relative dimension `d` over `k̄`, and `ℓ` a prime
invertible in `k̄`. If `X` has a `k`-rational point (`hpt`), `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` is cyclic of order
`ℓⁿ⁺¹` (`hcount`, the conclusion of `Stacks.EtaleCohomology.nonempty_ext_top_addEquiv_zmod`) and
the Kummer point class of a rational point is not divisible by `ℓ` (`hgen`), then restriction along
`π̄ = π_X × id` is multiplication by `q^d` on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` for every `n`. -/
theorem constantExtRestriction_geometricFrobeniusBaseChange_top [Fintype k] [IsAlgClosed kbar]
    [Fact ℓ.Prime] [QuasiCompact f] [IsSeparated f] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (hpt : ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _)
    (hcount : ∀ m : ℕ, Nonempty (Ext (unitSheaf (X := fieldBaseChange (Over.mk f) kbar)
      (ℓ ^ (m + 1))) (unitSheaf (ℓ ^ (m + 1))) (2 * d) ≃+ ZMod (ℓ ^ (m + 1))))
    (hgen : RationalPointKummerClassNondivisible f kbar ℓ d) :
    ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z := by
  intro n z
  obtain ⟨s, hs⟩ := hpt
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hN : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar) := by
    rw [Nat.cast_pow]
    exact hℓ.pow _
  have : NeZero (((ℓ ^ (n + 1) : ℕ)) : kbar) := ⟨hN.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot kbar (ℓ ^ (n + 1))
  have : SmoothOfRelativeDimension d (pullback.snd f (specAlgebraMap k kbar)) :=
    ‹SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))›
  obtain ⟨V, hV, π, hπ, hover, ⟨v₀, hv₀⟩, hiff⟩ :=
    exists_etale_affineSpace_centred_rationalPoint f kbar d s hs
  obtain ⟨z₀, hz₀, hK⟩ := exists_isAdapted_constantExtRestriction_kummerPointClass_chartDatum
    f kbar d p q hcard hζ hN s hs V hV π v₀ hv₀ fun v => (hiff v).1
  obtain ⟨e⟩ := hcount n
  obtain ⟨m, rfl⟩ := exists_nsmul_eq_of_not_exists_eq_nsmul e
    (hgen n hζ hN s hs V hV π hπ hover ⟨v₀, hv₀⟩ hiff z₀ hz₀) z
  rw [map_nsmul, hK, smul_comm]

end Main

end Stacks.EtaleCohomology

end
