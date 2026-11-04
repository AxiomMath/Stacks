module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.GoodTraceExistence

/-!
# The class of a point in top compactly supported cohomology: reduction to its nonvanishing

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`. For `W`
smooth irreducible of relative dimension `e` over `k` with a compactification `j : W → X̄`, and a
`k`-point `i : P → N` closed in an open `n : N → W` with a purity class `γ` of degree `2e`, the
point-class map

`z ↦ z ∘ (n ≫ j)_! γ : Ext⁰_X̄(Λ, (n ≫ j)_! i_* Λ_P) → H^{2e}_c(W)`

goes between two groups with `ℓ` elements: the target by the count
`Stacks.EtaleCohomology.nonempty_ext_top_addEquiv_zmod`, the source because
`(n ≫ j)_! i_* Λ_P = ι_* t_! Λ_P` for the closure `ι : P̄ → X̄` of `P` and the open immersion
`t : P → P̄`, `Ext⁰_X̄(Λ, ι_* -) = Ext⁰_{P̄}(Λ, -)`, and `H⁰_c(P) = Λ`
(`Stacks.EtaleCohomology.nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero`).
An additive map between two groups of prime order is bijective as soon as it is nonzero. So
`Stacks.EtaleCohomology.TopCohomologyPointClass` follows from the count and from the
nonvanishing of the point-class map (`Stacks.EtaleCohomology.TopCohomologyPointClassNonzero`).

## Main results

* `Stacks.EtaleCohomology.nonempty_ext_zero_point_addEquiv_zmod`: the source has `ℓ` elements.
* `Stacks.EtaleCohomology.bijective_of_ne_zero_of_addEquiv_zmod`.
* `Stacks.EtaleCohomology.topCohomologyPointClass_of_nonzero`.
* `Stacks.EtaleCohomology.topCohomologyPointClassNonzero_of_exists`: it suffices to test one class
  supported at the point, not necessarily a purity class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

/-- **An additive map between two groups of prime order `ℓ` is bijective once it is nonzero.** -/
theorem bijective_of_ne_zero_of_addEquiv_zmod {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (eA : A ≃+ ZMod ℓ) (eB : B ≃+ ZMod ℓ) (φ : A →+ B)
    (hφ : φ ≠ 0) : Function.Bijective φ := by
  let ψ : ZMod ℓ →+ ZMod ℓ := eB.toAddMonoidHom.comp (φ.comp eA.symm.toAddMonoidHom)
  have hψ : ∀ x, ψ x = x * ψ 1 := by
    intro x
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← nsmul_one, map_nsmul]
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  have h1 : ψ 1 ≠ 0 := by
    intro h0
    apply hφ
    ext a
    have := hψ (eA a)
    rw [h0, mul_zero] at this
    simpa [ψ] using this
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨y * (ψ 1)⁻¹, ?_⟩⟩
    · rw [hψ x, hψ y] at hxy
      exact mul_right_cancel₀ h1 hxy
    · rw [hψ, mul_assoc, inv_mul_cancel₀ h1, mul_one]
  have hφeq : (φ : A → B) = eB.symm ∘ ψ ∘ eA := by
    funext a
    simp [ψ]
  rw [hφeq]
  exact eB.symm.bijective.comp (hbij.comp eA.bijective)

section Point

variable {k : Type u} [Field k]

attribute [local instance] isClosedImmersion_restrictOpen_closedSpaceι
  preservesFiniteColimits_restrictOpen_closedSpaceι

/-- **`H⁰_c` of a point is `ℤ/N`, read on the compactification of the ambient variety**: for a
point `i : P → N` (irreducible, smooth of relative dimension zero over `k`) closed in an open
`n : N → W` of a noetherian `W` with a compactification `j : W → X̄`,
`Ext⁰_X̄(Λ, (n ≫ j)_! i_* Λ_P) ≅ ℤ/N`. -/
theorem nonempty_ext_zero_point_addEquiv_zmod (N : ℕ) [NeZero N] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of k)) [TopologicalSpace.NoetherianSpace W]
    (jc : CompactificationOf (Over.mk f)) {M P : Scheme.{u}} (n : M ⟶ W) [IsOpenImmersion n]
    (i : P ⟶ M) [IsClosedImmersion i] [IrreducibleSpace P]
    [SmoothOfRelativeDimension 0 (i ≫ n ≫ f)] :
    Nonempty (Ext (unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) (n ≫ jc.immersion)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod N) i).obj (unitSheaf (X := P) N))) 0 ≃+
      ZMod N) := by
  have : TopologicalSpace.NoetherianSpace M := n.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (n ≫ f) := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : TopologicalSpace.NoetherianSpace P := (i ≫ n).isEmbedding.isInducing.noetherianSpace
  let jP := (jc.restrictOpen n).restrictClosed i
  let t := ((jc.restrictOpen n).closedImmersion i).toImage
  let ι : (jc.restrictOpen n).closedSpace i ⟶ jc.space := (jc.restrictOpen n).closedSpaceι i
  let sq := (jc.restrictOpen n).isPullback_restrictClosed i
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod N) ι
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod N) ι
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (ZMod N) ι
  let G := (etaleModuleExtensionByZero.{u, 0} (ZMod N) t).obj (unitSheaf (X := P) N)
  let eD := (etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod N) i t (n ≫ jc.immersion) ι
    sq).app (unitSheaf (X := P) N)
  -- `Ext⁰_X̄(Λ, (n ≫ j)_! i_* Λ_P) ≅ Ext⁰_X̄(Λ, ι_* t_! Λ_P)`
  let e₁ := AddEquiv.ofBijective ((Ext.mk₀ eD.hom).postcomp (unitSheaf (X := jc.space) N)
    (add_zero 0)) (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso eD.hom 0)
  -- `Ext⁰_X̄(Λ, ι_* G) ≅ Ext⁰_{P̄}(ι⁻¹ Λ, G) ≅ Ext⁰_{P̄}(Λ, G)`
  let e₂ := AddEquiv.ofBijective (Stacks.ExtAdjunction.extMap adj (unitSheaf (X := jc.space) N)
    G 0) (Stacks.ExtAdjunction.extMap_zero_bijective adj _ _)
  let eU : (etaleModuleInverseImage.{u, 0} (ZMod N) ι).obj (unitSheaf (X := jc.space) N) ≅
      unitSheaf (X := (jc.restrictOpen n).closedSpace i) N :=
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) ι).app
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))
  let e₃ := AddEquiv.ofBijective ((Ext.mk₀ eU.inv).precomp G (zero_add 0))
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso eU.inv 0)
  obtain ⟨e₄⟩ := nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero N
    (i ≫ n ≫ f) jP
  exact ⟨e₁.trans (e₂.trans (e₃.trans e₄))⟩

end Point

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- **The class of a point in top compactly supported cohomology is nonzero**: for `W` smooth
irreducible of relative dimension `e` over `k`, noetherian, with a compactification `j : W → X̄`,
and a `k`-point `i : P → N` closed in an open `n : N → W` with a purity class `γ` of degree `2e`,
some `z ∈ Ext⁰_X̄(Λ, (n ≫ j)_! i_* Λ_P)` has `z ∘ (n ≫ j)_! γ ≠ 0` in `H^{2e}_c(W)`. -/
def TopCohomologyPointClassNonzero : Prop :=
  ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f))
    (N P : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : P ⟶ N) [IsClosedImmersion i]
      [IrreducibleSpace P] [SmoothOfRelativeDimension 0 (i ≫ n ≫ f)]
      (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ))) (2 * e)),
      IsPurityClass i _ γ →
        ∃ z : Ext (unitSheaf (X := jc.space) ℓ)
            ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
              ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))) 0,
          z.comp (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
            (n ≫ jc.immersion)) _ _ (2 * e) γ) (zero_add _) ≠ 0

variable {k}

/-- **`H^{2e}_c(W) ≅ Λ`, freely generated by the class of a point**
(`Stacks.EtaleCohomology.TopCohomologyPointClass`), from the count
(`Stacks.EtaleCohomology.nonempty_ext_top_addEquiv_zmod`: dense elementary fibrations and
`R²f_! Λ ≅ Λ` for them) and the nonvanishing of the class of a point: the point-class map goes
between two groups with `ℓ` elements. -/
theorem topCohomologyPointClass_of_nonzero [IsAlgClosed k] (hℓ : IsUnit (ℓ : k))
    (hfib : ExistsDenseElementaryFibration k)
    (hR2 : HigherDirectImageTwoOfElementaryFibration k ℓ)
    (hnz : TopCohomologyPointClassNonzero ℓ k) : TopCohomologyPointClass ℓ k := by
  intro e W f _ _ _ jc
  obtain ⟨eB⟩ := nonempty_ext_top_addEquiv_zmod ℓ hℓ hfib hR2 e W f jc
  refine ⟨⟨eB⟩, fun N P n _ i _ _ _ γ hγ => ?_⟩
  obtain ⟨eA⟩ := nonempty_ext_zero_point_addEquiv_zmod ℓ f jc n i
  let φ := (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
    (n ≫ jc.immersion)) _ _ (2 * e) γ).postcomp (unitSheaf (X := jc.space) ℓ) (zero_add _)
  obtain ⟨z, hz⟩ := hnz e W f jc N P n i γ hγ
  exact bijective_of_ne_zero_of_addEquiv_zmod eA eB φ fun h =>
    hz (by simpa [φ] using congrArg (fun ψ : _ →+ _ => ψ z) h)

/-- **Every class of degree `c` supported on `T` factors through a purity class**: if `γ` is a
purity class for `i : T → Y` in degree `c`, every `γ₀ ∈ Ext^c_Y(i_* Λ_T, A)` is `i_* v ∘ γ` for
some `v ∈ Ext⁰_T(Λ_T, Λ_T)`. -/
theorem exists_mapExactFunctor_comp_eq_of_isPurityClass {T Y : Scheme.{u}} (i : T ⟶ Y)
    [IsClosedImmersion i] (A : EtaleModules.{u, 0} (ZMod ℓ) Y) {c c' : ℕ}
    (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) A c)
    (hγ : IsPurityClass i A γ) (h : 0 + c = c')
    (γ₀ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ)) A c') :
    ∃ v : Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) 0,
      (v.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ h = γ₀ := by
  subst h
  exact (hγ.1 _ 0).2 γ₀

/-- **The nonvanishing of the class of a point may be tested on any class supported at the
point**: if some `γ₀ ∈ Ext^{2e}_N(i_* Λ_P, (n ≫ j)⁻¹ j_! Λ_W)` (not necessarily a purity class)
has `z ∘ (n ≫ j)_! γ₀ ≠ 0` for some `z`, then the same holds for every purity class `γ`, since
`γ₀ = i_* v ∘ γ` (`Stacks.EtaleCohomology.exists_mapExactFunctor_comp_eq_of_isPurityClass`).
So `Stacks.EtaleCohomology.TopCohomologyPointClassNonzero` may be proved with a convenient class,
for instance a Kummer flag class. -/
theorem topCohomologyPointClassNonzero_of_exists
    (hex : ∀ (e : ℕ) (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f))
      (N P : Scheme.{u}) (n : N ⟶ W) [IsOpenImmersion n] (i : P ⟶ N) [IsClosedImmersion i]
        [IrreducibleSpace P] [SmoothOfRelativeDimension 0 (i ≫ n ≫ f)]
        (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))
          ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
              (unitSheaf (X := W) ℓ))) (2 * e)),
        IsPurityClass i _ γ →
          ∃ (γ₀ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))
              ((etaleModuleRestriction.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
                ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
                  (unitSheaf (X := W) ℓ))) (2 * e))
            (z : Ext (unitSheaf (X := jc.space) ℓ)
              ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
                ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ))) 0),
            z.comp (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
              (n ≫ jc.immersion)) _ _ (2 * e) γ₀) (zero_add _) ≠ 0) :
    TopCohomologyPointClassNonzero ℓ k := by
  intro e W f _ _ _ jc N P n _ i _ _ _ γ hγ
  obtain ⟨γ₀, z, hz⟩ := hex e W f jc N P n i γ hγ
  obtain ⟨v, rfl⟩ := exists_mapExactFunctor_comp_eq_of_isPurityClass ℓ i _ γ hγ (zero_add _) γ₀
  refine ⟨z.comp ((v.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).mapExactFunctor
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion))) (zero_add 0), ?_⟩
  rw [Stacks.ExtAdjunction.extMap_comp] at hz
  rwa [Ext.comp_assoc _ _ _ (zero_add 0) (zero_add _) (by omega)]

end Stacks.EtaleCohomology

end
