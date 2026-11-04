module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTopDegreeFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupPairingBounds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsForgetSupportsInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLisseLevelDualityOpenImmersion

/-!
# Finite-level Poincaré duality on a curve over a finite field, with bounded defect

Let `U` be a scheme over the finite field `k` with `q` elements, `j : U ⟶ X̄` a compactification
over `k`, `k̄` an algebraic closure, and suppose `Y = X̄_k̄` is a smooth proper curve over `k̄`.
Let `ℓ` be a prime invertible in `k̄`, `N = ℓⁿ⁺¹`, and `F`, `F'` ℓ-adic sheaves on `U` with
pairings `μₙ : j_! Fₙ ⊗ j_! F'ₙ ⟶ ℤ/N` on `X̄`. Suppose that `F'ₙ|_{U_k̄}` is lisse, that
`j_! F'ₙ|_Y` has flat fibres, that the restriction of the pulled back pairing to `U_k̄` is
perfect on geometric fibres, and that the local terms of `F` at the boundary are killed by `ℓ^K`
(`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`). Then the cup product pairings

`εₙ(x, y) = t(x ∪_{μₙ} y) : H¹_c(U_k̄, Fₙ) × H¹_c(U_k̄, F'ₙ) → H²(Y, ℤ/N) ≅ ℤ/N`

have left kernels killed by `ℓ^K`, right kernels killed by `ℓ^{2K}`, and are scaled by `q` under
the canonical geometric Frobenius
(`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve`).
This is the input of the ℓ-adic perfect pairing with bounded defect
(`Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_of_forall_zmodPow`) in Poincaré duality on
an affine curve, in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The proof: the levels of `H¹_c` are `H¹(Y, M)` and `H¹(Y, G)` for `M = pr^{-1} j_! Fₙ`,
`G = pr^{-1} j_! F'ₙ` (`Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_level_frobenius`).
Duality holds on `Y` at `G ≅ j'_! (F'ₙ|_{U_k̄})`
(`Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_lisse_zmodPow_of_isOpenImmersion`).
The map `Θ(a) = μ ∘ (a ⊗ G) ∘ λ⁻¹ : H¹(Y, M) → Ext¹(G, ℤ/N)` becomes, after the inverse image
`j'^{-1}` (injective on `Ext¹(G, ℤ/N)`, `G` being an extension by zero), the forgetting of supports
`H¹(Y, M) → H¹(U_k̄, Fₙ)` followed by the coefficient duality
`H¹(U_k̄, Fₙ) ≅ Ext¹(F'ₙ, ℤ/N)` (`Stacks.EtaleCohomology.bijective_tensorPairingExt`); forgetting
supports has kernel killed by `ℓ^K` and image containing `ℓ^{2K} H¹(U_k̄, Fₙ)`
(`Stacks.EtaleCohomology.LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy`), and
`Stacks.ExtCup.cup_nondegenerate_of_bounds` concludes. The Frobenius commutes with cup products
(`Stacks.EtaleCohomology.cup_adjunctionExtMap_frobeniusBaseChangeTwist`) and is multiplication by
`q` on `H²(Y, ℤ/N)`
(`Stacks.EtaleCohomology.constantExtRestriction_geometricFrobeniusBaseChange_two_of_curve`).

## Main results

* `Stacks.EtaleCohomology.exists_injective_trace_zmodPow_of_curve`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category (the ℓ-adic compactly supported cohomology), which is therefore a local instance
in the section `Main`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

section Trace

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

include f in
/-- **An injective trace on `H²(Y, ℤ/ℓⁿ)`** of a smooth proper curve over an algebraically closed
field in which `ℓ` is invertible: through a primitive `ℓⁿ`-th root of unity,
`H²(Y, ℤ/ℓⁿ) ≅ H²(Y, μ_{ℓⁿ}) ≅ ℤ/ℓⁿ`. -/
theorem exists_injective_trace_zmodPow_of_curve {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (n : ℕ) :
    ∃ t : Ext (unitSheaf (X := Y) (ℓ ^ n)) (unitSheaf (ℓ ^ n)) 2 →+ ZMod (ℓ ^ n),
      Function.Injective t := by
  have hp : ℓ.Prime := Fact.out
  have hN0 : ℓ ^ n ≠ 0 := (pow_pos hp.pos n).ne'
  have hNk : IsUnit (((ℓ ^ n : ℕ)) : k) := by rw [Nat.cast_pow]; exact hℓ.pow n
  have : NeZero (((ℓ ^ n : ℕ)) : k) := ⟨hNk.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k (ℓ ^ n)
  exact ⟨(Stacks.Kummer.smoothProperCurveTrace f hNk).toAddMonoidHom.comp
      (Stacks.Picard.extRootsOfUnityAddEquiv f hζ hN0 2).toAddMonoidHom,
    (Stacks.Kummer.smoothProperCurveTrace f hNk).injective.comp
      (Stacks.Picard.extRootsOfUnityAddEquiv f hζ hN0 2).injective⟩

end Trace

section Main

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- The morphisms inverted by sheafification form a monoidal class for étale sheaves of
`Λ`-modules on `S` (`Stacks.EtaleCohomology.isMonoidal_W_etaleModules`). -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The base change to `k̄` of an open immersion over `k` is an open immersion. -/
private theorem isOpenImmersion_fieldBaseChangeMap_of_isOpenImmersion {k : Type u} [Field k]
    {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsOpenImmersion i.left] : IsOpenImmersion (fieldBaseChangeMap i kbar) :=
  have : MorphismProperty.IsStableUnderComposition @IsOpenImmersion.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs (IsOpenImmersion i.left))
    (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w i).symm (Category.id_comp _).symm

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The level-`n` cup product pairing on a curve is nondegenerate up to bounded torsion.**
In the situation of `Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing_of_curve`, at a fixed
level `n`, with `M = pr^{-1} j_! Fₙ`, `G = pr^{-1} j_! F'ₙ` on `Y = X̄_k̄` and an injective trace
`t` on `H²(Y, ℤ/ℓⁿ⁺¹)`: if `t(a ∪ b) = 0` for all `b ∈ H¹(Y, G)` then `ℓ^K a = 0`, and if
`t(a ∪ b) = 0` for all `a ∈ H¹(Y, M)` then `ℓ^K ℓ^K b = 0`. -/
theorem LAdicSheaf.levelCup_bounds_of_curve [IsAlgClosed kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [IsProper (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Nonempty (fieldBaseChange (Over.mk f) kbar)] (hℓ : IsUnit (ℓ : kbar))
    (F F' : LAdicSheaf B X ℓ) {K : ℕ} (hF : LAdicSheaf.LocalTermsKilledBy B X ℓ f j kbar F K)
    (n : ℕ)
    (μ : (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        j.space.smallEtaleTopology)
    (hlisse : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n)))
    (hflat : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (hμ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n)))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeMap j.obj.hom kbar) (ℓ ^ (n + 1))
            (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar)
              (ℓ ^ (n + 1)) μ))).hom))
    [HasExt.{u + 1}
      (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk j.toBase) kbar))]
    (t : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk j.toBase) kbar)))
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 →+ ZMod (ℓ ^ (n + 1)))
    (ht : Function.Injective t)
    [(MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ F' n)))).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
      (ZMod (ℓ ^ (n + 1))) (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ F' n))))]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
      (ZMod (ℓ ^ (n + 1))) (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ F' n))))] :
    (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ F n))) 1,
      (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n))) 1,
          t (Stacks.ExtCup.cup.{u + 1, _, _} (inverseImageConstantPairing
            (fieldBaseChangeProj (Over.mk j.toBase) kbar) (ℓ ^ (n + 1)) μ) a b
              (show 1 + 1 = 2 from rfl)) = 0) → (ℓ ^ K) • a = 0) ∧
    (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ F' n))) 1,
      (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n))) 1,
          t (Stacks.ExtCup.cup.{u + 1, _, _} (inverseImageConstantPairing
            (fieldBaseChangeProj (Over.mk j.toBase) kbar) (ℓ ^ (n + 1)) μ) a b
              (show 1 + 1 = 2 from rfl)) = 0) → (ℓ ^ K * ℓ ^ K) • b = 0) := by
  have : IsOpenImmersion j.obj.hom.left := j.property.1
  have : IsOpenImmersion (fieldBaseChangeMap j.obj.hom kbar) :=
    isOpenImmersion_fieldBaseChangeMap_of_isOpenImmersion j.obj.hom kbar
  have : HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChange (Over.mk f) kbar)) := etaleModules_hasExt _ (ZMod (ℓ ^ (n + 1)))
  let μY := inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar)
    (ℓ ^ (n + 1)) μ
  let M := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F n))
  let G := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n))
  obtain ⟨_, _, _⟩ := tensorRight_exact_of_flat G hflat
  let j' := fieldBaseChangeMap j.obj.hom kbar
  let Φ := etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) j'
  let R := etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (n + 1))) j'
  let ι := etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod (ℓ ^ (n + 1))) j'
  have sq := (isPullback_fieldBaseChangeMap j.obj.hom kbar).flip
  let A := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk f) kbar)).obj (LAdicSheaf.etaleLevel B X ℓ F n)
  let A' := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk f) kbar)).obj (LAdicSheaf.etaleLevel B X ℓ F' n)
  let e : M ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j').obj A :=
    ((etaleModuleInverseImageExtensionByZeroIso.{u, 0} (ZMod (ℓ ^ (n + 1))) sq).app
      (LAdicSheaf.etaleLevel B X ℓ F n)).symm
  let e' : G ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j').obj A' :=
    ((etaleModuleInverseImageExtensionByZeroIso.{u, 0} (ZMod (ℓ ^ (n + 1))) sq).app
      (LAdicSheaf.etaleLevel B X ℓ F' n)).symm
  let T := Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
  -- duality at `G`
  have hPD : Ext.IsDualityPerfect (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk j.toBase) kbar))) T 2 t G :=
    Ext.isDualityPerfect_of_iso e'.symm
      (isDualityPerfect_extensionByZero_lisse_zmodPow_of_isOpenImmersion
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) hℓ t ht j' A'
        hlisse).1
  -- forgetting supports
  obtain ⟨hb₁, hb₂⟩ := mapUnit_bounds_of_forgetSupports (ℓ ^ (n + 1)) j' A M e (ℓ ^ K)
    (ℓ ^ K * ℓ ^ K) 1
    (LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy B X ℓ f j kbar F hF n).1
    (LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy B X ℓ f j kbar F hF n).2
  -- coefficient duality on `U_k̄`
  let cU := inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) j'
  let μU := inverseImageConstantPairing j' (ℓ ^ (n + 1)) μY
  have hflatU := flat_sheafFiber_inverseImage j' G hflat
  let eG : Φ.obj G ≅ A' := Φ.mapIso e' ≪≫ ι.app _ ≪≫
    (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod (ℓ ^ (n + 1))) j').unit.app A')).symm
  have hlisseU : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology (Φ.obj G) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ (ZMod (ℓ ^ (n + 1))) eG.symm
      hlisse
  obtain ⟨_, _, _⟩ := tensorRight_exact_of_flat (Φ.obj G) hflatU
  have hΘU := bijective_tensorPairingExt (Φ.obj M) (Φ.obj G) hlisseU hflatU μU hμ 1
  have hΦinj :=
    injective_mapExactFunctor_inverseImage_of_iso (ZMod (ℓ ^ (n + 1))) j' (T := T) A' e' 1
  obtain ⟨hker, hrange⟩ := Stacks.ExtCup.bounds_tensorDual_of_mapUnit
    (C := EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk j.toBase) kbar))
    (D := EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar))
    (F := M) (G := G) Φ μY cU (ℓ ^ K)
    (ℓ ^ K * ℓ ^ K) hb₁ hb₂ hΘU hΦinj
  exact Stacks.ExtCup.cup_nondegenerate_of_bounds μY (p := ℓ) (m := n + 1) t
    (show 1 + 1 = 2 from rfl) (ℓ ^ K) (ℓ ^ K * ℓ ^ K) hker hrange hPD

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Finite-level Poincaré duality on a curve over a finite field, with bounded defect.** Let
`X` be a `k`-scheme, `k` finite with `p ^ q` elements, `j : X ⟶ X̄` a compactification over `k`,
`k̄` algebraically closed with `Y = X̄_k̄` a smooth proper curve over `k̄`, `X` nonempty, `ℓ` a
prime invertible in `k̄`, and `F`, `F'` ℓ-adic sheaves on `X` with pairings
`μₙ : j_! Fₙ ⊗ j_! F'ₙ ⟶ ℤ/ℓⁿ⁺¹` on `X̄`. Suppose that `F'ₙ|_{X_k̄}` is lisse, that
`(j_! F'ₙ)|_Y` has flat geometric fibres, that the pullback of `μₙ` to `X_k̄` is perfect on
geometric fibres, and that the local terms of `F` at the boundary are killed by `ℓ^K`. Then the
cup product pairings `εₙ : H¹_c(X_k̄, Fₙ) × H¹_c(X_k̄, F'ₙ) → ℤ/ℓⁿ⁺¹` have left kernels killed by
`ℓ^K` and right kernels killed by `ℓ^K · ℓ^K`, and are scaled by `p ^ q` under the canonical
geometric Frobenius. -/
theorem LAdicSheaf.exists_levelPairing_of_curve [IsAlgClosed kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Nonempty X.1] (hℓ : IsUnit (ℓ : kbar))
    (F F' : LAdicSheaf B X ℓ) {K : ℕ} (hF : LAdicSheaf.LocalTermsKilledBy B X ℓ f j kbar F K)
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        j.space.smallEtaleTopology)
    (hlisse : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n)))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (hμ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F n))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ F' n)))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeMap j.obj.hom kbar) (ℓ ^ (n + 1))
            (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar)
              (ℓ ^ (n + 1)) (μ n)))).hom)) :
    ∃ ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
          (LAdicSheaf.padicLevel B X ℓ F n) →+
        (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
          (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)),
      (∀ n x, (∀ y, ε n x y = 0) → (ℓ ^ K) • x = 0) ∧
      (∀ n y, (∀ x, ε n x y = 0) → (ℓ ^ K * ℓ ^ K) • y = 0) ∧
      ∀ n x y, ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) 1).hom x)
        ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n)) 1).hom y) =
        ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) * ε n x y := by
  have hp : ℓ.Prime := Fact.out
  have : IsProper (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (inferInstanceAs (IsProper j.toBase))
  have : IsOpenImmersion j.obj.hom.left := j.property.1
  have : IsOpenImmersion (fieldBaseChangeMap j.obj.hom kbar) :=
    isOpenImmersion_fieldBaseChangeMap_of_isOpenImmersion j.obj.hom kbar
  have : Nonempty (fieldBaseChange (Over.mk f) kbar) := by
    obtain ⟨x⟩ := ‹Nonempty X.1›
    obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x (default : Spec (.of kbar))
      (f := f) (g := specAlgebraMap k kbar) (Subsingleton.elim _ _)
    exact ⟨y⟩
  have hExt : ∀ n : ℕ, HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk j.toBase) kbar)) := fun n =>
    etaleModules_hasExt _ (ZMod (ℓ ^ (n + 1)))
  have hji : 1 + 1 = 2 := rfl
  choose Φl hΦl using fun n => LAdicSheaf.exists_addEquiv_level_frobenius B X ℓ f j kbar p q
    hcard F 1 n
  choose Φl' hΦl' using fun n => LAdicSheaf.exists_addEquiv_level_frobenius B X ℓ f j kbar p q
    hcard F' 1 n
  let φ : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
        (LAdicSheaf.padicLevel B X ℓ F n) ≃+ Ext.{u + 1}
      (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk j.toBase) kbar)))
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ F n))) 1 := fun n => Φl n
  let φ' : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
        (LAdicSheaf.padicLevel B X ℓ F' n) ≃+ Ext.{u + 1}
      (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk j.toBase) kbar)))
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
          (LAdicSheaf.etaleLevel B X ℓ F' n))) 1 := fun n => Φl' n
  choose t₀ ht₀ using fun n => exists_injective_trace_zmodPow_of_curve
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) hℓ (ℓ := ℓ) (n + 1)
  let t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk j.toBase) kbar)))
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 →+ ZMod (ℓ ^ (n + 1)) :=
    fun n => t₀ n
  have ht : ∀ n, Function.Injective (t n) := fun n => ht₀ n
  let μY := fun n => inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar)
    (ℓ ^ (n + 1)) (μ n)
  let M := fun n => (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F n))
  let G := fun n => (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ F' n))
  have hT₁ : ∀ n, (MonoidalCategory.tensorRight (G n)).Additive := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).1
  have hT₂ : ∀ n, PreservesFiniteLimits (MonoidalCategory.tensorRight (G n)) := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).2.1
  have hT₃ : ∀ n, PreservesFiniteColimits (MonoidalCategory.tensorRight (G n)) := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).2.2
  have hnd : ∀ n,
      (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar))) (M n) 1,
        (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar))) (G n) 1,
            t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji) = 0) → (ℓ ^ K) • a = 0) ∧
      (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar))) (G n) 1,
        (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar))) (M n) 1,
            t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji) = 0) → (ℓ ^ K * ℓ ^ K) • b = 0) :=
    fun n => LAdicSheaf.levelCup_bounds_of_curve B X ℓ f j kbar hℓ F F' hF n (μ n) (hlisse n)
      (hflat n) (hμ n) (t n) (ht n)
  let ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
        (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
        (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)) :=
    fun n => AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y =>
      t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ' n y) hji)) (fun y y' => by
        rw [map_add, Stacks.ExtCup.cup_add, map_add])) (fun x x' => by
        ext y
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          Stacks.ExtCup.add_cup])
  refine ⟨ε, fun n x hx => ?_, fun n y hy => ?_, fun n x y => ?_⟩
  · have h0 := (hnd n).1 (φ n x) fun b => by
      obtain ⟨y, rfl⟩ := (φ' n).surjective b
      exact hx y
    exact (φ n).injective (by rw [map_nsmul, h0, map_zero])
  · have h0 := (hnd n).2 (φ' n y) fun a => by
      obtain ⟨x, rfl⟩ := (φ n).surjective a
      exact hy x
    exact (φ' n).injective (by rw [map_nsmul, h0, map_zero])
  · let πb := geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard
    let G' := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) πb).obj (G n)
    obtain ⟨_, _, _⟩ := tensorRight_exact_of_flat G'
      (flat_sheafFiber_inverseImage πb (G n) (hflat n))
    have key := cup_adjunctionExtMap_frobeniusBaseChangeTwist (ℓ ^ (n + 1)) (Over.mk j.toBase) kbar
      p q hcard (μ n) hji (φ n x) (φ' n y)
    have h₁ : ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) 1).hom x)
        ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n)) 1).hom y) =
        t n (constantExtRestriction (ZMod (ℓ ^ (n + 1))) πb 2
          (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ' n y) hji)) := by
      show t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n _) (φ' n _) hji) = _
      rw [← key]
      exact congrArg₂ (fun a b => t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji))
        (hΦl n x) (hΦl' n y)
    refine h₁.trans ((congrArg (t n)
      (constantExtRestriction_geometricFrobeniusBaseChange_two_of_curve (Over.mk j.toBase) kbar p q
        hcard hℓ (n + 1) _)).trans ?_)
    exact (map_nsmul (t n) _ _).trans (nsmul_eq_mul _ _)

end Main

end Stacks.EtaleCohomology

end
