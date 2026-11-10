module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelPoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupPairingNondegenerate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TensorPairingExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FrobeniusExtRestriction

/-!
# The finite-level Poincaré pairing, with its Frobenius factor `q^d`

Let `X` be proper over a finite field `k` with `q` elements, `k̄` an algebraic closure,
`Y = X_k̄` connected, smooth of relative dimension `d` over `k̄`, `ℓ` a prime invertible in `k̄`
and `N = ℓⁿ⁺¹`. Let `F`, `F'` be ℓ-adic sheaves on `X` with a pairing `μₙ : Fₙ ⊗ F'ₙ → ℤ/N` at
every level. When the pullback of `μₙ` to `Y` is perfect on the geometric fibres and `F'ₙ|_Y` is
lisse with flat fibres, the pairing

`εₙ(x, y) = t(x ∪_{μₙ} y) : Hⁱ(X_k̄, Fₙ) × H^{2d-i}(X_k̄, F'ₙ) → H^{2d}(Y, ℤ/N) ≅ ℤ/N`

is nondegenerate on both sides and the canonical geometric Frobenius scales it by `q^d`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing`). This is exactly the input of
`Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_of_levelPairing`, the deduction of the
last assertion of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) from Poincaré duality.

The ingredients:

* the levels of `Hⁱ(X_k̄, F)` are `Ext^i(ℤ/N_Y, Fₙ|_Y)`, the Frobenius being the twisted action
  of `π̄` (`Stacks.EtaleCohomology.LAdicSheaf.exists_addEquiv_level_frobenius`,
  `Stacks.ExtCup.twistAction_homEquiv_symm`);
* nondegeneracy: Poincaré duality with `ℤ/N` coefficients at `F'ₙ|_Y`
  (`Stacks.EtaleCohomology.isDualityPerfect_levelPow_of_isFiniteTypeLocallyConstant`) and the
  duality of `Ext` along the fibrewise perfect pairing
  (`Stacks.EtaleCohomology.bijective_tensorPairingExt`), combined by
  `Stacks.ExtCup.cup_nondegenerate`;
* the Frobenius: the twisted action commutes with cup products of pulled back coefficients
  (`Stacks.ExtCup.twistAction_cup`,
  `Stacks.EtaleCohomology.frobeniusBaseChangeTwist_twistAction_hσ`),
  on `H^{2d}(Y, ℤ/N)` it is restriction along `π̄`
  (`Stacks.EtaleCohomology.adjunctionExtMap_frobeniusBaseChangeTwist_constant`), which is
  multiplication by `q^d` (the input `hC`).

## Main results

* `Stacks.EtaleCohomology.inverseImageConstantPairing`: the pulled back pairing of coefficients.
* `Stacks.EtaleCohomology.cup_adjunctionExtMap_frobeniusBaseChangeTwist`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_levelPairing`.

The named inputs are those of finite-level Poincaré duality (`hcore`, `hD1`, `hA1`) and the
Frobenius on the top cohomology (`hC`). The statements consume objects defined in the standard
model `HasDerivedCategory.standard` of the derived category, which is therefore a local instance
here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

/-- The morphisms of presheaves of `Λ`-modules on the small étale site of `S` inverted by
sheafification form a monoidal class (`Stacks.EtaleCohomology.isMonoidal_W_etaleModules`). -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

section Pairing

variable {S T : Scheme.{u}} (g : T ⟶ S) (N : ℕ)

/-- **A pairing of coefficients pulled back along `g`**: `g^{-1} K ⊗ g^{-1} K' ⟶ g^{-1}(K ⊗ K')
⟶ g^{-1} ℤ/N_S ≅ ℤ/N_T` for `μ : K ⊗ K' ⟶ ℤ/N_S`. -/
def inverseImageConstantPairing {K K' : EtaleModules.{u, 0} (ZMod N) S}
    (μ : K ⊗ K' ⟶ Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      S.smallEtaleTopology) :
    (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj K ⊗
        (etaleModuleInverseImage.{u, 0} (ZMod N) g).obj K' ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) T.smallEtaleTopology :=
  Functor.LaxMonoidal.μ (etaleModuleInverseImage.{u, 0} (ZMod N) g) K K' ≫
    (etaleModuleInverseImage.{u, 0} (ZMod N) g).map μ ≫
    (inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod N)
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) g).hom

end Pairing

section Frobenius

variable (N : ℕ) {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The canonical Frobenius commutes with cup products of pulled back coefficients, and is
restriction along `π̄` on the target.** For `μ₀ : L₁ ⊗ L₂ ⟶ ℤ/N` on `Y` and classes
`a ∈ Ext^i(ℤ/N, L₁|_{Y_k̄})`, `b ∈ Ext^j(ℤ/N, L₂|_{Y_k̄})`, the cup product of the Frobenius
images `θ(a ∘ τ)`, `θ(b ∘ τ)` is the restriction along `π̄` of `a ∪ b`. -/
theorem cup_adjunctionExtMap_frobeniusBaseChangeTwist
    {L₁ L₂ : EtaleModules.{u, 0} (ZMod N) Y.left}
    (μ₀ : L₁ ⊗ L₂ ⟶ Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N)
      Y.left.smallEtaleTopology)
    [(MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} (ZMod N)
      (fieldBaseChangeProj Y kbar)).obj L₂)).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
      (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₂))]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
      (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₂))]
    [(MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} (ZMod N)
      (geometricFrobeniusBaseChange Y kbar p q hcard)).obj ((etaleModuleInverseImage.{u, 0}
        (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₂))).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
      (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₂)))]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0}
      (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₂)))]
    {i j n : ℕ} (h : j + i = n)
    (a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) (fieldBaseChange Y kbar)))
      ((etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₁) i)
    (b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) (fieldBaseChange Y kbar)))
      ((etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₂) j) :
    Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj Y kbar) N μ₀)
        (Stacks.ExtCup.adjunctionExtMap
          (etaleModuleInverseImage.{u, 0} (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard))
          (etaleModuleDirectImage.{u, 0} (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard))
          (etaleModuleInverseImageAdj.{u, 0} (ZMod N)
            (geometricFrobeniusBaseChange Y kbar p q hcard))
          ((etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₁)
          (a.comp (Ext.mk₀ ((frobeniusBaseChangeTwist.{u, 0} (ZMod N) Y kbar p q hcard).app L₁))
            (add_zero i)))
        (Stacks.ExtCup.adjunctionExtMap
          (etaleModuleInverseImage.{u, 0} (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard))
          (etaleModuleDirectImage.{u, 0} (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard))
          (etaleModuleInverseImageAdj.{u, 0} (ZMod N)
            (geometricFrobeniusBaseChange Y kbar p q hcard))
          ((etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj Y kbar)).obj L₂)
          (b.comp (Ext.mk₀ ((frobeniusBaseChangeTwist.{u, 0} (ZMod N) Y kbar p q hcard).app L₂))
            (add_zero j))) h =
      constantExtRestriction (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard) n
        (Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj Y kbar) N μ₀)
          a b h) := by
  let P := etaleModuleInverseImage.{u, 0} (ZMod N) (fieldBaseChangeProj Y kbar)
  let Φ := etaleModuleInverseImage.{u, 0} (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard)
  let Ψ := etaleModuleDirectImage.{u, 0} (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard)
  let adj :=
    etaleModuleInverseImageAdj.{u, 0} (ZMod N) (geometricFrobeniusBaseChange Y kbar p q hcard)
  let τ := frobeniusBaseChangeTwist.{u, 0} (ZMod N) Y kbar p q hcard
  let c := inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod N)
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) (fieldBaseChangeProj Y kbar)
  have e1 : ∀ {i' j' n' : ℕ} (h' : j' + i' = n') (x : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N)
      (fieldBaseChange Y kbar))) (P.obj L₁) i') (y : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N)
      (fieldBaseChange Y kbar))) (P.obj L₂) j'),
      Stacks.ExtCup.cup (inverseImageConstantPairing (fieldBaseChangeProj Y kbar) N μ₀) x y h' =
        (Stacks.ExtCup.cup (Functor.LaxMonoidal.μ P L₁ L₂ ≫ P.map μ₀) x y h').comp
          (Ext.mk₀ c.hom) (add_zero n') := by
    intro i' j' n' h' x y
    rw [Stacks.ExtCup.cup_comp_mk₀]
    simp only [inverseImageConstantPairing, Category.assoc]
    rfl
  rw [e1, e1, ← Stacks.ExtCup.twistAction_homEquiv_symm Φ Ψ adj (τ.app L₁),
    ← Stacks.ExtCup.twistAction_homEquiv_symm Φ Ψ adj (τ.app L₂),
    ← Stacks.ExtCup.twistAction_cup Φ (Functor.LaxMonoidal.μ P L₁ L₂ ≫ P.map μ₀) _ _
      ((adj.homEquiv _ _).symm (τ.app (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod N) Y.left.smallEtaleTopology)))
      (frobeniusBaseChangeTwist_twistAction_hσ (ZMod N) Y kbar p q hcard μ₀),
    Stacks.ExtCup.twistAction_homEquiv_symm Φ Ψ adj]
  have key := adjunctionExtMap_frobeniusBaseChangeTwist_constant (ZMod N) Y kbar p q hcard
    ((Stacks.ExtCup.cup (Functor.LaxMonoidal.μ P L₁ L₂ ≫ P.map μ₀) a b h).comp
      (Ext.mk₀ c.hom) (add_zero n))
  have hz : ((Stacks.ExtCup.cup (Functor.LaxMonoidal.μ P L₁ L₂ ≫ P.map μ₀) a b h).comp
      (Ext.mk₀ c.hom) (add_zero n)).comp (Ext.mk₀ c.inv) (add_zero n) =
      Stacks.ExtCup.cup (Functor.LaxMonoidal.μ P L₁ L₂ ≫ P.map μ₀) a b h := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.comp_mk₀_id]
  conv_lhs => rw [← hz]
  exact key

end Frobenius

section Flat

variable {S : Scheme.{u}} {N : ℕ}

/-- `- ⊗ G` is exact for `G` with flat fibres at all geometric points. -/
theorem tensorRight_exact_of_flat (G : EtaleModules.{u, 0} (ZMod N) S)
    (hG : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Module.Flat (ZMod N)
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).obj G)) :
    (MonoidalCategory.tensorRight G).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight G) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight G) :=
  preservesFiniteLimits_tensorRight_etaleModules_of_flat (ZMod N) S
    (fun x : S => residueGeometricPoint S x)
    (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2
      ⟨x, default, residueGeometricPoint_apply S x default⟩) G
    (fun x => hG _ (residueGeometricPoint S x))

/-- Flat fibres pass to inverse images. -/
theorem flat_sheafFiber_inverseImage {T : Scheme.{u}} (g : T ⟶ S)
    (G : EtaleModules.{u, 0} (ZMod N) S)
    (hG : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Module.Flat (ZMod N)
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).obj G))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T) :
    Module.Flat (ZMod N)
      ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod N))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj G)) :=
  have := hG Ω (s ≫ g)
  Module.Flat.of_linearEquiv
    ((etaleModuleInverseImageSheafFiberIso (ZMod N) g s).app G).toLinearEquiv

end Flat

section Main

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
  [QuasiCompact f] [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

omit [QuasiCompact f] in
/-- **Finite-level Poincaré duality with its Frobenius factor `q^d`**, in the shape consumed by
`Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_of_levelPairing`. Let `X` be proper
over the finite field `k` with `p^q` elements, compactified by itself, `k̄` algebraically closed,
`Y = X_k̄` connected and smooth of relative dimension `d` over `k̄`, `ℓ` a prime invertible in
`k̄`, and `F`, `F'` ℓ-adic sheaves on `X` with pairings `μₙ : Fₙ ⊗ F'ₙ ⟶ ℤ/ℓⁿ⁺¹` (read on
`j_! = id`). Suppose that on `Y` the sheaves `F'ₙ|_Y` are lisse with flat fibres and the pulled
back pairings are perfect on the geometric fibres. Given finite-level Poincaré duality on `Y` (the
inputs `hcore`, `hD1`, `hA1`) and the Frobenius on `H^{2d}(Y, ℤ/ℓⁿ⁺¹)` being multiplication by
`q^d` (`hC`), for `0 ≤ i ≤ 2d` the cup product pairings
`εₙ : Hⁱ(X_k̄, Fₙ) × H^{2d-i}(X_k̄, F'ₙ) → ℤ/ℓⁿ⁺¹` are nondegenerate on both sides and scaled by
`q^d` under the canonical geometric Frobenius. -/
theorem LAdicSheaf.exists_levelPairing [IsAlgClosed kbar] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
    (hℓ : IsUnit (ℓ : kbar))
    (hcore : IsUnit (ℓ : kbar) → LocalPurity ℓ kbar → PoincareDualityCore ℓ kbar)
    (hD1 : TopCohomologyPointClass ℓ kbar)
    (hA1 : ∀ m : ℕ, Nonempty (Ext (unitSheaf (X := fieldBaseChange (Over.mk f) kbar) (ℓ ^ (m + 1)))
      (unitSheaf (ℓ ^ (m + 1))) (2 * d) ≃+ ZMod (ℓ ^ (m + 1))))
    (hC : ∀ (n : ℕ) (z : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf
        (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d)),
      constantExtRestriction (ZMod (ℓ ^ (n + 1)))
        (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard) (2 * d) z =
          ((p ^ q) ^ d : ℕ) • z)
    (F F' : LAdicSheaf B X ℓ)
    (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology)
    (hlisse : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n)))))
    (hμ : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n)))
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk f) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))) ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
          (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar) (ℓ ^ (n + 1))
            (μ n))).hom))
    (i : ℕ) (hi : i ≤ 2 * d) :
    ∃ ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f)
          kbar i).obj (LAdicSheaf.padicLevel B X ℓ F n) →+
        (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
          (2 * d - i)).obj (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)),
      (∀ n x, (∀ y, ε n x y = 0) → x = 0) ∧ (∀ n y, (∀ x, ε n x y = 0) → y = 0) ∧
      ∀ n x y, ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f
          (CompactificationOf.ofProper f) kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x)
        ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n))
            (2 * d - i)).hom y) = (((p ^ q) ^ d : ℕ) : ZMod (ℓ ^ (n + 1))) * ε n x y := by
  have hidx : (2 * (d : ℤ) - (i : ℤ)) = ((2 * d - i : ℕ) : ℤ) := by omega
  rw [hidx]
  have hji : (2 * d - i) + i = 2 * d := Nat.sub_add_cancel hi
  choose Φ hΦ using fun n => LAdicSheaf.exists_addEquiv_level_frobenius B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard F i n
  choose Φ' hΦ' using fun n => LAdicSheaf.exists_addEquiv_level_frobenius B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard F' (2 * d - i) n
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  have : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) inferInstance
  have hExt : ∀ n : ℕ, HasExt.{u + 1} (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar)) := fun n => etaleModules_hasExt _ (ZMod (ℓ ^ (n + 1)))
  let t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar)))
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) (2 * d) →+ ZMod (ℓ ^ (n + 1)) :=
    fun n => (hA1 n).some.toAddMonoidHom
  let μY := fun n => inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar)
    (ℓ ^ (n + 1)) (μ n)
  let M := fun n => (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk f) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F n))
  let G := fun n => (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
    (fieldBaseChangeProj (Over.mk f) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n))
  have hT₁ : ∀ n, (MonoidalCategory.tensorRight (G n)).Additive := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).1
  have hT₂ : ∀ n, PreservesFiniteLimits (MonoidalCategory.tensorRight (G n)) := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).2.1
  have hT₃ : ∀ n, PreservesFiniteColimits (MonoidalCategory.tensorRight (G n)) := fun n =>
    (tensorRight_exact_of_flat (G n) (hflat n)).2.2
  let φ : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f)
        kbar i).obj (LAdicSheaf.padicLevel B X ℓ F n) ≃+ Ext.{u + 1}
      (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar))) (M n) i :=
    fun n => Φ n
  let φ' : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f)
        kbar ((2 * d - i : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ F' n) ≃+ Ext.{u + 1}
      (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) (fieldBaseChange (Over.mk f) kbar))) (G n)
        (2 * d - i) :=
    fun n => Φ' n
  let ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f)
        kbar i).obj (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
        ((2 * d - i : ℕ) : ℤ)).obj (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)) :=
    fun n => AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y =>
      t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ' n y) hji)) (fun y y' => by
        rw [map_add, Stacks.ExtCup.cup_add, map_add])) (fun x x' => by
        ext y
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          Stacks.ExtCup.add_cup])
  have hε : ∀ n x y, ε n x y = t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ' n y) hji) :=
    fun _ _ _ => rfl
  have hnd : ∀ n,
      (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (M n) i,
        (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (G n) (2 * d - i),
            t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji) = 0) → a = 0) ∧
      (∀ b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (G n) (2 * d - i),
        (∀ a : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar))) (M n) i,
            t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji) = 0) → b = 0) := fun n => by
    exact Stacks.ExtCup.cup_nondegenerate.{u + 1, _, _} (μY n) (p := ℓ) (m := n + 1) (t n) hji
      (bijective_tensorPairingExt (M n) (G n) (hlisse n) (hflat n) (μY n) (hμ n) i)
      (isDualityPerfect_levelPow_of_isFiniteTypeLocallyConstant ℓ hℓ hcore hD1
        (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) d hA1 n (t n)
        (hA1 n).some.injective (G n) (hlisse n))
  refine ⟨ε, fun n x hx => ?_, fun n y hy => ?_, fun n x y => ?_⟩
  · refine (φ n).injective ((((hnd n).1 (φ n x) fun b => ?_)).trans (map_zero _).symm)
    obtain ⟨y, rfl⟩ := (φ' n).surjective b
    exact hx y
  · refine (φ' n).injective ((((hnd n).2 (φ' n y) fun a => ?_)).trans (map_zero _).symm)
    obtain ⟨x, rfl⟩ := (φ n).surjective a
    exact hy x
  · let πb := geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard
    let G' := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) πb).obj (G n)
    have hG' := tensorRight_exact_of_flat G'
      (flat_sheafFiber_inverseImage πb (G n) (hflat n))
    have := hG'.1
    have := hG'.2.1
    have := hG'.2.2
    have key := cup_adjunctionExtMap_frobeniusBaseChangeTwist (ℓ ^ (n + 1)) (Over.mk f) kbar p q
      hcard (μ n) hji (φ n x) (φ' n y)
    have h₁ : ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f
          (CompactificationOf.ofProper f) kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x)
        ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f (CompactificationOf.ofProper f)
          kbar p q hcard ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n))
            ((2 * d - i : ℕ) : ℤ)).hom y) =
        t n (constantExtRestriction (ZMod (ℓ ^ (n + 1))) πb (2 * d)
          (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n x) (φ' n y) hji)) := by
      change t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) (φ n _) (φ' n _) hji) = _
      rw [← key]
      exact congrArg₂ (fun a b => t n (Stacks.ExtCup.cup.{u + 1, _, _} (μY n) a b hji))
        (hΦ n x) (hΦ' n y)
    refine h₁.trans ((congrArg (t n) (hC n _)).trans ?_)
    exact (map_nsmul (t n) _ _).trans (nsmul_eq_mul _ _)

end Main

end Stacks.EtaleCohomology

end
