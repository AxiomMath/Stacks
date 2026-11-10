module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportGeometricVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineFourierKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseEtaleSheafTensorStalk
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactHomology

/-!
# `Rf_!(M ⊗ L_ψ) = 0` on the affine line, with coefficients in a finite ring

Let `k` be a finite field with `q` elements, `Λ` a finite commutative ring in which `q` is
invertible, `ψ : k → Λ` an additive character with `∑_{a ∈ k} ψ(a) = 0`, and `L = L_ψ(x)` the
Artin–Schreier sheaf of `Λ`-modules on `𝔸¹_k`. For every finite `Λ`-module `M`,

`Rf_!(M ⊗_Λ L) = 0` in `D⁺(Spec k, Λ)`, `f : 𝔸¹_k ⟶ Spec k`,

the vanishing of the kernel of the Fourier transform at a finite level, with coefficients
([Laumon, 1.2.2.1]; [SGA 4½, Sommes trig., 2.7]).

## Main results

* `subsingleton_compactSupportSheafCohomology_constantSheaf_tensor_affineLineArtinSchreierSheaf`:
  `Hⁱ_c(𝔸¹_k̄, M ⊗ L_ψ) = 0` for every `i` and every finite `Λ`-module `M`.
* `isZero_derivedLowerShriek_constantSheaf_tensor_affineLineArtinSchreierSheaf`:
  `Rf_!(M ⊗ L_ψ) = 0` for every finite `Λ`-module `M`.

## References

* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, 1.2.2]
* [P. Deligne, SGA 4½, Sommes trigonométriques, 2.7]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.GroupCohomology Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

/-- **Sheafification of étale sheaves of modules over a ring in `Type`**, at the universes of
`EtaleModules.{u, 0}`: `Stacks.EtaleCohomology.hasSheafifyEtale` with its coefficient universe
pinned to `0`. -/
instance hasSheafify_etaleModules_universeZero (Λ : Type) [Ring Λ] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasSheafifyEtale.{u, 0} X Λ

/-! ### Twists by a character and restriction of scalars of finite continuous modules -/

section Modules

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The stabilizer of a vector under an action through a character with open kernel is open. -/
theorem isOpen_setOf_character_smul_eq (Λ : Type) [CommRing Λ] (χ : G →* Λˣ)
    (hχ : IsOpen (χ.ker : Set G)) {M : Type*} [AddCommGroup M] [Module Λ M] (v : M) :
    IsOpen {g : G | (χ g : Λ) • v = v} := by
  refine isOpen_iff_forall_mem_open.2 fun g hg =>
    ⟨(fun h => g⁻¹ * h) ⁻¹' (χ.ker : Set G), ?_, ?_, ?_⟩
  · intro h hh
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker] at hh
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have : χ h = χ g := by
      rw [show h = g * (g⁻¹ * h) by group, map_mul, hh, mul_one]
    rw [this]
    exact hg
  · exact hχ.preimage (continuous_const.mul continuous_id)
  · simp

variable (Λ : Type) [CommRing Λ] [Finite Λ] (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G))

/-- `G` acting on a `Λ`-module through a character `χ : G →* Λˣ`. -/
def characterTwistRepresentation (M : ModuleCat.{u + 1} Λ) : Representation Λ G M where
  toFun g := (χ g : Λ) • LinearMap.id
  map_one' := by
    ext v
    simp
  map_mul' g g' := by
    ext v
    change (χ (g * g') : Λ) • v = (χ g : Λ) • ((χ g' : Λ) • v)
    rw [map_mul, Units.val_mul, mul_smul]

/-- **A finite `Λ`-module twisted by a character `χ` with open kernel**, as a finite `Λ`-module
with continuous `G`-action: `g` acts as multiplication by `χ g`. -/
def characterTwistContinuousModule (M : ModuleCat.{u + 1} Λ) [Finite M] :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G :=
  ⟨ofRepresentation (characterTwistRepresentation Λ χ M)
      ((isContinuous_actionOfRepresentation_iff _).2 fun v =>
        isOpen_setOf_character_smul_eq Λ χ hχ v),
    (ModuleCat.isFG_iff _).2 (show Module.Finite Λ M from Module.Finite.of_finite)⟩

omit [Finite Λ] in
/-- In the twist of `M` by `χ`, an element `g` acts on `v` as `χ g • v`. -/
theorem characterTwistContinuousModule_ρ_hom (M : ModuleCat.{u + 1} Λ) [Finite M] (g : G)
    (v : M) :
    (((characterTwistContinuousModule Λ χ hχ M).obj.obj.obj.ρ g).asHom.hom v : M) = (χ g : Λ) • v :=
  rfl

variable {Λ} in
/-- **Restriction of scalars of a finite continuous module** along `ρ : R →+* S`. -/
def finiteTypeContinuousModuleRestrictScalars {R : Type} [CommRing R] [Finite R] (ρ : R →+* Λ)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G) :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} R G :=
  haveI : Finite (ToType P.obj.obj.obj.V) := (moduleCat_isFG_iff_finite Λ _).mp P.property
  haveI : Finite (ToType ((ModuleCat.restrictScalars.{u + 1} ρ).obj P.obj.obj.obj.V)) :=
    inferInstanceAs (Finite (ToType P.obj.obj.obj.V))
  ⟨ofRepresentation (R := R) (M := (ModuleCat.restrictScalars.{u + 1} ρ).obj P.obj.obj.obj.V)
      { toFun := fun g => ((ModuleCat.restrictScalars.{u + 1} ρ).map (P.obj.obj.obj.ρ g).asHom).hom
        map_one' := by
          ext v
          change (P.obj.obj.obj.ρ 1).asHom.hom v = v
          rw [map_one]
          rfl
        map_mul' := fun g g' => by
          ext v
          change (P.obj.obj.obj.ρ (g * g')).asHom.hom v =
            (P.obj.obj.obj.ρ g).asHom.hom ((P.obj.obj.obj.ρ g').asHom.hom v)
          rw [map_mul]
          rfl }
      ((isContinuous_actionOfRepresentation_iff _).2 fun v => isOpen_stabilizer Λ G P.obj v),
    (ModuleCat.isFG_iff _).2 (show Module.Finite R ((ModuleCat.restrictScalars.{u + 1} ρ).obj
      P.obj.obj.obj.V) from Module.Finite.of_finite)⟩

end Modules

/-! ### Lisse sheaves and restriction of scalars of their modules -/

section Lisse

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {R S : Type} [CommRing R] [CommRing S] [Finite R] [Finite S] (ρ : R →+* S)

/-- **`res_ρ ℱ_P ≅ ℱ_{res_ρ P}`** on Mathlib's small étale site. -/
def lisseEtaleSheafRestrictScalarsModuleIso
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} S (EtaleFundamentalGroup X.1 x)) :
    (etaleModuleRestrictScalars ρ X.1).obj ((lisseEtaleSheaf B X x S).obj P) ≅
      (lisseEtaleSheaf B X x R).obj (finiteTypeContinuousModuleRestrictScalars ρ P) :=
  lisseEtaleSheafRestrictScalarsIso B X x ρ (Iso.refl _) fun _ => rfl

end Lisse

/-! ### `Hⁱ_c(X_k̄, -)` and restriction of scalars, for sheaves -/

section RestrictScalars

attribute [local instance] HasDerivedCategory.standard

variable {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) {k : Type u} [Field k] [Fintype k]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [Algebra k kbar]

/-- **`Hⁱ_c(X_k̄, G)|_R ≅ Hⁱ_c(X_k̄, res_ρ G)`** for a sheaf `G` of `S`-modules ([Tag 03V2]'s
comparison `RΓ_c(X_k̄, K)|_R ≅ RΓ_c(X_k̄, res_ρ K)`, at `K = G[0]`). -/
def compactSupportSheafCohomologyRestrictScalarsIso (G : EtaleModules.{u, 0} S X) (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} ρ).obj ((compactSupportSheafCohomology S f j kbar i).obj G) ≅
      (compactSupportSheafCohomology R f j kbar i).obj ((etaleModuleRestrictScalars ρ X).obj G) :=
  compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar
      ((sheafSingleComplex S).obj G) i ≪≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} R) i).mapIso
      ((compactSupportFrobeniusFunctor.{u, 0} R f j kbar).mapIso
        (ObjectProperty.isoMk (P := CochainComplex.plus (EtaleModules.{u, 0} R X))
          (X := (etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj
            ((sheafSingleComplex S).obj G))
          (Y := (sheafSingleComplex R).obj ((etaleModuleRestrictScalars ρ X).obj G))
          ((HomologicalComplex.singleMapHomologicalComplex
            (etaleModuleRestrictScalars ρ X) (ComplexShape.up ℤ) 0).app G)))

omit [Fintype k] in
/-- `Hⁱ_c(X_k̄, G)` vanishes as soon as `Hⁱ_c(X_k̄, res_ρ G)` does. -/
theorem subsingleton_compactSupportSheafCohomology_of_restrictScalars (G : EtaleModules.{u, 0} S X)
    (i : ℤ) (h : Subsingleton ((compactSupportSheafCohomology R f j kbar i).obj
      ((etaleModuleRestrictScalars ρ X).obj G))) :
    Subsingleton ((compactSupportSheafCohomology S f j kbar i).obj G) :=
  Equiv.subsingleton
    (compactSupportSheafCohomologyRestrictScalarsIso ρ f j kbar G i).toLinearEquiv.toEquiv

omit [Fintype k] in
/-- `Hⁱ_c(X_k̄, res_ρ G)` vanishes as soon as `Hⁱ_c(X_k̄, G)` does. -/
theorem subsingleton_compactSupportSheafCohomology_restrictScalars (G : EtaleModules.{u, 0} S X)
    (i : ℤ) (h : Subsingleton ((compactSupportSheafCohomology S f j kbar i).obj G)) :
    Subsingleton ((compactSupportSheafCohomology R f j kbar i).obj
      ((etaleModuleRestrictScalars ρ X).obj G)) :=
  have : Subsingleton ((ModuleCat.restrictScalars.{u + 1} ρ).obj
      ((compactSupportSheafCohomology S f j kbar i).obj G)) := h
  Equiv.subsingleton
    (compactSupportSheafCohomologyRestrictScalarsIso ρ f j kbar G i).symm.toLinearEquiv.toEquiv

end RestrictScalars

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

open Polynomial Stacks.EtaleCohomology

/-! ### The counting argument over `ℤ/p` on the affine line -/

section Counting

variable (k : Type u) [Field k] [Fintype k] (B : BigEtaleSite.{u})

/-- **`Hⁱ_c(𝔸¹_k̄, ℱ_M) = 0` over the field `ℤ/p`** for a finite `ℤ/p`-module `M` on which
`π₁(𝔸¹_k)` acts through the character of the Artin–Schreier cover by an action of `k` without
invariants, `p ∤ q`. -/
theorem subsingleton_compactSupportSheafCohomology_affineLine_torsor_character (p : ℕ)
    [Fact p.Prime] (hp : IsUnit (Fintype.card k : ZMod p))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (x : GeometricPoint (Spec (.of k[X])))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k k[X] Polynomial.X))
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod p) (EtaleFundamentalGroup _ x))
    (ρK : Multiplicative k →* Module.End (ZMod p) M.obj.obj.obj.V)
    (hM : ∀ (σ : EtaleFundamentalGroup _ x) (v : M.obj.obj.obj.V),
      (M.obj.obj.obj.ρ σ).asHom.hom v = ρK ((torsorCover k k[X] Polynomial.X).character x p₀ σ) v)
    (hfix : ∀ v, ∑ a : k, ρK (Multiplicative.ofAdd a) v = 0) (i : ℤ) :
    Subsingleton ((compactSupportSheafCohomology (ZMod p) (affineLineStructureMap k) j
      (AlgebraicClosure k) i).obj
        ((lisseEtaleSheaf B (specObject k[X] B (schemeSizeBelow_spec_polynomial k B)) x
          (ZMod p)).obj M)) := by
  let pU := affineLineStructureMap k
  let U := specObject k[X] B (schemeSizeBelow_spec_polynomial k B)
  have : IsCurve k pU := isCurve_specPolynomial k
  have : LocallyOfFiniteType pU := locallyOfFiniteType_specPolynomial k
  have : Algebra.Smooth k k[X] := {}
  have : Smooth pU := smooth_Spec_map_algebraMap k k[X]
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let g : U ⟶ U := ObjectProperty.homMk (affineLineASHom k)
  have : IsFinite (B.inclusion.map g) := inferInstanceAs (IsFinite (affineLineASHom k))
  have : Etale (B.inclusion.map g) := inferInstanceAs (Etale (affineLineASHom k))
  have hgf : g.hom ≫ pU = pU := affineLineASHom_comp_structureMap k
  have : Module.Finite (ZMod p) M.obj.obj.obj.V := M.property
  classical
  exact subsingleton_compactSupportSheafCohomology_of_torsor_character B U pU j
    (AlgebraicClosure k) p g hgf (finiteEtale_affineLineASHom k) hp
    (torsorCover k k[X] Polynomial.X) (coverIsoAffineLineASHom k) x p₀ M ρK hM hfix
    (Module.Free.chooseBasis (ZMod p) M.obj.obj.obj.V) i

end Counting

end Stacks.ArtinSchreier

namespace Stacks.EtaleCohomology

open Polynomial Stacks.ArtinSchreier

/-! ### Modules killed by a prime: reduction to `ℤ/p` -/

section Prime

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- The affine line as an object of the big étale site. -/
local notation "𝕌" => specObject k[X] B (schemeSizeBelow_spec_polynomial k B)

/-- The Artin–Schreier character of `L_ψ(x)` at the origin. -/
local notation "χ" => artinSchreierCharacter k k[X] Polynomial.X ψ (affineLineOrigin k) p₀

/-- Its kernel is open. -/
local notation "hχ" =>
  isOpen_ker_artinSchreierCharacter k k[X] Polynomial.X Λ ψ (affineLineOrigin k) p₀

/-- Through any morphism `ℤ/n → R`, a scalar acts on an `R`-module as the natural number it
represents. -/
theorem zmod_smul_eq_val_nsmul_of_ringHom {n : ℕ} [NeZero n] {R : Type*} [Ring R]
    (σ : ZMod n →+* R) {M : Type*} [AddCommGroup M] [Module R M] (c : ZMod n) (v : M) :
    σ c • v = c.val • v := by
  rw [← ZMod.natCast_zmod_val c, map_natCast, Nat.cast_smul_eq_nsmul,
    ZMod.val_natCast_of_lt (ZMod.val_lt c)]

/-- Multiplication by a scalar `c` of `R` on an `R`-module carrying a `ℤ/n`-module structure, as a
`ℤ/n`-linear map. -/
def scalarZModLinearMap {n : ℕ} [NeZero n] {R : Type*} [Ring R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module (ZMod n) M] (c : R) : M →ₗ[ZMod n] M where
  toFun v := c • v
  map_add' := smul_add c
  map_smul' z v := by
    rw [RingHom.id_apply, ← ZMod.natCast_zmod_val z]
    simpa only [Nat.cast_smul_eq_nsmul] using smul_comm c z.val v

/-- `scalarZModLinearMap c` sends `v` to `c • v`. -/
theorem scalarZModLinearMap_apply {n : ℕ} [NeZero n] {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module (ZMod n) M] (c : R) (v : M) :
    scalarZModLinearMap (n := n) c v = c • v :=
  rfl

/-- **A finite `Λ`-module `W` with a compatible `ℤ/p`-module structure, twisted by the
Artin–Schreier character, as a finite continuous `ℤ/p`-module.** -/
def artinSchreierPrimeTwist (p : ℕ) [Fact p.Prime] (W : Type (u + 1)) [AddCommGroup W]
    [Module Λ W] [Module (ZMod p) W] [Finite W] :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod p)
      (EtaleFundamentalGroup (Spec (.of k[X])) (affineLineOrigin k)) :=
  ⟨ofRepresentation (R := ZMod p) (M := W)
      { toFun := fun g => scalarZModLinearMap (n := p) (χ g : Λ)
        map_one' := by
          refine LinearMap.ext fun v => ?_
          rw [scalarZModLinearMap_apply, map_one, Units.val_one, one_smul]
          rfl
        map_mul' := fun g g' => by
          refine LinearMap.ext fun v => ?_
          rw [Module.End.mul_apply, scalarZModLinearMap_apply, scalarZModLinearMap_apply,
            scalarZModLinearMap_apply, map_mul, Units.val_mul, mul_smul] }
      ((isContinuous_actionOfRepresentation_iff _).2 fun v =>
        isOpen_setOf_character_smul_eq Λ χ hχ v),
    (ModuleCat.isFG_iff _).2 (show Module.Finite (ZMod p) W from Module.Finite.of_finite)⟩

include ψ in
/-- **`Hⁱ_c(𝔸¹_k̄, ℱ_{W_χ}) = 0` for a finite `Λ`-module `W` with a `ℤ/p`-module structure, `p ∤ q`
prime**, `W_χ` the twist of `W` by the Artin–Schreier character and `∑ ψ = 0`. -/
theorem subsingleton_compactSupportSheafCohomology_lisseEtaleSheaf_characterTwist_of_zmod
    (hψ : ∑ a : k, ψ a = 0) (p : ℕ) [Fact p.Prime] (hp : IsUnit (Fintype.card k : ZMod p))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (W : Type (u + 1))
    [AddCommGroup W] [Module Λ W] [Module (ZMod p) W] [Finite W] (i : ℤ) :
    Subsingleton ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j
      (AlgebraicClosure k) i).obj ((lisseEtaleSheaf B 𝕌 (affineLineOrigin k) Λ).obj
        (characterTwistContinuousModule Λ χ hχ (ModuleCat.of Λ W)))) := by
  let : Fintype Λ := Fintype.ofFinite Λ
  let m := Fintype.card Λ * p
  have : NeZero m := ⟨Nat.mul_ne_zero Fintype.card_ne_zero (Fact.out : p.Prime).ne_zero⟩
  let ρ₁ : ZMod m →+* Λ :=
    ZMod.castHom ((ringChar.dvd (Nat.cast_card_eq_zero Λ)).trans (dvd_mul_right _ p)) Λ
  let ρ₂ : ZMod m →+* ZMod p := ZMod.castHom (dvd_mul_left p _) (ZMod p)
  let P := characterTwistContinuousModule Λ χ hχ (ModuleCat.of Λ W)
  let V := artinSchreierPrimeTwist k Λ ψ p₀ p W
  let e : finiteTypeContinuousModuleRestrictScalars ρ₂ V ≅
      finiteTypeContinuousModuleRestrictScalars ρ₁ P :=
    finiteTypeContinuousModuleIsoOfLinearEquiv (ZMod m)
      { toFun := fun v => (v : W)
        invFun := fun v => (v : W)
        map_add' := fun _ _ => rfl
        map_smul' := fun c v => by
          change ρ₂ c • (@id W v) = ρ₁ c • (@id W v)
          rw [zmod_smul_eq_val_nsmul_of_ringHom ρ₂, zmod_smul_eq_val_nsmul_of_ringHom ρ₁]
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      fun _ _ => rfl
  let H := fun (R : Type) [CommRing R] => compactSupportSheafCohomology R
    (affineLineStructureMap k) j (AlgebraicClosure k) i
  let ρK : Multiplicative k →* Module.End (ZMod p) W :=
    { toFun := fun a => scalarZModLinearMap (n := p) (ψ (Multiplicative.toAdd a⁻¹))
      map_one' := by
        refine LinearMap.ext fun v => ?_
        rw [scalarZModLinearMap_apply, inv_one, toAdd_one, AddChar.map_zero_eq_one, one_smul]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun v => ?_
        rw [Module.End.mul_apply, scalarZModLinearMap_apply, scalarZModLinearMap_apply,
          scalarZModLinearMap_apply, mul_inv, toAdd_mul, AddChar.map_add_eq_mul, mul_smul] }
  have hfix : ∀ v : W, ∑ a : k, ρK (Multiplicative.ofAdd a) v = 0 := fun v => by
    change ∑ a : k, ψ (Multiplicative.toAdd (Multiplicative.ofAdd a)⁻¹) • v = 0
    rw [← Finset.sum_smul]
    have h2 : ∑ a : k, ψ (Multiplicative.toAdd (Multiplicative.ofAdd a)⁻¹) = ∑ a : k, ψ a :=
      Fintype.sum_equiv (Equiv.neg k) _ _ fun a => by simp
    rw [h2, hψ, zero_smul]
  have h0 : Subsingleton ((H (ZMod p)).obj
      ((lisseEtaleSheaf B 𝕌 (affineLineOrigin k) (ZMod p)).obj V)) :=
    subsingleton_compactSupportSheafCohomology_affineLine_torsor_character k B p hp j
      (affineLineOrigin k) p₀ V ρK (fun _ _ => rfl) hfix i
  have h1 := subsingleton_compactSupportSheafCohomology_restrictScalars ρ₂
    (affineLineStructureMap k) j (AlgebraicClosure k) _ i h0
  have h2 : Subsingleton ((H (ZMod m)).obj ((etaleModuleRestrictScalars ρ₁ _).obj
      ((lisseEtaleSheaf B 𝕌 (affineLineOrigin k) Λ).obj P))) :=
    ((H (ZMod m)).mapIso (lisseEtaleSheafRestrictScalarsModuleIso B 𝕌 (affineLineOrigin k) ρ₂ V ≪≫
      (lisseEtaleSheaf B 𝕌 (affineLineOrigin k) (ZMod m)).mapIso e ≪≫
      (lisseEtaleSheafRestrictScalarsModuleIso B 𝕌 (affineLineOrigin k) ρ₁ P).symm)).symm
      |>.toLinearEquiv.toEquiv.subsingleton
  exact subsingleton_compactSupportSheafCohomology_of_restrictScalars ρ₁
    (affineLineStructureMap k) j (AlgebraicClosure k) _ i h2

end Prime

/-! ### `M ⊗ L_ψ` is the lisse sheaf of the twist of `M` -/

section Tensor

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- The affine line as an object of the big étale site. -/
local notation "𝕌" => specObject k[X] B (schemeSizeBelow_spec_polynomial k B)

/-- The Artin–Schreier character of `L_ψ(x)` at the origin. -/
local notation "χ" => artinSchreierCharacter k k[X] Polynomial.X ψ (affineLineOrigin k) p₀

/-- Its kernel is open. -/
local notation "hχ" =>
  isOpen_ker_artinSchreierCharacter k k[X] Polynomial.X Λ ψ (affineLineOrigin k) p₀

/-- The trivial character has open kernel. -/
theorem isOpen_ker_one {G : Type (u + 1)} [Group G] [TopologicalSpace G] (R : Type) [CommRing R] :
    IsOpen ((1 : G →* Rˣ).ker : Set G) := by
  rw [MonoidHom.ker_one]
  exact isOpen_univ

/-- **`M ⊗ L_ψ ≅ ℱ_{M_χ}`**: the constant sheaf on a finite `Λ`-module `M` tensored with the
Artin–Schreier sheaf is the lisse sheaf of `M` with `π₁` acting through the Artin–Schreier
character. -/
theorem nonempty_constantSheaf_tensor_affineLineArtinSchreierSheaf_iso (M : ModuleCat.{u + 1} Λ)
    [Finite M] :
    Nonempty (etaleModuleConstantSheaf Λ M (Spec (.of k[X])) ⊗
        affineLineArtinSchreierSheaf k Λ ψ B p₀ ≅
      (lisseEtaleSheaf B 𝕌 (affineLineOrigin k) Λ).obj
        (characterTwistContinuousModule Λ χ hχ M)) := by
  let G := EtaleFundamentalGroup (Spec (.of k[X])) (affineLineOrigin k)
  let M₁ := characterTwistContinuousModule Λ (1 : G →* Λˣ) (isOpen_ker_one Λ) M
  let Lχ := characterContinuousModule Λ χ hχ
  let Mχ := characterTwistContinuousModule Λ χ hχ M
  obtain ⟨e₁⟩ := nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial B 𝕌 (affineLineOrigin k) Λ
    M₁ fun g => by
      refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun v => ?_))
      change (((1 : G →* Λˣ) g : Λˣ) : Λ) • v = v
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
  let μ : M₁.obj.obj.obj.V →ₗ[Λ] Lχ.obj.obj.obj.V →ₗ[Λ] Mχ.obj.obj.obj.V :=
    LinearMap.mk₂ Λ (fun (v : M) (a : ULift.{u + 1} Λ) => a.down • v)
      (fun v₁ v₂ a => smul_add a.down v₁ v₂) (fun c v a => smul_comm a.down c v)
      (fun v a₁ a₂ => add_smul a₁.down a₂.down v)
      (fun c v a => by
        change (c * a.down) • v = c • a.down • v
        rw [mul_smul])
  have hμ : ∀ (g : G) (a : M₁.obj.obj.obj.V) (b : Lχ.obj.obj.obj.V),
      μ ((M₁.obj.obj.obj.ρ g).asHom.hom a) ((Lχ.obj.obj.obj.ρ g).asHom.hom b) =
        (Mχ.obj.obj.obj.ρ g).asHom.hom (μ a b) := fun g a b => by
    change ((χ g : Λ) * b.down) • ((((1 : G →* Λˣ) g : Λˣ) : Λ) • (a : M)) =
      (χ g : Λ) • (b.down • (a : M))
    rw [MonoidHom.one_apply, Units.val_one, one_smul, mul_smul]
  have hsurj : ∀ r : Mχ.obj.obj.obj.V, ∃ p q, μ p q = r :=
    fun r => ⟨r, ULift.up 1, one_smul Λ (r : M)⟩
  have hcard : Nat.card (TensorProduct Λ M₁.obj.obj.obj.V Lχ.obj.obj.obj.V) ≤
      Nat.card Mχ.obj.obj.obj.V :=
    (Nat.card_congr ((TensorProduct.congr (LinearEquiv.refl Λ M)
      (ULift.moduleEquiv (R := Λ))).trans (TensorProduct.rid Λ M)).toEquiv).le
  have hiso := isIso_lisseEtaleSheafTensorHom B 𝕌 (affineLineOrigin k) Λ μ hμ hsurj hcard
  exact ⟨whiskerRightIso e₁.symm _ ≪≫
    @asIso _ _ _ _ (lisseEtaleSheafTensorHom B 𝕌 (affineLineOrigin k) Λ μ hμ) hiso⟩

end Tensor

/-! ### Dévissage and the vanishing of `Rf_!(M ⊗ L_ψ)` -/

section Vanishing

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **`M ↦ M ⊗ L_ψ`**, from finite `Λ`-modules to sheaves on `𝔸¹_k`: an exact functor. -/
abbrev constantTensorArtinSchreier :
    ModuleCat.{u + 1} Λ ⥤ EtaleModules.{u, 0} Λ (Spec (.of k[X])) :=
  constantSheaf (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    MonoidalCategory.tensorRight (affineLineArtinSchreierSheaf k Λ ψ B p₀)

include ψ in
/-- **`Hⁱ_c(𝔸¹_k̄, M ⊗ L_ψ) = 0`** for every finite `Λ`-module `M`, `q` invertible in `Λ` and
`∑ ψ = 0`. -/
theorem subsingleton_compactSupportSheafCohomology_constantSheaf_tensor_affineLineArtinSchreierSheaf
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (M : ModuleCat.{u + 1} Λ)
    [Finite M] (i : ℤ) :
    Subsingleton ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j
      (AlgebraicClosure k) i).obj
        (etaleModuleConstantSheaf Λ M (Spec (.of k[X])) ⊗
          affineLineArtinSchreierSheaf k Λ ψ B p₀)) := by
  let H := compactSupportSheafCohomology Λ (affineLineStructureMap k) j (AlgebraicClosure k) i
  let F := constantTensorArtinSchreier k Λ ψ B p₀
  -- modules killed by a prime `p ∤ q`
  have hprime : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Fintype.card k → ∀ (N : ModuleCat.{u + 1} Λ)
      [Finite N], (∀ v : N, p • v = 0) → Subsingleton (H.obj (F.obj N)) := by
    intro p _ hpk N _ hN
    obtain ⟨e⟩ := nonempty_constantSheaf_tensor_affineLineArtinSchreierSheaf_iso k Λ ψ B p₀ N
    let : Module (ZMod p) N := AddCommGroup.zmodModule hN
    have hp : IsUnit (Fintype.card k : ZMod p) :=
      isUnit_iff_ne_zero.2 fun h => hpk ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have h := subsingleton_compactSupportSheafCohomology_lisseEtaleSheaf_characterTwist_of_zmod k Λ
      ψ B p₀ hψ p hp j N i
    exact (H.mapIso e).toLinearEquiv.toEquiv.subsingleton
  -- the exact functor `M ↦ M ⊗ L`
  have hL := isExactTensorRight_of_isLocallyFreeEtaleModule
    (isLocallyFreeEtaleModule_affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have := hL.1
  have := hL.2.1
  have := hL.2.2
  have : PreservesFiniteColimits (constantSheaf (Spec (.of k[X])).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) :=
    have := (constantSheafAdj (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (isTerminalEtaleMkId (Spec (.of k[X])))).leftAdjoint_preservesColimits
    inferInstance
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  -- strong induction on `#M`
  suffices h : ∀ (n : ℕ) (M : ModuleCat.{u + 1} Λ) [Finite M], Nat.card M = n →
      Subsingleton (H.obj (F.obj M)) from h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ hn
  by_cases hM : Nat.card M ≤ 1
  · -- `M = 0`: it is killed by any prime larger than `q`
    obtain ⟨p, hp1, hpp⟩ := Nat.exists_infinite_primes (Fintype.card k + 1)
    have : Fact p.Prime := ⟨hpp⟩
    have : Subsingleton M := (Finite.card_le_one_iff_subsingleton).1 hM
    exact hprime p (Nat.not_dvd_of_pos_of_lt Fintype.card_pos (by omega)) M
      fun _ => Subsingleton.elim _ _
  · let : Fintype M := Fintype.ofFinite M
    let p := (Nat.card M).minFac
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨v₀, hv₀⟩ := exists_prime_addOrderOf_dvd_card (G := M) p
      (by rw [← Nat.card_eq_fintype_card]; exact Nat.minFac_dvd _)
    have hv₀0 : v₀ ≠ 0 := fun h => by
      rw [h, addOrderOf_zero] at hv₀
      exact hpp.one_lt.ne hv₀
    have hpv₀ : p • v₀ = 0 := by rw [← hv₀]; exact addOrderOf_nsmul_eq_zero v₀
    have hpk : ¬ p ∣ Fintype.card k := fun ⟨c, hc⟩ => hv₀0 <| hq.smul_eq_zero.1 <| by
      rw [Nat.cast_smul_eq_nsmul, hc, mul_nsmul, hpv₀, nsmul_zero]
    -- `0 → pM → M → M/pM → 0`
    let f : M →ₗ[Λ] M := p • LinearMap.id
    let S := LinearMap.range f
    let N₁ := ModuleCat.of Λ S
    let N₂ := ModuleCat.of Λ (M ⧸ S)
    have : Finite N₁ := inferInstanceAs (Finite S)
    have : Finite N₂ := inferInstanceAs (Finite (M ⧸ S))
    have hnotsurj : ¬ Function.Surjective f := fun hs => hv₀0 <|
      (Finite.injective_iff_surjective.2 hs) (by
        change p • v₀ = p • 0
        rw [hpv₀, nsmul_zero])
    obtain ⟨x, hx⟩ : ∃ x, x ∉ S := not_forall.1 fun h => hnotsurj fun y => h y
    have hcard : Nat.card N₁ < n := hn ▸ Finite.card_subtype_lt hx
    have h₁ : Subsingleton (H.obj (F.obj N₁)) := ih _ hcard N₁ rfl
    have h₃ : Subsingleton (H.obj (F.obj N₂)) := hprime p hpk N₂ fun w => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S w
      rw [← Submodule.Quotient.mk_smul]
      exact (Submodule.Quotient.mk_eq_zero S).2 ⟨y, rfl⟩
    let T := ModuleCat.shortComplexOfCompEqZero S.subtype S.mkQ (by ext; simp)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T (LinearMap.exact_subtype_mkQ S)
      S.injective_subtype S.mkQ_surjective
    have hT' := (hT.map_of_exact F).map_of_exact (HomologicalComplex.single
      (EtaleModules.{u, 0} Λ (Spec (.of k[X]))) (ComplexShape.up ℤ) 0)
    have hge : ∀ Y : ModuleCat.{u + 1} Λ, CochainComplex.plus _ ((HomologicalComplex.single
        (EtaleModules.{u, 0} Λ (Spec (.of k[X]))) (ComplexShape.up ℤ) 0).obj (F.obj Y)) :=
      fun _ => ⟨0, inferInstance⟩
    have hex := exact_homology_compactSupportFrobeniusFunctor_map Λ (affineLineStructureMap k) j
      (AlgebraicClosure k) hT' (hge T.X₁) (hge T.X₂) (hge T.X₃) i
    change Subsingleton (H.obj (F.obj T.X₂))
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨z, hz⟩ := (hex y).1 (@Subsingleton.elim _ h₃ _ _)
    rw [← hz, @Subsingleton.elim _ h₁ z 0, map_zero]

/-- **`Rf_!(M ⊗ L_ψ) = 0`** on the affine line, for every finite `Λ`-module `M`, a finite
commutative ring `Λ` in which `q` is invertible and an additive character `ψ` of `k` with
`∑ ψ = 0`: the kernel of the Fourier transform vanishes at a finite level, with coefficients
([Laumon, 1.2.2.1]). -/
theorem isZero_derivedLowerShriek_constantSheaf_tensor_affineLineArtinSchreierSheaf
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (M : ModuleCat.{u + 1} Λ)
    [Finite M] :
    IsZero ((derivedLowerShriek.{u, 0} (affineLineStructureMap k) j Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (etaleModuleConstantSheaf Λ M (Spec (.of k[X])) ⊗
          affineLineArtinSchreierSheaf k Λ ψ B p₀))) := by
  have : LocallyOfFiniteType (affineLineStructureMap k) := locallyOfFiniteType_specPolynomial k
  exact isZero_derivedLowerShriek_single_of_forall_subsingleton Λ (affineLineStructureMap k) j _
    fun i =>
      subsingleton_compactSupportSheafCohomology_constantSheaf_tensor_affineLineArtinSchreierSheaf
        k Λ ψ B p₀ hψ hq j M i

end Vanishing

end Stacks.EtaleCohomology

end
