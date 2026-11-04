module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity

/-!
# The Fourier family of Laumon's argument at a fixed `a`

Let `k'` be a finite field, `E` a finite extension of `ℚ_ℓ` with a `ℚ_ℓ`-basis `b`, `ψ'` an
additive character of `k'` with values in `E`, `n ∈ ℕ` and `a ∈ k'`. On the plane
`𝔸² = Spec k'[x][t]` (`x` the coordinate of the curve, `t` the parameter `c`) the kernel of the
family of fibres `H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` at fixed `a` is
`g = a xⁿ + x t` (`Stacks.EtaleCohomology.laumonFourierKernel`). For a representation `σ₁` of
`π₁(𝔸¹_{k'})` with coefficients in `E`, the family sheaf is `pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t)`: the
sheaf `ℱ_{Res_b K}` of the twist `K = pr₁^*σ₁ ⊗ ψ'(-χ_g)`
(`Stacks.EtaleCohomology.laumonFourierFamilyRep`), with the action of the integral part of `E`
(`Stacks.EtaleCohomology.laumonFourierFamilySheaf`). Its `R¹pr₂!` is the (naive) Fourier
transform of `ℱ_{σ₁} ⊗ L_ψ'(a xⁿ)`; its specialisation at `t = c` is the kernel `a xⁿ + c x` of
the fibres of `Stacks.EtaleCohomology.LaumonFibreCharpoly`
(`Stacks.EtaleCohomology.laumonFourierKernel_eval`).

## Main definitions

* `Stacks.EtaleCohomology.laumonFourierKernel`, `Stacks.EtaleCohomology.laumonFourierFamilyRep`,
  `Stacks.EtaleCohomology.laumonFourierFamilySheaf`,
  `Stacks.EtaleCohomology.laumonFourierRestrictedHigherDirectImage`.

## Main results

* `Stacks.EtaleCohomology.laumonFourierKernel_eval`.
* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_laumonFourierFamilyRep`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Polynomial

universe u

namespace Stacks.EtaleCohomology

section Kernel

variable (k' : Type u) [Field k']

/-- **The kernel `g = a xⁿ + x t` of the Fourier family at fixed `a`**, in `k'[x][t]` (`x` the
inner variable, `t` the outer one). -/
public def laumonFourierKernel (n : ℕ) (a : k') : Polynomial (Polynomial k') :=
  Polynomial.C (Polynomial.C a * Polynomial.X ^ n) + Polynomial.C Polynomial.X * Polynomial.X

/-- **The specialisation of the kernel at `t = s`** (for a ring map `f : k' → κ` and `s ∈ κ`):
`f(a) xⁿ + s x`, the kernel of `Stacks.EtaleCohomology.LaumonFibreCharpoly` at `(f(a), s)`. -/
public theorem laumonFourierKernel_eval {κ : Type*} [CommRing κ] (f : k' →+* κ) (n : ℕ) (a : k')
    (s : κ) :
    eval₂ (mapRingHom f) (Polynomial.C s) (laumonFourierKernel k' n a) =
      Polynomial.C (f a) * Polynomial.X ^ n + Polynomial.C s * Polynomial.X := by
  simp only [laumonFourierKernel, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C, coe_mapRingHom]
  ring

end Kernel

section Family

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (n : ℕ) (a : k')
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
  {m : ℕ}

/-- **The representation of the Fourier family sheaf**: `pr₁^* σ₁` twisted by the Artin–Schreier
character `ψ'(-χ_g)` of the kernel `g = a xⁿ + x t`. -/
public def laumonFourierFamilyRep
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) :
    EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z →* GL (Fin m) E :=
  characterTwist (σ₁.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (laumonFourierKernel k' n a) ψ' z p₀)

/-- **`Res_b K` is continuous when `Res_b σ₁` is**, for the twisted representation `K`
(`Stacks.EtaleCohomology.laumonFourierFamilyRep`). -/
public theorem continuous_restrictScalarsRep_laumonFourierFamilyRep
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) :
    Continuous (restrictScalarsRep b (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁)) :=
  continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter k'
    (Polynomial (Polynomial k')) (laumonFourierKernel k' n a) b ψ' z p₀ _
    (hσ₁.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).continuous)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Fourier family sheaf `pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t)` on `Spec k'[x][t]`**, with the
action of the integral part of `E`: `ℱ_{Res_b K}` for the twisted representation `K`
(`Stacks.EtaleCohomology.laumonFourierFamilyRep`). -/
public def laumonFourierFamilySheaf
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) :=
  restrictScalarsRepCoefficientSheaf B
    (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    z b (laumonFourierFamilyRep k' ψ' n a z p₀ σ₁)
    (continuous_restrictScalarsRep_laumonFourierFamilyRep k' b ψ' n a z p₀ σ₁ hσ₁)

end Family

section Reduction

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (ℓ : ℕ) [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (n : ℕ) (a : k')
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
  {m : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **`G_V = R¹g'_!(K|_{U'})` for the Fourier family**: the higher direct image with compact
support of the restriction of the Fourier family sheaf `K`
(`Stacks.EtaleCohomology.laumonFourierFamilySheaf`) to `U' ⟶ Spec k'[x][t]`, along
`g' : U' ⟶ V'`, with the induced action of the integral part of `E`. -/
public abbrev laumonFourierRestrictedHigherDirectImage
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) {V' U' : B.Scheme}
    [IsNoetherian V'.1] [IsNoetherian U'.1]
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))) :=
  haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (laumonFourierFamilySheaf k' B hS b ψ' n a z p₀ σ₁ hσ₁)).higherDirectImageShriek B ℓ g' jg' 1

end Reduction

end Stacks.EtaleCohomology

end
