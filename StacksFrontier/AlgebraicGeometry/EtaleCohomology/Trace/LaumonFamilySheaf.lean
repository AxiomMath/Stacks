module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekEnd
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Sheaf

/-!
# The family sheaf of Laumon's degeneration and its `R¹pr₂!`

Let `k'` be a finite field, `E` a finite extension of `ℚ_ℓ` with a `ℚ_ℓ`-basis `b`, `ψ'` an
additive character of `k'` with values in `E`, `n₀ ∈ ℕ` and `c ∈ k'`. On the plane
`𝔸² = Spec k'[x][t]` (`x` the coordinate of the curve, `t` the parameter) the kernel of the family
restricted to the line `(a, c') = (t, c t)` of the `(a, c')`-plane is
`g = t (xⁿ⁰ + c x)` (`Stacks.EtaleCohomology.laumonKernel`). For a representation `σ₁` of
`π₁(𝔸¹_{k'})` with coefficients in `E`, the family sheaf is `pr₁^*ℱ_{σ₁} ⊗ L_ψ'(g)`: the sheaf
`ℱ_{Res_b K}` of the twist `K = pr₁^*σ₁ ⊗ ψ'(-χ_g)` (`Stacks.EtaleCohomology.laumonFamilyRep`),
with the action of the integral part of `E` (`Stacks.EtaleCohomology.laumonFamilySheaf`,
through `Stacks.EtaleCohomology.restrictScalarsRepCoefficientSheaf`, exactly as the fibres in
`Stacks.EtaleCohomology.LaumonFibrePure`). Its higher direct image with compact support along
`pr₂ : 𝔸² → 𝔸¹_t` is `G = R¹pr₂!`, with the induced action of the coefficients
(`Stacks.EtaleCohomology.laumonFamilyHigherDirectImage`, through
`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.higherDirectImageShriek`). This is the
sheaf `G` of Laumon's degeneration argument in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.laumonKernel`, `Stacks.EtaleCohomology.laumonFamilyRep`,
  `Stacks.EtaleCohomology.laumonFamilySheaf`, `Stacks.EtaleCohomology.laumonFamilyProjection`,
  `Stacks.EtaleCohomology.laumonFamilyHigherDirectImage`.

## Main results

* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter`:
  the twist of a continuous `Res_b σ` by an Artin–Schreier character is continuous.
* `Stacks.EtaleCohomology.laumonKernel_eval`: the specialisation of the kernel at `t = s` is
  `s xⁿ⁰ + (c s) x`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Polynomial

universe u

namespace Stacks.EtaleCohomology

section Continuity

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))] {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E]
  {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ : AddChar k E) (x : GeometricPoint (Spec (.of A)))
  (p₀ : (finiteEtaleFiberFunctor x).obj (Stacks.ArtinSchreier.cover k A g)) {m : ℕ}

/-- **The twist of a continuous `Res_b σ` by an Artin–Schreier character is continuous**: the
character factors through the finite discrete group `k`. -/
public theorem continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter
    (σ : EtaleFundamentalGroup (Spec (.of A)) x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) :
    Continuous (restrictScalarsRep b (characterTwist σ
      (Stacks.ArtinSchreier.artinSchreierCharacter k A g ψ x p₀))) := by
  let : TopologicalSpace (Multiplicative k) := ⊥
  have : DiscreteTopology (Multiplicative k) := ⟨rfl⟩
  refine continuous_restrictScalarsRep b _ ?_
  have h : (fun γ => restrictScalarsMatrix b (characterTwist σ
      (Stacks.ArtinSchreier.artinSchreierCharacter k A g ψ x p₀) γ).val) = fun γ =>
      restrictScalarsMatrix b (σ γ).val * (fun a : Multiplicative k =>
        restrictScalarsMatrix b (Matrix.scalar (Fin m) (ψ (-Multiplicative.toAdd a))))
          ((Stacks.ArtinSchreier.torsorCover k A g).character x p₀ γ) := by
    funext γ
    change restrictScalarsMatrix b ((σ γ).val * Matrix.scalar (Fin m)
      ((Stacks.ArtinSchreier.artinSchreierCharacter k A g ψ x p₀ γ : Eˣ) : E)) = _
    rw [restrictScalarsMatrix_mul, Stacks.ArtinSchreier.artinSchreierCharacter_apply]
  rw [h]
  refine Continuous.mul ?_ ((continuous_of_discreteTopology (f := fun a : Multiplicative k =>
    restrictScalarsMatrix b (Matrix.scalar (Fin m) (ψ (-Multiplicative.toAdd a))))).comp
      ((Stacks.ArtinSchreier.torsorCover k A g).continuous_character x p₀))
  have := Units.continuous_val.comp hσ
  simpa [Function.comp_def, restrictScalarsRep_val] using this

end Continuity

section Kernel

variable (k' : Type u) [Field k']

/-- **The kernel `g = t (xⁿ⁰ + c x)` of the family on the line `(a, c') = (t, c t)`**, in
`k'[x][t]` (`x` the inner variable, `t` the outer one). -/
public def laumonKernel (n₀ : ℕ) (c : k') : Polynomial (Polynomial k') :=
  Polynomial.C (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X) * Polynomial.X

/-- **The specialisation of the kernel at `t = s`** (for a ring map `f : k' → κ` and `s ∈ κ`):
`s xⁿ⁰ + (f(c) s) x`, the kernel of `Stacks.EtaleCohomology.LaumonFibrePure` at
`(a, c') = (s, c s)`. -/
public theorem laumonKernel_eval {κ : Type*} [CommRing κ] (f : k' →+* κ) (n₀ : ℕ) (c : k') (s : κ) :
    eval₂ (mapRingHom f) (Polynomial.C s) (laumonKernel k' n₀ c) =
      Polynomial.C s * Polynomial.X ^ n₀ + Polynomial.C (f c * s) * Polynomial.X := by
  simp only [laumonKernel, eval₂_mul, eval₂_C, eval₂_X, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_mul, map_X, map_C, coe_mapRingHom, C_mul]
  ring

end Kernel

section Family

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (n₀ : ℕ) (c : k')
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}

/-- The first projection `pr₁ : Spec k'[x][t] → Spec k'[x]`: `Spec` of the coefficient
embedding `Polynomial.C : k'[x] → k'[x][t]`, not of
`algebraMap (Polynomial k') (Polynomial (Polynomial k'))` (`p ↦ p.map C`, i.e. `x ↦ t`), which is
the ring map of `Stacks.EtaleCohomology.laumonFamilyPr₂`. -/
public abbrev laumonFamilyPr₁ :
    Spec (.of (Polynomial (Polynomial k'))) ⟶ Spec (.of (Polynomial k')) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : Polynomial k' →+* Polynomial (Polynomial k')))

/-- The second projection `pr₂ : Spec k'[x][t] → Spec k'[t]`. -/
public abbrev laumonFamilyPr₂ :
    Spec (.of (Polynomial (Polynomial k'))) ⟶ Spec (.of (Polynomial k')) :=
  Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k' (Polynomial k'))))

omit [Fintype k'] in
/-- **The two projections differ**: `pr₁` pulls `x` back to the inner variable `C X` of
`k'[x][t]`, `pr₂` pulls the coordinate back to the outer variable `X`. -/
public theorem laumonFamilyPr₁_ne_laumonFamilyPr₂ : laumonFamilyPr₁ k' ≠ laumonFamilyPr₂ k' := by
  intro h
  have h' := congrArg (fun φ : CommRingCat.of (Polynomial k') ⟶
    CommRingCat.of (Polynomial (Polynomial k')) => φ.hom Polynomial.X) (Spec.map_injective h)
  simp only [CommRingCat.hom_ofHom, coe_mapRingHom, map_X] at h'
  have h'' := congrArg Polynomial.natDegree h'
  rw [natDegree_C, natDegree_X] at h''
  exact zero_ne_one h''

/-- **The representation of the family sheaf**: `pr₁^* σ₁` twisted by the Artin–Schreier
character `ψ'(-χ_g)` of the kernel `g = t (xⁿ⁰ + c x)`. -/
public def laumonFamilyRep
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) :
    EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z →* GL (Fin m) E :=
  characterTwist (σ₁.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (laumonKernel k' n₀ c) ψ' z p₀)

/-- If `Res_b σ₁` is continuous, then so is `Res_b` of the family representation
`Stacks.EtaleCohomology.laumonFamilyRep`. -/
public theorem continuous_restrictScalarsRep_laumonFamilyRep
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) :
    Continuous (restrictScalarsRep b (laumonFamilyRep k' ψ' n₀ c z p₀ σ₁)) :=
  continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter k'
    (Polynomial (Polynomial k')) (laumonKernel k' n₀ c) b ψ' z p₀ _
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

/-- **The family sheaf `pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` on `Spec k'[x][t]`**, with the action of
the integral part of `E`: `ℱ_{Res_b K}` for the twisted representation `K`
(`Stacks.EtaleCohomology.laumonFamilyRep`). -/
public def laumonFamilySheaf
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) :=
  restrictScalarsRepCoefficientSheaf B
    (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    z b (laumonFamilyRep k' ψ' n₀ c z p₀ σ₁)
    (continuous_restrictScalarsRep_laumonFamilyRep k' b ψ' n₀ c z p₀ σ₁ hσ₁)

/-- **`pr₂ : Spec k'[x][t] → Spec k'[t]`**, as a morphism of the big étale site. -/
public abbrev laumonFamilyProjection :
    Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS ⟶
      Stacks.ArtinSchreier.specObject (Polynomial k') B hL :=
  ObjectProperty.homMk (laumonFamilyPr₂ k')

omit [Fintype k'] in
/-- The ring map `k'[t] → k'[x][t]` of `pr₂`, mapping coefficients along `k' → k'[x]`, is of
finite type. -/
public theorem finiteType_mapRingHom_algebraMap :
    (mapRingHom (algebraMap k' (Polynomial k'))).FiniteType := by
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k' (Polynomial k')) ?_
  have h : (mapRingHom (algebraMap k' (Polynomial k'))).comp (algebraMap k' (Polynomial k')) =
      algebraMap k' (Polynomial (Polynomial k')) := by
    refine RingHom.ext fun a => ?_
    simp
  rw [h]
  exact RingHom.finiteType_algebraMap.2 inferInstance

omit [Fintype k'] in
/-- The second projection `pr₂ : Spec k'[x][t] → Spec k'[t]` is locally of finite type. -/
public instance locallyOfFiniteType_laumonFamilyPr₂ : LocallyOfFiniteType (laumonFamilyPr₂ k') := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact finiteType_mapRingHom_algebraMap k'

/-- The underlying morphism of schemes of `pr₂` is locally of finite type. -/
public instance locallyOfFiniteType_laumonFamilyProjection :
    LocallyOfFiniteType (B.inclusion.map (laumonFamilyProjection k' B hS hL)) :=
  locallyOfFiniteType_laumonFamilyPr₂ k'

/-- The underlying morphism of schemes of `pr₂` is quasi-compact. -/
public instance quasiCompact_laumonFamilyProjection :
    QuasiCompact (B.inclusion.map (laumonFamilyProjection k' B hS hL)) :=
  inferInstanceAs (QuasiCompact (laumonFamilyPr₂ k'))

/-- The underlying morphism of schemes of `pr₂` is separated. -/
public instance isSeparated_laumonFamilyProjection :
    IsSeparated (B.inclusion.map (laumonFamilyProjection k' B hS hL)) :=
  inferInstanceAs (IsSeparated (laumonFamilyPr₂ k'))

/-- **`G = R¹pr₂!` of the family sheaf**, a sheaf on `𝔸¹_t = Spec k'[t]` with the induced action of
the integral part of `E`
(`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.higherDirectImageShriek`),
for a compactification `jg` of `pr₂`. -/
public def laumonFamilyHigherDirectImage
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL)))) :=
  (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).higherDirectImageShriek B ℓ
    (laumonFamilyProjection k' B hS hL) jg 1

end Family

end Stacks.EtaleCohomology
