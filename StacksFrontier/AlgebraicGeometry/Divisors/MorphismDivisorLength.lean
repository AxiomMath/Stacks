module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.StalkBasis
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalkBasisGenericPoint
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismDivisorSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.RingTheory.HilbertSamuel.Function

/-!
# The multiplicity of the divisor of a morphism is at most the colength of its stalk map

Let `L`, `L'` be invertible modules on an integral scheme and `σ : L ⟶ L'`. At a point `x`,
the length of `𝒪_{X, x}` modulo the stalk of the divisor of `σ` is at most the length of
`L'_x ⧸ im(σ_x)`.

Both are lengths of a quotient of a free rank-one module, and they are in fact equal; only the
inequality is proved, because only it is needed and it is by far the cheaper half. On a
trivializing affine open `U ∋ x` with `e : Γ(L', U) ≃ₗ Γ(X, U)` the germ `α` of `e (σ v₀)`,
for `v₀` a generator of `L_x` coming from `U`, is a generator of the image of `σ_x` read in the
coordinate `e`; it lies in the stalk of the divisor by
`AlgebraicGeometry.mem_ideal_morphismZeroScheme`, so that stalk contains `(α)` and the quotient
by it is a quotient of `𝒪_{X, x} ⧸ (α) ≃ L'_x ⧸ im(σ_x)`. The reverse inclusion would need
every functional on the sections of the internal hom to be of that form, which is a
trivialization of the internal hom; nothing in the library builds one.

## Main results

* `AlgebraicGeometry.germ_mem_stalk_morphismZeroScheme`: the germ of a value `ψ (σ v)` lies in
  the stalk of the divisor of `σ`.
* `AlgebraicGeometry.length_quotient_stalk_morphismZeroScheme_le`: **the multiplicity bound.**

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Divisors (IsStalkBasis)

variable {X : Scheme.{u}} (L L' : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L'] in
/-- A trivialization of the sections over `U` writes every section as a multiple of the one
sent to `1`. -/
theorem eq_smul_symm_one {U : X.Opens} (e : Γ(L', U) ≃ₗ[Γ(X, U)] Γ(X, U)) (t : Γ(L', U)) :
    t = e t • e.symm 1 := by
  conv_lhs => rw [← e.symm_apply_apply t]
  rw [← map_smul e.symm (e t) 1, smul_eq_mul, mul_one]

/-- The germ of the section a trivialization sends to `1` is a stalk basis: it is a unit
multiple of a germ that already is one. -/
theorem isStalkBasis_germ_symm_one {U : X.Opens} (e : Γ(L', U) ≃ₗ[Γ(X, U)] Γ(X, U)) {x : X}
    (hx : x ∈ U) {t : Γ(L', U)} (ht : IsStalkBasis L' x (L'.presheaf.germ U x hx t)) :
    IsStalkBasis L' x (L'.presheaf.germ U x hx (e.symm 1)) := by
  refine (Stacks.Divisors.isStalkBasis_iff_span_eq_top L' x _).2 (top_le_iff.1 ?_)
  rw [← ht.span_eq_top]
  refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
  refine Submodule.mem_span_singleton.2 ⟨X.presheaf.germ U x hx (e t), ?_⟩
  rw [← Scheme.Modules.germ_smul, ← eq_smul_symm_one]

/-- **The germ of a value `ψ (σ v)` lies in the stalk of the divisor of `σ`.** -/
theorem germ_mem_stalk_morphismZeroScheme (σ : L ⟶ L') (U : X.affineOpens) {x : X}
    (hx : x ∈ U.1) (v : Γ(L, U.1)) (ψ : Γ(L', U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1)) :
    (X.presheaf.germ U.1 x hx).hom (ψ (σ.app U.1 v)) ∈
      IdealSheafData.stalk (morphismZeroScheme L L' σ) x :=
  IdealSheafData.map_germ_le_stalk _ U hx
    (Ideal.mem_map_of_mem _ (mem_ideal_morphismZeroScheme L L' σ U v ψ))

variable {L L'}

/-- **The multiplicity at `x` of the divisor of a morphism of invertible modules is at most the
length of the cokernel of its stalk map at `x`.** -/
theorem length_quotient_stalk_morphismZeroScheme_le (σ : L ⟶ L') (x : X) :
    Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ IdealSheafData.stalk (morphismZeroScheme L L' σ) x)
      ≤ Module.length (X.presheaf.stalk x)
        (L'.presheaf.stalk x ⧸ LinearMap.range (Stacks.ModuleStalk.map σ x)) := by
  classical
  obtain ⟨W₁, hxW₁, w, hw⟩ :=
    Stacks.Divisors.exists_isStalkBasis_germ_of_isInvertible L ‹_› x
  obtain ⟨W₂, hxW₂, u, hu⟩ :=
    Stacks.Divisors.exists_isStalkBasis_germ_of_isInvertible L' ‹_› x
  obtain ⟨U, hxU, hUle, ⟨e⟩⟩ :=
    exists_affineOpens_linearEquiv_le X L' x (W₁ ⊓ W₂) ⟨hxW₁, hxW₂⟩
  set v₀ : Γ(L, U.1) := L.presheaf.map (homOfLE (hUle.trans inf_le_left)).op w with hv₀
  set u₀ : Γ(L', U.1) := e.symm 1 with hu₀
  have hb : IsStalkBasis L x (L.presheaf.germ U.1 x hxU v₀) := by
    rw [hv₀, L.presheaf.germ_res_apply (homOfLE (hUle.trans inf_le_left)) x hxU w]
    exact hw
  have hb' : IsStalkBasis L' x (L'.presheaf.germ U.1 x hxU u₀) := by
    refine isStalkBasis_germ_symm_one L' e hxU (t :=
      L'.presheaf.map (homOfLE (hUle.trans inf_le_right)).op u) ?_
    rw [L'.presheaf.germ_res_apply (homOfLE (hUle.trans inf_le_right)) x hxU u]
    exact hu
  set α : X.presheaf.stalk x := X.presheaf.germ U.1 x hxU (e (σ.app U.1 v₀)) with hα
  -- the stalk map sends the basis of `L_x` to `α` times the basis of `L'_x`
  have hσb : Stacks.ModuleStalk.map σ x (L.presheaf.germ U.1 x hxU v₀)
      = α • L'.presheaf.germ U.1 x hxU u₀ := by
    rw [Stacks.ModuleStalk.map_apply, Stacks.ModuleStalk.mapFun_germ, hα,
      ← Scheme.Modules.germ_smul, ← eq_smul_symm_one]
  -- the image of the stalk map is the span of that element
  have hrange : LinearMap.range (Stacks.ModuleStalk.map σ x)
      = Submodule.span (X.presheaf.stalk x)
        {Stacks.ModuleStalk.map σ x (L.presheaf.germ U.1 x hxU v₀)} := by
    rw [LinearMap.range_eq_map, ← hb.span_eq_top, Submodule.map_span, Set.image_singleton]
  -- read in the coordinate of `L'_x` the image becomes the ideal generated by `α`
  have hmap : Submodule.map hb'.coord.toLinearMap
      (LinearMap.range (Stacks.ModuleStalk.map σ x)) = Ideal.span {α} := by
    rw [hrange, Submodule.map_span, Set.image_singleton]
    exact congrArg (fun z : X.presheaf.stalk x => Ideal.span {z})
      (by rw [hσb]; exact hb'.coord_smul α)
  have hlen : Module.length (X.presheaf.stalk x)
      (L'.presheaf.stalk x ⧸ LinearMap.range (Stacks.ModuleStalk.map σ x))
      = Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ Ideal.span {α}) :=
    (Submodule.Quotient.equiv _ _ hb'.coord hmap).length_eq
  rw [hlen]
  refine length_quotient_antitone (Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_))
  exact germ_mem_stalk_morphismZeroScheme L L' σ U hxU v₀ e.toLinearMap

end AlgebraicGeometry

end
