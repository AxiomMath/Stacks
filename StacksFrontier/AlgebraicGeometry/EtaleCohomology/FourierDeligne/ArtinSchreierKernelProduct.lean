module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierLevelSheafTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt

/-!
# Products of pulled back Artin–Schreier sheaves

Let `L = L_ψ(g)` be the Artin–Schreier sheaf of `g ∈ A` with coefficients in a finite ring `Λ`,
and let `h₁, h₂, h₃ : Y ⟶ Spec A` be morphisms factoring as `e ≫ Spec φᵢ` through a morphism
`e : Y ⟶ Spec R` and `k`-algebra maps `φᵢ : A → R`. If `φ₁ g + φ₂ g = φ₃ g` then
`h₁⁻¹ L ⊗ h₂⁻¹ L ≅ h₃⁻¹ L`, and if `φ g = c^q - c` then `(e ≫ Spec φ)⁻¹ L` is the constant sheaf
`Λ`. These are the identities of kernels of the Fourier transform on `𝔸³ = Spec k[x, t, u]`:
`L_ψ(xt) ⊗ L_ψ(tu) ≅ L_ψ(t(x + u))`, and `L_ψ(t(x + u))` is trivial on the antidiagonal
`x + u = 0`, through which the composite of two Fourier transforms is computed in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) through Laumon's Fourier transform.

The sheaves are lisse with respect to base points: the base point of `L` on `Spec A` has to be the
image of one geometric point `ȳ` of `Spec R` under all the `Spec φᵢ` (for `𝔸³` the origin, where
`xt`, `tu` and `t(x + u)` all vanish).

## Main results

* `nonempty_finiteEtaleFiber_cover`: the geometric fibres of the Artin–Schreier cover are
  nonempty.
* `nonempty_tensor_etaleModuleInverseImage_artinSchreierLevelSheaf_iso`:
  `h₁⁻¹ L ⊗ h₂⁻¹ L ≅ h₃⁻¹ L`.
* `nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf`:
  `(e ≫ Spec φ)⁻¹ L ≅ Λ` when `φ g = c^q - c`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Polynomial Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)

/-- **The geometric fibres of the Artin–Schreier cover are nonempty**: over an algebraically
closed field the polynomial `T^q - T - g(s̄)`, of derivative `-1`, has a root. -/
theorem nonempty_finiteEtaleFiber_cover (s : GeometricPoint (Spec (.of A))) :
    Nonempty ((finiteEtaleFiberFunctor s).obj (cover k A g)) := by
  let φ : A →+* s.residueField := (Spec.preimage s.hom).hom
  have hd : derivative ((poly k g).map φ) = -1 := by
    rw [derivative_map, derivative_poly, Polynomial.map_neg, Polynomial.map_one]
  have hdeg : ((poly k g).map φ).degree ≠ 0 := fun h0 => by
    rw [eq_C_of_degree_eq_zero h0, derivative_C] at hd
    exact zero_ne_one (neg_eq_zero.1 hd.symm).symm
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  have hr' : (poly k g).eval₂ φ r = 0 := (Polynomial.eval_map φ r).symm.trans hr
  let ψ : Ring k g →+* s.residueField := AdjoinRoot.lift φ r hr'
  refine ⟨⟨Spec.map (CommRingCat.ofHom ψ), ?_⟩⟩
  change Spec.map (CommRingCat.ofHom ψ) ≫ coverHom k A g = s.hom
  rw [← Spec.map_comp]
  have hψ : CommRingCat.ofHom (algebraMap A (Ring k g)) ≫ CommRingCat.ofHom ψ =
      Spec.preimage s.hom := by
    ext a
    exact AdjoinRoot.lift_of hr'
  rw [hψ, Spec.map_preimage]

variable {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')
  [ConnectedSpace (Spec (.of A))] [ConnectedSpace (Spec (.of A'))]
  (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (hX : schemeSizeBelow B.cutoff (Spec (.of A))) (hX' : schemeSizeBelow B.cutoff (Spec (.of A')))

/-- T4 (c) with the base point and the function given up to equality: the inverse image of
`L_ψ(g)` (base point `x̄`) along `Spec φ` is `L_ψ(g')` (base point `ȳ`) when `x̄` is the image of
`ȳ` and `φ g = g'`. -/
theorem nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_eq
    {x : GeometricPoint (Spec (.of A))} (y : GeometricPoint (Spec (.of A')))
    (hy : y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)) = x)
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) {g' : A'} (hg : φ g = g')
    (p₀' : (finiteEtaleFiberFunctor y).obj (cover k A' g')) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
        (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅
      artinSchreierLevelSheaf k A' g' Λ ψ B hX' y p₀') := by
  subst hy hg
  exact nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso k g φ Λ ψ B hX hX' y p₀ p₀'

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

/-- T4 (d) with the sum given up to equality: `L_ψ(g₁) ⊗ L_ψ(g₂) ≅ L_ψ(g₃)` when
`g₁ + g₂ = g₃`. -/
theorem nonempty_artinSchreierLevelSheaf_tensor_iso_of_add_eq (g₁ g₂ g₃ : A) (h : g₁ + g₂ = g₃)
    (x : GeometricPoint (Spec (.of A)))
    (p₁ : (finiteEtaleFiberFunctor x).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor x).obj (cover k A g₂))
    (p₃ : (finiteEtaleFiberFunctor x).obj (cover k A g₃)) :
    Nonempty (artinSchreierLevelSheaf k A g₁ Λ ψ B hX x p₁ ⊗
        artinSchreierLevelSheaf k A g₂ Λ ψ B hX x p₂ ≅
      artinSchreierLevelSheaf k A g₃ Λ ψ B hX x p₃) := by
  subst h
  exact ⟨artinSchreierLevelSheafTensorIso k A g₁ g₂ Λ ψ B hX x p₁ p₂ p₃⟩

attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal

variable {Y : Scheme.{u}} (e : Y ⟶ Spec (.of A'))

/-- The inverse image of `L_ψ(g)` along `e ≫ Spec φ` is that of `L_ψ(φ g)` along `e`. -/
private theorem nonempty_etaleModuleInverseImage_comp_iso_artinSchreierLevelSheaf
    {x : GeometricPoint (Spec (.of A))} (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (y : GeometricPoint (Spec (.of A')))
    (hy : y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)) = x)
    (q : (finiteEtaleFiberFunctor y).obj (cover k A' (φ g))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ
        (e ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
          (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅
      (etaleModuleInverseImage.{u, 0} Λ e).obj
        (artinSchreierLevelSheaf k A' (φ g) Λ ψ B hX' y q)) := by
  obtain ⟨a⟩ := nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_of_eq k g φ Λ ψ B
    hX hX' y hy p₀ rfl q
  exact ⟨(etaleModuleInverseImageCompIso Λ e (Spec.map (CommRingCat.ofHom φ.toRingHom))).app _ ≪≫
    (etaleModuleInverseImage.{u, 0} Λ e).mapIso a⟩

include hX' in
/-- **`h₁⁻¹ L ⊗ h₂⁻¹ L ≅ h₃⁻¹ L`** for `L = L_ψ(g)` on `Spec A` and morphisms `hᵢ = e ≫ Spec φᵢ`
with `φ₁ g + φ₂ g = φ₃ g`, the base point `x̄` of `L` being the image of a geometric point `ȳ` of
`Spec A'` under the three `Spec φᵢ`: `(Spec φᵢ)⁻¹ L ≅ L_ψ(φᵢ g)` (T4 (c)), the inverse image along
`e` is monoidal, and `L_ψ(φ₁ g) ⊗ L_ψ(φ₂ g) ≅ L_ψ(φ₃ g)` (T4 (d)). -/
theorem nonempty_tensor_etaleModuleInverseImage_artinSchreierLevelSheaf_iso
    (φ₁ φ₂ φ₃ : A →ₐ[k] A') (hφ : φ₁ g + φ₂ g = φ₃ g) {h₁ h₂ h₃ : Y ⟶ Spec (.of A)}
    (hh₁ : h₁ = e ≫ Spec.map (CommRingCat.ofHom φ₁.toRingHom))
    (hh₂ : h₂ = e ≫ Spec.map (CommRingCat.ofHom φ₂.toRingHom))
    (hh₃ : h₃ = e ≫ Spec.map (CommRingCat.ofHom φ₃.toRingHom))
    {x : GeometricPoint (Spec (.of A))} (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (y : GeometricPoint (Spec (.of A')))
    (hy₁ : y.map (Spec.map (CommRingCat.ofHom φ₁.toRingHom)) = x)
    (hy₂ : y.map (Spec.map (CommRingCat.ofHom φ₂.toRingHom)) = x)
    (hy₃ : y.map (Spec.map (CommRingCat.ofHom φ₃.toRingHom)) = x) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ h₁).obj
          (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ⊗
        (etaleModuleInverseImage.{u, 0} Λ h₂).obj (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅
      (etaleModuleInverseImage.{u, 0} Λ h₃).obj (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀)) := by
  subst hh₁ hh₂ hh₃
  obtain ⟨q₁⟩ := nonempty_finiteEtaleFiber_cover k (φ₁ g) y
  obtain ⟨q₂⟩ := nonempty_finiteEtaleFiber_cover k (φ₂ g) y
  obtain ⟨q₃⟩ := nonempty_finiteEtaleFiber_cover k (φ₃ g) y
  obtain ⟨a₁⟩ := nonempty_etaleModuleInverseImage_comp_iso_artinSchreierLevelSheaf k g φ₁ Λ ψ B
    hX hX' e p₀ y hy₁ q₁
  obtain ⟨a₂⟩ := nonempty_etaleModuleInverseImage_comp_iso_artinSchreierLevelSheaf k g φ₂ Λ ψ B
    hX hX' e p₀ y hy₂ q₂
  obtain ⟨a₃⟩ := nonempty_etaleModuleInverseImage_comp_iso_artinSchreierLevelSheaf k g φ₃ Λ ψ B
    hX hX' e p₀ y hy₃ q₃
  obtain ⟨m⟩ := nonempty_artinSchreierLevelSheaf_tensor_iso_of_add_eq k Λ ψ B hX' _ _ _ hφ y
    q₁ q₂ q₃
  exact ⟨(a₁ ⊗ᵢ a₂) ≪≫ Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ e) _ _ ≪≫
    (etaleModuleInverseImage.{u, 0} Λ e).mapIso m ≪≫ a₃.symm⟩

include hX' in
/-- **`(e ≫ Spec φ)⁻¹ L_ψ(g)` is the constant sheaf `Λ` when `φ g = c^q - c`**, the base point of
`L_ψ(g)` being the image of a geometric point of `Spec A'`: `(Spec φ)⁻¹ L_ψ(g) ≅ L_ψ(c^q - c)`
(T4 (c)), which is constant (T4 (e)), and the inverse image of a constant sheaf is constant. -/
theorem nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso_constantSheaf
    (c : A') (hc : φ g = c ^ Fintype.card k - c) {h : Y ⟶ Spec (.of A)}
    (hh : h = e ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    {x : GeometricPoint (Spec (.of A))} (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (y : GeometricPoint (Spec (.of A')))
    (hy : y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)) = x) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ h).obj
        (artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) ≅
      etaleModuleConstantSheaf Λ (ModuleCat.of Λ (ULift.{u + 1} Λ)) Y) := by
  subst hh
  obtain ⟨q⟩ := nonempty_finiteEtaleFiber_cover k (φ g) y
  obtain ⟨a⟩ := nonempty_etaleModuleInverseImage_comp_iso_artinSchreierLevelSheaf k g φ Λ ψ B
    hX hX' e p₀ y hy q
  obtain ⟨b⟩ := nonempty_artinSchreierLevelSheaf_iso_constantSheaf_of_sub_eq k A' (φ g) Λ ψ B hX'
    c hc.symm y q
  exact ⟨a ≪≫ (etaleModuleInverseImage.{u, 0} Λ e).mapIso b ≪≫
    (etaleModuleInverseImageConstantIso Λ e).app (ModuleCat.of Λ (ULift.{u + 1} Λ))⟩

end Stacks.ArtinSchreier
