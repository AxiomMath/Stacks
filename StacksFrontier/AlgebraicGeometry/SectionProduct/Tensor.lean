module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio

/-!
# Products of sections of a tensor product of modules on a scheme

Let `X` be a scheme and `M`, `N` two `𝒪_X`-modules. Sections `s` of `M` and `t` of `N` over an
open `U` have a product `s ⊗ t`, a section of `M ⊗_{𝒪_X} N` over `U`: the image of the pure
tensor under `Γ(M, U) ⊗_{Γ(X, U)} Γ(N, U) → Γ(M ⊗ N, U)`. This is
`Stacks.SheafOfModules.tensorSectionsAt`; this file develops its calculus.

* The product is `𝒪_X`-bilinear and commutes with restriction.
* At a point `x` its germ is the pure tensor of the germs, under
  `(M ⊗ N)_x ≅ M_x ⊗_{𝒪_{X,x}} N_x` ([Stacks, Tag 01CB]).
* **`X_{s ⊗ t} = X_s ∩ X_t`** for global sections, where `X_s` is the set of points at which the
  germ of `s` does not lie in `𝔪_x M_x`. This holds for arbitrary modules, by the local algebra
  statement that over a local ring `R` a pure tensor `m ⊗ n` with `m ∉ 𝔪 M` and `n ∉ 𝔪 N` does
  not lie in `𝔪 (M ⊗_R N)`: linear forms `φ : M → κ` and `ψ : N → κ` to the residue field with
  `φ m ≠ 0 ≠ ψ n` give `φ ⊗ ψ : M ⊗_R N → κ`, which kills `𝔪 (M ⊗_R N)` and not `m ⊗ n`.
* For invertible `M` and `N`, on an open where `s` and `t` do not vanish the ratio of
  `m ⊗ n` by `s ⊗ t` is `(m / s) (n / t)`; in particular the ratios of a family of products are
  the products of the ratios, and `s' ⊗ t = s ⊗ t'` forces `s' / s = t' / t`.
* The product commutes with pullback along a morphism of schemes `f : Y ⟶ X`: the canonical
  isomorphism `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` of [Stacks, Tag 01CD] carries `f^*(s ⊗ t)` to
  `f^*s ⊗ f^*t`.

## Main results

* `TensorProduct.tmul_notMem_maximalIdeal_smul_top`: the local algebra statement above.
* `Stacks.SectionProduct.tensorStalkEquiv_germ_tensorSectionsAt`: the germ of a product.
* `Stacks.SectionProduct.tensorSectionsAt_smul_smul`, `Stacks.SectionProduct.map_tensorSectionsAt`:
  bilinearity and compatibility with restriction.
* `Stacks.SectionProduct.nonvanishingLocus_tensorSectionsAt` and
  `Stacks.SectionProduct.nvOpen_tensorSectionsAt`: `X_{s ⊗ t} = X_s ∩ X_t`.
* `Stacks.SectionProduct.isInvertibleModule_tensorObj`: `M ⊗ N` is invertible when `M` and `N`
  are ([Stacks, Tag 01CT]).
* `Stacks.SectionProduct.div_tensorSectionsAt`, `Stacks.SectionProduct.ratio_tensorSectionsAt`
  and `Stacks.SectionProduct.div_eq_div_of_tensorSectionsAt_eq`: ratios multiply.
* `Stacks.SectionProduct.comparison_pullbackUnit_tensorSectionsAt` and
  `Stacks.SectionProduct.comparison_pullbackGlobalSection_tensorSectionsAt`: compatibility with
  pullback.

## Implementation notes

The tensor product is `AlgebraicGeometry.Scheme.Modules.tensorObj`, the sheafification of the
sectionwise tensor product, and the product of sections is the sheafification unit applied to a
pure tensor, with the structure sheaf written `X.sheaf.obj` so that the type of the product is
syntactically the module of sections of `Scheme.Modules.tensorObj M N`. The ratios are those of
`Stacks.ProjectiveFromSections.div`, whose defining property is uniqueness, so every identity
between ratios is proved by multiplying out.

Invertibility is `Stacks.Ample.IsInvertibleModule`, the spelling the nonvanishing opens and the
ratios are keyed on; `Stacks.SectionProduct.isInvertibleModule_tensorObj` is the instance at that
spelling, obtained from `Stacks.SheafOfModules.isInvertible_tensorSheaf` through the comparison
of the two invertibility classes.

The pullback statements are read off the canonicality clause
`Stacks.RingedSpace.comparisonBifunctorIso_hom_homEquiv_unit_tmul` of Tag 01CD by unfolding the
adjoint transpose.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

namespace TensorProduct

section Ideal

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- If `m ∈ I M` for an ideal `I`, then `m ⊗ n ∈ I (M ⊗_R N)`. -/
theorem tmul_mem_ideal_smul_top_of_left (I : Ideal R) {m : M} (n : N)
    (hm : m ∈ I • (⊤ : Submodule R M)) : m ⊗ₜ[R] n ∈ I • (⊤ : Submodule R (M ⊗[R] N)) := by
  refine Submodule.smul_induction_on hm (fun r hr z _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [TensorProduct.add_tmul]
    exact add_mem hx hy

/-- If `n ∈ I N` for an ideal `I`, then `m ⊗ n ∈ I (M ⊗_R N)`. -/
theorem tmul_mem_ideal_smul_top_of_right (I : Ideal R) (m : M) {n : N}
    (hn : n ∈ I • (⊤ : Submodule R N)) : m ⊗ₜ[R] n ∈ I • (⊤ : Submodule R (M ⊗[R] N)) := by
  refine Submodule.smul_induction_on hn (fun r hr z _ => ?_) (fun x y hx hy => ?_)
  · rw [TensorProduct.tmul_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [TensorProduct.tmul_add]
    exact add_mem hx hy

end Ideal

section Local

variable {R M N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Over a local ring `R` with maximal ideal `𝔪`, an element of `M` outside `𝔪 M` has nonzero
image under some `R`-linear map `M → R ⧸ 𝔪`. -/
theorem exists_linearMap_residue_ne_zero {m : M}
    (hm : m ∉ maximalIdeal R • (⊤ : Submodule R M)) :
    ∃ φ : M →ₗ[R] R ⧸ maximalIdeal R, φ m ≠ 0 := by
  set P : Submodule R M := maximalIdeal R • ⊤
  have hq : P.mkQ m ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual (R ⧸ maximalIdeal R) (M ⧸ P), ψ (P.mkQ m) ≠ 0 := by
    by_contra h
    exact hq ((Module.forall_dual_apply_eq_zero_iff _ _).mp
      fun ψ => not_not.mp fun h' => h ⟨ψ, h'⟩)
  exact ⟨ψ.restrictScalars R ∘ₗ P.mkQ, hψ⟩

/-- **A pure tensor of two elements that do not vanish modulo `𝔪` does not vanish modulo `𝔪`.**
Over a local ring `R` with maximal ideal `𝔪`, if `m ∉ 𝔪 M` and `n ∉ 𝔪 N` then
`m ⊗ n ∉ 𝔪 (M ⊗_R N)`. -/
theorem tmul_notMem_maximalIdeal_smul_top {m : M} {n : N}
    (hm : m ∉ maximalIdeal R • (⊤ : Submodule R M))
    (hn : n ∉ maximalIdeal R • (⊤ : Submodule R N)) :
    m ⊗ₜ[R] n ∉ maximalIdeal R • (⊤ : Submodule R (M ⊗[R] N)) := by
  obtain ⟨φ, hφ⟩ := exists_linearMap_residue_ne_zero hm
  obtain ⟨ψ, hψ⟩ := exists_linearMap_residue_ne_zero hn
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let Φ : M ⊗[R] N →ₗ[R] R ⧸ maximalIdeal R :=
    TensorProduct.lift ((LinearMap.mul R (R ⧸ maximalIdeal R)).compl₁₂ φ ψ)
  intro h
  have hzero : ∀ z ∈ maximalIdeal R • (⊤ : Submodule R (M ⊗[R] N)), Φ z = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun r hr z _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, _root_.Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
    · rw [map_add, hx, hy, add_zero]
  refine mul_ne_zero hφ hψ ?_
  simpa only [Φ, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] using
    hzero _ h

end Local

end TensorProduct

namespace Stacks.SectionProduct

open Stacks.ModuleStalk

variable {X : Scheme.{u}} (M N : X.Modules)

/-- **The germ of a product of sections is the pure tensor of the germs**, under the
identification `(M ⊗ N)_x ≅ M_x ⊗_{𝒪_{X,x}} N_x` of [Stacks, Tag 01CB]. -/
theorem tensorStalkEquiv_germ_tensorSectionsAt (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    tensorStalkEquiv M N x ((Scheme.Modules.tensorObj M N).presheaf.germ U x hx
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          M N s t)) =
      M.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx t :=
  tensorStalkEquiv_germ M N x U hx s t

/-- **`X_{s ⊗ t} = X_s ∩ X_t`.** For global sections `s` of `M` and `t` of `N` on any scheme, the
section `s ⊗ t` of `M ⊗_{𝒪_X} N` does not vanish at `x` exactly when neither `s` nor `t` does. -/
theorem nonvanishingLocus_tensorSectionsAt (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    Stacks.Ample.nonvanishingLocus (Scheme.Modules.tensorObj M N)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
          M N s t) =
      Stacks.Ample.nonvanishingLocus M s ∩ Stacks.Ample.nonvanishingLocus N t := by
  ext x
  have he := Stacks.NonvanishingPullback.mem_ideal_smul_top_iff_of_linearEquiv
    (maximalIdeal (X.presheaf.stalk x)) (tensorStalkEquiv M N x)
    ((Scheme.Modules.tensorObj M N).presheaf.germ ⊤ x trivial
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
        M N s t))
  rw [tensorStalkEquiv_germ_tensorSectionsAt M N x ⊤ trivial s t] at he
  change ¬ _ ↔ ¬ _ ∧ ¬ _
  refine (not_congr he).trans ⟨fun h => ⟨fun hs => h ?_, fun ht => h ?_⟩, fun ⟨hs, ht⟩ => ?_⟩
  · exact TensorProduct.tmul_mem_ideal_smul_top_of_left _ _ hs
  · exact TensorProduct.tmul_mem_ideal_smul_top_of_right _ _ ht
  · exact TensorProduct.tmul_notMem_maximalIdeal_smul_top hs ht

/-- **The product of sections is bilinear over `𝒪_X`**: `(a s) ⊗ (b t) = (a b) (s ⊗ t)`. -/
theorem tensorSectionsAt_smul_smul {U : X.Opens} (a b : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U) M N
        (a • s) (b • t) =
      (a * b) • (show Γ(Scheme.Modules.tensorObj M N, U) from
        Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          M N s t) := by
  unfold Stacks.SheafOfModules.tensorSectionsAt
  exact (congrArg _ (TensorProduct.smul_tmul_smul a b s t)).trans
    (LinearMap.map_smul (PresheafOfModules.Hom.app
      (Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj X.ringCatSheaf.property
        _) (op U)).hom (a * b) _)

/-- **The product of sections commutes with restriction.** -/
theorem map_tensorSectionsAt {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    (Scheme.Modules.tensorObj M N).presheaf.map i.op
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          M N s t) =
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op V) M N
        (M.presheaf.map i.op s) (N.presheaf.map i.op t) := by
  unfold Stacks.SheafOfModules.tensorSectionsAt
  exact (PresheafOfModules.naturality_apply (Stacks.SheafOfModules.TensorSheafification.toSheafify
    X.sheaf.obj X.ringCatSheaf.property (PresheafOfModules.tensorObj M.val N.val)) i.op _).symm

/-! ### Pullback -/

section Pullback

variable {Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The product of sections commutes with pullback.** For a morphism of schemes `f : Y ⟶ X`
and sections `s` of `M` and `t` of `N` over an open `U` of `X`, the canonical isomorphism
`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` of [Stacks, Tag 01CD] carries the pullback of `s ⊗ t` to
`f^*s ⊗ f^*t` over `f⁻¹U`. -/
theorem comparison_pullbackUnit_tensorSectionsAt (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    ((Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).hom.app (M, N)).val.app
        (op (f ⁻¹ᵁ U))
      (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (Scheme.Modules.tensorObj M N) (op U)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          M N s t)) =
      Stacks.SheafOfModules.tensorSectionsAt Y.sheaf.obj Y.ringCatSheaf.property
        (op (f ⁻¹ᵁ U)) ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom M (op U) s)
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom N (op U) t) := by
  have e := congrArg (fun ψ => ψ.val.app (op U)
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        M N s t))
    ((Stacks.RingedSpace.pullbackAdjunction f.toLRSHom.toShHom).homEquiv_unit
      (Scheme.Modules.tensorObj M N)
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N))
      ((Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).hom.app (M, N)))
  exact e.symm.trans (Stacks.RingedSpace.comparisonBifunctorIso_hom_homEquiv_unit_tmul
    f.toLRSHom.toShHom M N (op U) s t)

/-- **The product of global sections commutes with pullback**: the isomorphism
`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` of [Stacks, Tag 01CD] carries `f^*(s ⊗ t)` to `f^*s ⊗ f^*t`. -/
theorem comparison_pullbackGlobalSection_tensorSectionsAt (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    ((Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).hom.app (M, N)).val.app
        (op ⊤)
      (Stacks.NonvanishingPullback.pullbackGlobalSection f (Scheme.Modules.tensorObj M N)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
          M N s t)) =
      Stacks.SheafOfModules.tensorSectionsAt Y.sheaf.obj Y.ringCatSheaf.property (op ⊤)
        ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
        (Stacks.NonvanishingPullback.pullbackGlobalSection f M s)
        (Stacks.NonvanishingPullback.pullbackGlobalSection f N t) :=
  comparison_pullbackUnit_tensorSectionsAt M N f ⊤ s t

end Pullback

/-! ### Invertible modules -/

section Invertible

open Stacks.ProjectiveFromSections

/-- **The tensor product of two invertible `𝒪_X`-modules is invertible** ([Stacks, Tag 01CT]),
at the spelling `Stacks.Ample.IsInvertibleModule` of invertibility that the nonvanishing opens
and the ratios of sections are keyed on. -/
instance isInvertibleModule_tensorObj [hM : Stacks.Ample.IsInvertibleModule X M]
    [hN : Stacks.Ample.IsInvertibleModule X N] :
    Stacks.Ample.IsInvertibleModule X (Scheme.Modules.tensorObj M N) :=
  haveI := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry X.presheaf _ M hM
  haveI := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry X.presheaf _ N hN
  (Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf _ M N).toAlgebraicGeometry

/-- Restricting a product of global sections to `W` gives the product of the restrictions. -/
private theorem resT_tensorSectionsAt (W : X.Opens) (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    resT (L := Scheme.Modules.tensorObj M N) W
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
          M N s t) =
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op W)
        M N (resT W s) (resT W t) :=
  map_tensorSectionsAt M N (homOfLE le_top) s t

variable [Stacks.Ample.IsInvertibleModule X M] [Stacks.Ample.IsInvertibleModule X N]

/-- **`X_{s ⊗ t} = X_s ∩ X_t`**, as an equality of open subschemes. -/
theorem nvOpen_tensorSectionsAt (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    nvOpen (Scheme.Modules.tensorObj M N)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
          M N s t) =
      nvOpen M s ⊓ nvOpen N t :=
  Opens.ext (nonvanishingLocus_tensorSectionsAt M N s t)

/-- **Ratios multiply.** On an open `W` on which the global sections `s` of `M` and `t` of `N`
do not vanish, the ratio of `m ⊗ n` by `s ⊗ t` is the product of the ratios `m / s` and
`n / t`. -/
theorem div_tensorSectionsAt (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) {W : X.Opens}
    (hs : W ≤ nvOpen M s) (ht : W ≤ nvOpen N t) (m : Γ(M, W)) (n : Γ(N, W)) :
    div (L := Scheme.Modules.tensorObj M N)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
          M N s t)
        ((le_inf hs ht).trans (nvOpen_tensorSectionsAt M N s t).ge)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op W)
          M N m n) =
      div s hs m * div t ht n := by
  refine (eq_div _ _ ?_).symm
  change _ • (Scheme.Modules.tensorObj M N).presheaf.map (homOfLE le_top).op _ = _
  rw [map_tensorSectionsAt, ← tensorSectionsAt_smul_smul]
  exact congrArg₂ _ (div_smul s hs m) (div_smul t ht n)

/-- **Cross-multiplication.** If `s' ⊗ t = s ⊗ t'` for global sections `s, s'` of `M` and
`t, t'` of `N`, then `s' / s = t' / t` on every open on which `s` and `t` do not vanish. -/
theorem div_eq_div_of_tensorSectionsAt_eq {s s' : Γ(M, ⊤)} {t t' : Γ(N, ⊤)}
    (h : Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
        M N s' t =
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
        M N s t')
    {W : X.Opens} (hs : W ≤ nvOpen M s) (ht : W ≤ nvOpen N t) :
    div s hs (resT W s') = div t ht (resT W t') := by
  have hW : W ≤ nvOpen (Scheme.Modules.tensorObj M N)
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
        M N s t) :=
    (le_inf hs ht).trans (nvOpen_tensorSectionsAt M N s t).ge
  have key := congrArg (fun z => div (L := Scheme.Modules.tensorObj M N) _ hW (resT W z)) h
  rw [resT_tensorSectionsAt, resT_tensorSectionsAt, div_tensorSectionsAt M N s t hs ht,
    div_tensorSectionsAt M N s t hs ht,
    ← eq_div t ht (one_smul _ (resT W t)), ← eq_div s hs (one_smul _ (resT W s)), mul_one,
    one_mul] at key
  exact key

/-- **The ratios of a family of products are the products of the ratios.** For families `sⱼ` of
global sections of `M` and `tⱼ` of `N`, on the nonvanishing open of `sᵢ ⊗ tᵢ` the ratio
`(sₖ ⊗ tₖ) / (sᵢ ⊗ tᵢ)` is `(sₖ / sᵢ) · (tₖ / tᵢ)`. -/
theorem ratio_tensorSectionsAt {ι : Type*} (s : ι → Γ(M, ⊤)) (t : ι → Γ(N, ⊤)) (i k : ι) :
    ratio (L := Scheme.Modules.tensorObj M N)
        (fun j => Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
          (op ⊤) M N (s j) (t j)) i k =
      resO ((nvOpen_tensorSectionsAt M N (s i) (t i)).le.trans inf_le_left) (ratio s i k) *
        resO ((nvOpen_tensorSectionsAt M N (s i) (t i)).le.trans inf_le_right) (ratio t i k) := by
  set W := nvOpen (Scheme.Modules.tensorObj M N)
    (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤) M N
      (s i) (t i))
  have hs : W ≤ nvCover s i := (nvOpen_tensorSectionsAt M N (s i) (t i)).le.trans inf_le_left
  have ht : W ≤ nvCover t i := (nvOpen_tensorSectionsAt M N (s i) (t i)).le.trans inf_le_right
  have hsk : div (s i) hs (resT W (s k)) = resO hs (ratio s i k) :=
    (eq_div (s i) hs (resO_ratio_smul s hs k)).symm
  have htk : div (t i) ht (resT W (t k)) = resO ht (ratio t i k) :=
    (eq_div (t i) ht (resO_ratio_smul t ht k)).symm
  refine Eq.trans ?_ ((div_tensorSectionsAt M N (s i) (t i) hs ht _ _).trans
    (congrArg₂ (· * ·) hsk htk))
  exact congrArg (div (L := Scheme.Modules.tensorObj M N) _ le_rfl) (resT_tensorSectionsAt ..)

end Invertible

end Stacks.SectionProduct
