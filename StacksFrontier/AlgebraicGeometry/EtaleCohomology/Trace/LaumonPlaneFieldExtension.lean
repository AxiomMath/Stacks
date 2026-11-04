module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilySheaf
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The `(x, t)`-plane over a finite extension of the constants

For a field extension `k → k'`, the plane `Spec k'[x][t]` is the base change of `Spec k[x][t]`
along the `t`-line `Spec k'[t] → Spec k[t]`: the square

```
Spec k'[x][t] ──π──▶ Spec k[x][t]
     │pr₂                 │pr₂
     ▼                    ▼
Spec k'[t]   ──π──▶ Spec k[t]
```

is cartesian (`isPullback_laumonPlaneFieldExtension`), since `k'[x][t] = k[x][t] ⊗_{k[t]} k'[t]`
(`isPushout_laumonPlaneFieldExtension`). The preimage of `D(D₀)` is `D(D₀ ⊗ k')`, and the plane and
line over `k` are below the cutoff of the site as soon as those over `k'` are. These are the base
changes of the constant field extension used to make the lisse locus of Laumon's Fourier family
uniform in `k'` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). All names are in the
namespace `Stacks.EtaleCohomology`.

## Main results

* `isPushout_laumonPlaneFieldExtension`: `k'[x][t]` is the pushout of `k[x][t] ← k[t] → k'[t]`.
* `isPullback_laumonPlaneFieldExtension`: the plane over `k'` is the base change of the plane
  over `k` along the `t`-line.
* `range_comp_laumonLineFieldExtension_subset`: the `t`-line over `k'` maps `D(D₀ ⊗ k')` into
  `D(D₀)`.
* `schemeSizeBelow_laumonPlane_of_fieldExtension`: the plane over `k` is below the cutoff when the
  plane over `k'` is.
* `schemeSizeBelow_laumonLine_of_laumonPlane`: the line over `k` is below the cutoff when the plane
  over `k` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Stacks.EtaleCohomology

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

/-- **`k'[x][t]` is the pushout of `k[x][t] ← k[t] → k'[t]`**: a pair of ring maps from
`k[x][t]` and `k'[t]` agreeing on `k[t]` extends uniquely to `k'[x][t]`, by evaluating the
coefficients of `k'` through `k'[t]`, `x` at the image of `x` and `t` at the image of `t`. -/
public theorem isPushout_laumonPlaneFieldExtension :
    IsPushout (CommRingCat.ofHom (mapRingHom (algebraMap k (Polynomial k))))
      (CommRingCat.ofHom (mapRingHom (algebraMap k k')))
      (CommRingCat.ofHom (mapRingHom (mapRingHom (algebraMap k k'))))
      (CommRingCat.ofHom (mapRingHom (algebraMap k' (Polynomial k')))) := by
  have hw : CommRingCat.ofHom (mapRingHom (algebraMap k (Polynomial k))) ≫
      CommRingCat.ofHom (mapRingHom (mapRingHom (algebraMap k k'))) =
      CommRingCat.ofHom (mapRingHom (algebraMap k k')) ≫
        CommRingCat.ofHom (mapRingHom (algebraMap k' (Polynomial k'))) := by
    ext : 1
    refine Polynomial.ringHom_ext (fun c => ?_) ?_ <;> simp
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw) ?_
  have hcond : ∀ s : PushoutCocone (CommRingCat.ofHom (mapRingHom (algebraMap k (Polynomial k))))
      (CommRingCat.ofHom (mapRingHom (algebraMap k k'))), ∀ q : Polynomial k,
      s.inl.hom (q.map (algebraMap k (Polynomial k))) = s.inr.hom (q.map (algebraMap k k')) :=
    fun s q => congrArg (fun φ => φ.hom q) s.condition
  let inner : ∀ s : PushoutCocone (CommRingCat.ofHom (mapRingHom (algebraMap k (Polynomial k))))
      (CommRingCat.ofHom (mapRingHom (algebraMap k k'))), Polynomial k' →+* s.pt := fun s =>
    eval₂RingHom (s.inr.hom.comp Polynomial.C) (s.inl.hom (Polynomial.C Polynomial.X))
  refine PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (eval₂RingHom (inner s) (s.inr.hom Polynomial.X)))
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)
  · ext : 1
    refine Polynomial.ringHom_ext (fun q => ?_) ?_
    · refine RingHom.congr_fun (Polynomial.ringHom_ext (f := ((CommRingCat.ofHom
        (mapRingHom (mapRingHom (algebraMap k k'))) ≫ CommRingCat.ofHom (eval₂RingHom (inner s)
          (s.inr.hom Polynomial.X))).hom.comp Polynomial.C))
        (g := s.inl.hom.comp Polynomial.C) (fun c => ?_) ?_) q
      · have := hcond s (Polynomial.C c)
        simp only [Polynomial.map_C, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply] at this
        simp [inner, this]
      · simp [inner]
    · have := hcond s Polynomial.X
      simp only [Polynomial.map_X] at this
      simp [this]
  · ext : 1
    refine Polynomial.ringHom_ext (fun q => ?_) ?_ <;> simp [inner]
  · ext : 1
    refine Polynomial.ringHom_ext (fun q => ?_) ?_
    · refine RingHom.congr_fun (Polynomial.ringHom_ext (f := m.hom.comp Polynomial.C)
        (g := (eval₂RingHom (inner s) (s.inr.hom Polynomial.X)).comp Polynomial.C)
        (fun c => ?_) ?_) q
      · have := congrArg (fun φ => φ.hom (Polynomial.C c)) h₂
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply, coe_mapRingHom, Polynomial.map_C, Polynomial.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] at this
        simp [inner, this]
      · have := congrArg (fun φ => φ.hom (Polynomial.C Polynomial.X)) h₁
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply, coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at this
        simp [inner, this]
    · have := congrArg (fun φ => φ.hom Polynomial.X) h₂
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, coe_mapRingHom, Polynomial.map_X] at this
      simp [this]

/-- **The plane over `k'` is the base change of the plane over `k` along the `t`-line.** -/
public theorem isPullback_laumonPlaneFieldExtension :
    IsPullback (Spec.map (CommRingCat.ofHom (mapRingHom (mapRingHom (algebraMap k k')))))
      (laumonFamilyPr₂ k') (laumonFamilyPr₂ k)
      (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k')))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_laumonPlaneFieldExtension k k')

/-- **The preimage of `D(D₀)` under the `t`-line over `k'`**: if a morphism `j` to `Spec k'[t]`
lands in `D(D₀ ⊗ k')`, then `j` followed by `Spec k'[t] → Spec k[t]` lands in `D(D₀)`. -/
public theorem range_comp_laumonLineFieldExtension_subset {X : Scheme.{u}}
    (j : X ⟶ Spec (.of (Polynomial k'))) (D₀ : Polynomial k)
    (h : Set.range j ⊆ (PrimeSpectrum.basicOpen (D₀.map (algebraMap k k')) :
      Set (PrimeSpectrum (Polynomial k')))) :
    Set.range (j ≫ Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k')))) ⊆
      (PrimeSpectrum.basicOpen D₀ : Set (PrimeSpectrum (Polynomial k))) := by
  rintro _ ⟨y, rfl⟩
  exact h ⟨y, rfl⟩

/-- A ring injecting into a ring whose spectrum is below the cutoff has its spectrum below it. -/
private theorem schemeSizeBelow_spec_of_injective {κ : Cardinal.{u}} {R S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    (hS : schemeSizeBelow κ (Spec (.of S))) : schemeSizeBelow κ (Spec (.of R)) := by
  change (Spec (.of R)).size < κ
  change (Spec (.of S)).size < κ at hS
  rw [Scheme.size_Spec] at hS ⊢
  exact lt_of_le_of_lt (max_le_max le_rfl (Cardinal.mk_le_of_injective hf)) hS

/-- **The plane over `k` is below the cutoff when the plane over `k'` is**: `k[x][t]` injects
into `k'[x][t]`. -/
public theorem schemeSizeBelow_laumonPlane_of_fieldExtension {κ : Cardinal.{u}}
    (hS : schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial k'))))) :
    schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial k)))) :=
  schemeSizeBelow_spec_of_injective (mapRingHom (mapRingHom (algebraMap k k')))
    (Polynomial.map_injective _ (Polynomial.map_injective _ (algebraMap k k').injective)) hS

/-- **The line over `k` is below the cutoff when the plane over `k` is.** -/
public theorem schemeSizeBelow_laumonLine_of_laumonPlane {κ : Cardinal.{u}}
    (hS : schemeSizeBelow κ (Spec (.of (Polynomial (Polynomial k))))) :
    schemeSizeBelow κ (Spec (.of (Polynomial k))) :=
  schemeSizeBelow_spec_of_injective (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k))
    Polynomial.C_injective hS

end Stacks.EtaleCohomology
