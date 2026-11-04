module

public import StacksFrontier.RingTheory.Cech.Shrink

/-!
# Functoriality of the small model of the extended alternating Čech complex

`StacksFrontier/RingTheory/Cech/Shrink.lean` builds `Cech.cechComplexShrink`, the extended
alternating Čech complex of a module `M` in a module universe `v` independent of the ring
universe `u`, for each `M` separately. This file makes it a functor of `M`.

Two steps are involved, and the first is of independent use. The maps
`M_{∏ i ∈ s, f i} ⟶ N_{∏ i ∈ s, f i}` induced on the Čech localizations by an `R`-linear map
`M →ₗ[R] N` are available with the universes of `M` and `N` independent of each other and of the
ring universe — `Cech.cechModMap` below — because `IsLocalizedModule.map` is
universe-heterogeneous; `Stacks.LocalCohomology.cechModMap` and
`Stacks.LocalCohomology.cechTermMap` are the special case `M, N : ModuleCat.{max u v} R`, with
which they agree definitionally. The second step conjugates those maps by
`Cech.cechTermShrinkEquiv`, exactly as `Cech.cechDShrink` conjugates the differential, so every
compatibility is inherited from the unshrunk complex rather than reproved.

## Main definitions

* `Cech.cechModMap`, `Cech.cechTermMap` — the induced maps on the Čech localizations and on the
  terms of the complex, in free universes.
* `Cech.cechTermShrinkMap`, `Cech.cechComplexShrinkMap` — the induced maps on the small model.
* `Cech.cechFunctorShrink`, `Cech.extendedCechFunctorShrink` — **the small model of the extended
  alternating Čech complex as a functor of the module**, in natural and in integer degrees.

## Main results

* `Cech.cechTermMap_comp_cechD` — the induced maps commute with the alternating differential.
* `Cech.cechTermShrinkMap_comp_cechDShrink` — the same for the small model.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w w' w'' u

namespace Cech

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-! ### The induced maps on the localizations, in free universes -/

section Plain

variable {M : Type w} {N : Type w'} {P : Type w''} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The map `M_{∏ i ∈ s, f i} ⟶ N_{∏ i ∈ s, f i}` induced on the Čech localizations by an
`R`-linear map, with the universes of `M` and `N` independent of each other and of the ring
universe. -/
def cechModMap (g : M →ₗ[R] N) (s : Finset (Fin r)) :
    cechMod f M s →ₗ[R] cechMod f N s :=
  IsLocalizedModule.map (cechSub f s)
    (LocalizedModule.mkLinearMap (cechSub f s) M)
    (LocalizedModule.mkLinearMap (cechSub f s) N) g

/-- The induced map on a localization is determined by its values on the image of `M`. -/
@[simp] theorem cechModMap_comp_mk (g : M →ₗ[R] N) (s : Finset (Fin r)) :
    (cechModMap f g s).comp (LocalizedModule.mkLinearMap (cechSub f s) M) =
      (LocalizedModule.mkLinearMap (cechSub f s) N).comp g :=
  IsLocalizedModule.map_comp _ _ _ _

/-- The induced map sends `m/1` to `g m / 1`. -/
theorem cechModMap_mkLinearMap (g : M →ₗ[R] N) (s : Finset (Fin r)) (m : M) :
    cechModMap f g s (LocalizedModule.mkLinearMap (cechSub f s) M m) =
      LocalizedModule.mkLinearMap (cechSub f s) N (g m) :=
  LinearMap.congr_fun (cechModMap_comp_mk f g s) m

/-- The induced map sends `m/a` to `g m / a`. -/
theorem cechModMap_mk (g : M →ₗ[R] N) (s : Finset (Fin r)) (m : M) (a : cechSub f s) :
    cechModMap f g s (LocalizedModule.mk m a) = LocalizedModule.mk (g m) a :=
  IsLocalizedModule.map_LocalizedModules _ _ _ _

/-- The identity induces the identity on the localizations. -/
@[simp] theorem cechModMap_id (s : Finset (Fin r)) :
    cechModMap f (LinearMap.id (R := R) (M := M)) s = LinearMap.id :=
  IsLocalizedModule.map_id _ _

/-- A composite of linear maps induces the composite on the localizations. -/
theorem cechModMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) (s : Finset (Fin r)) :
    cechModMap f (h.comp g) s = (cechModMap f h s).comp (cechModMap f g s) := by
  refine IsLocalizedModule.ext (cechSub f s)
    (LocalizedModule.mkLinearMap (cechSub f s) M)
    (isUnit_algebraMap f P (le_refl s)
      (LocalizedModule.mkLinearMap (cechSub f s) P)) (LinearMap.ext fun m => ?_)
  simp only [LinearMap.comp_apply, cechModMap_mkLinearMap]

/-- The induced maps commute with the transition maps `M_{∏ i ∈ s} ⟶ M_{∏ i ∈ t}` of the
complex: both composites are determined by their values on the images of `M`. -/
theorem cechι_comp_cechModMap (g : M →ₗ[R] N) {s t : Finset (Fin r)} (hst : s ⊆ t) :
    (cechι f N hst).comp (cechModMap f g s) =
      (cechModMap f g t).comp (cechι f M hst) := by
  refine IsLocalizedModule.ext (cechSub f s)
    (LocalizedModule.mkLinearMap (cechSub f s) M)
    (isUnit_algebraMap f N hst (LocalizedModule.mkLinearMap (cechSub f t) N)) ?_
  rw [LinearMap.comp_assoc, cechModMap_comp_mk, ← LinearMap.comp_assoc, cechι_comp_mk,
    LinearMap.comp_assoc, cechι_comp_mk, cechModMap_comp_mk]

/-- The elementwise form of the commutation with the transition maps. -/
theorem cechι_cechModMap (g : M →ₗ[R] N) {s t : Finset (Fin r)} (hst : s ⊆ t)
    (x : cechMod f M s) :
    cechι f N hst (cechModMap f g s x) = cechModMap f g t (cechι f M hst x) :=
  LinearMap.congr_fun (cechι_comp_cechModMap f g hst) x

/-! ### The induced maps on the terms of the complex, in free universes -/

/-- The map induced by `g` on the degree-`p` term of the extended alternating Čech complex: `g`
acts on each localized summand. -/
def cechTermMap (g : M →ₗ[R] N) (p : ℕ) : cechTerm f M p →ₗ[R] cechTerm f N p :=
  DirectSum.toModule R _ _ fun s =>
    (DirectSum.lof R {t : Finset (Fin r) // t.card = p}
      (fun t => cechMod f N t.1) s).comp (cechModMap f g s.1)

/-- On the summand indexed by `s`, the induced map is the one on that localization. -/
@[simp] theorem cechTermMap_lof (g : M →ₗ[R] N) (p : ℕ)
    (s : {s : Finset (Fin r) // s.card = p}) (x : cechMod f M s.1) :
    cechTermMap f g p (DirectSum.lof R _ (fun t => cechMod f M t.1) s x) =
      DirectSum.lof R _ (fun t => cechMod f N t.1) s (cechModMap f g s.1 x) := by
  rw [cechTermMap, DirectSum.toModule_lof]
  rfl

/-- The induced maps commute with the alternating differential: on the summand indexed by `s`
both composites are the sum over the new indices of the transition map followed by `g`. -/
theorem cechTermMap_comp_cechD (g : M →ₗ[R] N) (p : ℕ) :
    (cechD f N p).comp (cechTermMap f g p) =
      (cechTermMap f g (p + 1)).comp (cechD f M p) := by
  refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, cechTermMap_lof, cechD_lof, map_sum, map_zsmul,
    cechι_cechModMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cechTermMap_lof]

/-- The identity induces the identity on the terms of the complex. -/
@[simp] theorem cechTermMap_id (p : ℕ) :
    cechTermMap f (LinearMap.id (R := R) (M := M)) p = LinearMap.id := by
  refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cechTermMap_lof, cechModMap_id]
  rfl

/-- A composite induces the composite on the terms of the complex. -/
theorem cechTermMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) (p : ℕ) :
    cechTermMap f (h.comp g) p = (cechTermMap f h p).comp (cechTermMap f g p) := by
  refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cechTermMap_lof, LinearMap.comp_apply, LinearMap.comp_apply,
    cechTermMap_lof, cechTermMap_lof, cechModMap_comp f g h s.1]
  rfl

end Plain

/-! ### The induced maps on the small model -/

section Shrunk

variable {M : Type w} {N : Type w'} {P : Type w''} [AddCommGroup M] [Module R M] [Small.{v} M]
  [AddCommGroup N] [Module R N] [Small.{v} N] [AddCommGroup P] [Module R P] [Small.{v} P]

/-- The map induced by `g` on the degree-`p` term of the small model: the map on the terms of
`Cech.cechComplex`, conjugated by `Cech.cechTermShrinkEquiv`, exactly as `Cech.cechDShrink`
conjugates the differential. -/
def cechTermShrinkMap (g : M →ₗ[R] N) (p : ℕ) :
    cechTermShrink.{v} f M p →ₗ[R] cechTermShrink.{v} f N p :=
  (cechTermShrinkEquiv.{v} f N p).symm.toLinearMap ∘ₗ cechTermMap f g p ∘ₗ
    (cechTermShrinkEquiv.{v} f M p).toLinearMap

/-- The comparison with `Cech.cechTerm` carries the induced map of small models to the induced
map of terms. -/
theorem cechTermShrinkEquiv_cechTermShrinkMap (g : M →ₗ[R] N) (p : ℕ)
    (x : cechTermShrink.{v} f M p) :
    cechTermShrinkEquiv.{v} f N p (cechTermShrinkMap.{v} f g p x) =
      cechTermMap f g p (cechTermShrinkEquiv.{v} f M p x) := by
  simp [cechTermShrinkMap]

/-- The induced maps of small models commute with the differentials of the small models. -/
theorem cechTermShrinkMap_comp_cechDShrink (g : M →ₗ[R] N) (p : ℕ) :
    (cechDShrink.{v} f N p).comp (cechTermShrinkMap.{v} f g p) =
      (cechTermShrinkMap.{v} f g (p + 1)).comp (cechDShrink.{v} f M p) := by
  refine LinearMap.ext fun x => (cechTermShrinkEquiv.{v} f N (p + 1)).injective ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, cechTermShrinkEquiv_cechDShrink,
    cechTermShrinkEquiv_cechTermShrinkMap, cechTermShrinkEquiv_cechTermShrinkMap,
    cechTermShrinkEquiv_cechDShrink, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    cechTermMap_comp_cechD]

/-- The identity induces the identity on the terms of the small model. -/
@[simp] theorem cechTermShrinkMap_id (p : ℕ) :
    cechTermShrinkMap.{v} f (LinearMap.id (R := R) (M := M)) p = LinearMap.id := by
  refine LinearMap.ext fun x => (cechTermShrinkEquiv.{v} f M p).injective ?_
  rw [cechTermShrinkEquiv_cechTermShrinkMap, cechTermMap_id, LinearMap.id_apply,
    LinearMap.id_apply]

/-- A composite induces the composite on the terms of the small model. -/
theorem cechTermShrinkMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) (p : ℕ) :
    cechTermShrinkMap.{v} f (h.comp g) p =
      (cechTermShrinkMap.{v} f h p).comp (cechTermShrinkMap.{v} f g p) := by
  refine LinearMap.ext fun x => (cechTermShrinkEquiv.{v} f P p).injective ?_
  rw [cechTermShrinkEquiv_cechTermShrinkMap, LinearMap.comp_apply,
    cechTermShrinkEquiv_cechTermShrinkMap, cechTermShrinkEquiv_cechTermShrinkMap,
    cechTermMap_comp, LinearMap.comp_apply]

end Shrunk

/-! ### The small model as a functor -/

section Functor

variable {M N P : ModuleCat.{v} R}

/-- The map of small models of the extended alternating Čech complex induced by a module map. -/
def cechComplexShrinkMap (g : M ⟶ N) :
    cechComplexShrink.{v} f (M : Type v) ⟶ cechComplexShrink.{v} f (N : Type v) where
  f p := ModuleCat.ofHom (cechTermShrinkMap.{v} f g.hom p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    rw [cechComplexShrink_d, cechComplexShrink_d]
    exact ModuleCat.hom_ext (cechTermShrinkMap_comp_cechDShrink.{v} f g.hom p)

/-- The degree-`p` component of the induced map of small models. -/
@[simp] theorem cechComplexShrinkMap_f (g : M ⟶ N) (p : ℕ) :
    (cechComplexShrinkMap.{v} f g).f p = ModuleCat.ofHom (cechTermShrinkMap.{v} f g.hom p) :=
  rfl

/-- **The small model of the extended alternating Čech complex as a functor of the module**, in
natural degrees: a functor from `ModuleCat.{v} R` to `ℕ`-indexed cochain complexes of
`ModuleCat.{v} R`, with the module universe `v` independent of the ring universe. -/
def cechFunctorShrink : ModuleCat.{v} R ⥤ CochainComplex (ModuleCat.{v} R) ℕ where
  obj M := cechComplexShrink.{v} f (M : Type v)
  map g := cechComplexShrinkMap.{v} f g
  map_id M := HomologicalComplex.hom_ext _ _ fun p => by
    rw [cechComplexShrinkMap_f, HomologicalComplex.id_f]
    exact congrArg ModuleCat.ofHom (cechTermShrinkMap_id.{v} f p)
  map_comp {M N P} g h := HomologicalComplex.hom_ext _ _ fun p => by
    rw [cechComplexShrinkMap_f, HomologicalComplex.comp_f, cechComplexShrinkMap_f,
      cechComplexShrinkMap_f]
    exact congrArg ModuleCat.ofHom (cechTermShrinkMap_comp.{v} f g.hom h.hom p)

/-- The functor at a module is the small model of that module's Čech complex. -/
@[simp] theorem cechFunctorShrink_obj :
    (cechFunctorShrink.{v} f).obj M = cechComplexShrink.{v} f (M : Type v) := rfl

/-- The functor on a module map is the induced map of small models. -/
@[simp] theorem cechFunctorShrink_map (g : M ⟶ N) :
    (cechFunctorShrink.{v} f).map g = cechComplexShrinkMap.{v} f g := rfl

/-- The map of integer-indexed small models induced by a module map. -/
def extendedCechComplexShrinkMap (g : M ⟶ N) :
    extendedCechComplexShrink.{v} f (M : Type v) ⟶ extendedCechComplexShrink.{v} f (N : Type v) :=
  HomologicalComplex.extendMap (cechComplexShrinkMap.{v} f g) ComplexShape.embeddingUpNat

/-- **The small model of the extended alternating Čech complex as a functor of the module**, in
integer degrees. -/
def extendedCechFunctorShrink : ModuleCat.{v} R ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  cechFunctorShrink.{v} f ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R)

/-- The integer-indexed functor at a module is the integer-indexed small model. -/
@[simp] theorem extendedCechFunctorShrink_obj :
    (extendedCechFunctorShrink.{v} f).obj M = extendedCechComplexShrink.{v} f (M : Type v) :=
  rfl

/-- The integer-indexed functor on a module map is the induced map of small models. -/
@[simp] theorem extendedCechFunctorShrink_map (g : M ⟶ N) :
    (extendedCechFunctorShrink.{v} f).map g = extendedCechComplexShrinkMap.{v} f g := rfl

/-- The identity induces the identity on the integer-indexed small model. -/
@[simp] theorem extendedCechComplexShrinkMap_id :
    extendedCechComplexShrinkMap.{v} f (𝟙 M) =
      𝟙 (extendedCechComplexShrink.{v} f (M : Type v)) :=
  (extendedCechFunctorShrink.{v} f).map_id M

/-- A composite induces the composite on the integer-indexed small model. -/
theorem extendedCechComplexShrinkMap_comp (g : M ⟶ N) (h : N ⟶ P) :
    extendedCechComplexShrinkMap.{v} f (g ≫ h) =
      extendedCechComplexShrinkMap.{v} f g ≫ extendedCechComplexShrinkMap.{v} f h :=
  (extendedCechFunctorShrink.{v} f).map_comp g h

end Functor

end Cech

end
