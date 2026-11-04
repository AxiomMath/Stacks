module

public import StacksFrontier.RingTheory.LocalCohomology.CechModel

/-!
# Functoriality of the extended alternating Čech complex in the module

Let `A` be a commutative ring and `f₁, …, f_r ∈ A`. The extended alternating Čech complex
`C^•(f₁, …, f_r; M)` of `StacksFrontier/RingTheory/Cech/Substrate.lean` is built from the
localizations `M_{f_{i₀} ⋯ f_{i_p}}`, each of which is functorial in `M`, so the complex is a
functor of `M`. This file carries out that construction: a module map `g : M ⟶ N` induces a map
on each localized summand, those assemble into a map of the degree-`p` terms, the maps commute
with the alternating differential, and the result is a functor
`Stacks.LocalCohomology.cechFunctor` from `A`-modules to cochain complexes of `A`-modules.

Functoriality is what the Čech model of local cohomology (Stacks 0A6R) lacks when it is obtained
from the uniqueness of a coreflection: `nonempty_localCohomology_iso_extendedCechObject` produces
an isomorphism `RΓ_{V(I)}(M) ≅ C^•(f₁, …, f_r; M)` for each `M` separately, with no compatibility
between different modules. With the complex available as a functor, the augmentation onto `M` in
degree zero becomes a natural transformation, and the universal property of that augmentation then
*forces* the comparison with local cohomology to be natural — this is carried out in
`StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Comparison.lean`.

## Main definitions

* `Stacks.LocalCohomology.cechModMap` — the map `M_{∏ i ∈ s, f i} ⟶ N_{∏ i ∈ s, f i}` induced by
  a module map.
* `Stacks.LocalCohomology.cechTermMap` — the induced map on the degree-`p` term of the complex.
* `Stacks.LocalCohomology.cechFunctor` — the extended alternating Čech complex as a functor to
  `ℕ`-indexed cochain complexes.
* `Stacks.LocalCohomology.extendedCechComplexMap`,
  `Stacks.LocalCohomology.extendedCechFunctor` — the same map and functor for the `ℤ`-indexed
  cochain complexes.
* `Stacks.LocalCohomology.extendedCechObjectFunctor` — the Čech object of the derived category,
  functorially in the module.

## Main results

* `Stacks.LocalCohomology.cechι_comp_cechModMap` — the induced maps commute with the transition
  maps of the complex.
* `Stacks.LocalCohomology.cechTermMap_comp_cechD` — they commute with the alternating
  differential.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

section Free

variable {M N P : ModuleCat.{v} R}

/-! ### The induced maps on the localized summands

The two modules need only be objects of `ModuleCat.{v} R` for a module universe `v` independent
of the ring universe: the Čech localizations of a module in `Type v` live in `Type (max u v)`
whatever `v` is, and `IsLocalizedModule.map` is universe-heterogeneous. It is the *complex*
`Cech.cechComplex` that forces `max u v` below. -/

/-- The map `M_{∏ i ∈ s, f i} ⟶ N_{∏ i ∈ s, f i}` induced on localizations by a module map. -/
def cechModMap (g : M ⟶ N) (s : Finset (Fin r)) :
    Cech.cechMod f M s →ₗ[R] Cech.cechMod f N s :=
  IsLocalizedModule.map (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) N) g.hom

/-- The induced map on a localization is determined by its values on the image of `M`. -/
@[simp] theorem cechModMap_comp_mk (g : M ⟶ N) (s : Finset (Fin r)) :
    (cechModMap f g s).comp (LocalizedModule.mkLinearMap (Cech.cechSub f s) M) =
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) N).comp g.hom :=
  IsLocalizedModule.map_comp _ _ _ _

/-- The induced map sends `m/1` to `g m / 1`. -/
theorem cechModMap_mkLinearMap (g : M ⟶ N) (s : Finset (Fin r)) (m : M) :
    cechModMap f g s (LocalizedModule.mkLinearMap (Cech.cechSub f s) M m) =
      LocalizedModule.mkLinearMap (Cech.cechSub f s) N (g m) :=
  LinearMap.congr_fun (cechModMap_comp_mk f g s) m

/-- The induced map sends `m/a` to `g m / a`. -/
theorem cechModMap_mk (g : M ⟶ N) (s : Finset (Fin r)) (m : M) (a : Cech.cechSub f s) :
    cechModMap f g s (LocalizedModule.mk m a) = LocalizedModule.mk (g m) a :=
  IsLocalizedModule.map_LocalizedModules _ _ _ _

/-- The identity induces the identity on localizations. -/
@[simp] theorem cechModMap_id (s : Finset (Fin r)) :
    cechModMap f (𝟙 M) s = LinearMap.id :=
  IsLocalizedModule.map_id _ _

/-- A composite of module maps induces the composite on localizations. -/
theorem cechModMap_comp (g : M ⟶ N) (h : N ⟶ P) (s : Finset (Fin r)) :
    cechModMap f (g ≫ h) s = (cechModMap f h s).comp (cechModMap f g s) := by
  refine IsLocalizedModule.ext (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)
    (Cech.isUnit_algebraMap f P (le_refl s)
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) P)) ?_
  rw [cechModMap_comp_mk, LinearMap.comp_assoc, cechModMap_comp_mk, ← LinearMap.comp_assoc,
    cechModMap_comp_mk, LinearMap.comp_assoc]
  rfl

/-- The induced maps commute with the transition maps `M_{∏ i ∈ s} ⟶ M_{∏ i ∈ t}` of the
complex: both composites are determined by their values on the images of `M`. -/
theorem cechι_comp_cechModMap (g : M ⟶ N) {s t : Finset (Fin r)} (hst : s ⊆ t) :
    (Cech.cechι f N hst).comp (cechModMap f g s) =
      (cechModMap f g t).comp (Cech.cechι f M hst) := by
  refine IsLocalizedModule.ext (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)
    (Cech.isUnit_algebraMap f N hst
      (LocalizedModule.mkLinearMap (Cech.cechSub f t) N)) ?_
  rw [LinearMap.comp_assoc, cechModMap_comp_mk, ← LinearMap.comp_assoc, Cech.cechι_comp_mk,
    LinearMap.comp_assoc, Cech.cechι_comp_mk, cechModMap_comp_mk]

/-- The elementwise form of the commutation with the transition maps. -/
theorem cechι_cechModMap (g : M ⟶ N) {s t : Finset (Fin r)} (hst : s ⊆ t)
    (x : Cech.cechMod f M s) :
    Cech.cechι f N hst (cechModMap f g s x) = cechModMap f g t (Cech.cechι f M hst x) :=
  LinearMap.congr_fun (cechι_comp_cechModMap f g hst) x

/-! ### The induced map on the terms of the complex -/

/-- The map induced by `g : M ⟶ N` on the degree-`p` term of the extended alternating Čech
complex: `g` acts on each localized summand. -/
def cechTermMap (g : M ⟶ N) (p : ℕ) : Cech.cechTerm f M p →ₗ[R] Cech.cechTerm f N p :=
  DirectSum.toModule R _ _ fun s =>
    (DirectSum.lof R {t : Finset (Fin r) // t.card = p}
      (fun t => Cech.cechMod f N t.1) s).comp (cechModMap f g s.1)

/-- On the summand indexed by `s`, the induced map is the one on that localization. -/
@[simp] theorem cechTermMap_lof (g : M ⟶ N) (p : ℕ)
    (s : {s : Finset (Fin r) // s.card = p}) (x : Cech.cechMod f M s.1) :
    cechTermMap f g p (DirectSum.lof R _ (fun t => Cech.cechMod f M t.1) s x) =
      DirectSum.lof R _ (fun t => Cech.cechMod f N t.1) s (cechModMap f g s.1 x) := by
  rw [cechTermMap, DirectSum.toModule_lof]
  rfl

/-- The induced maps commute with the alternating differential: on the summand indexed by `s`
both composites are the sum over the new indices of the transition map followed by `g`. -/
theorem cechTermMap_comp_cechD (g : M ⟶ N) (p : ℕ) :
    (Cech.cechD f N p).comp (cechTermMap f g p) =
      (cechTermMap f g (p + 1)).comp (Cech.cechD f M p) := by
  refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, cechTermMap_lof, Cech.cechD_lof, map_sum, map_zsmul,
    cechι_cechModMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cechTermMap_lof]

/-- The identity induces the identity on the terms of the complex. -/
@[simp] theorem cechTermMap_id (p : ℕ) : cechTermMap f (𝟙 M) p = LinearMap.id := by
  refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cechTermMap_lof, cechModMap_id]
  rfl

/-- A composite induces the composite on the terms of the complex. -/
theorem cechTermMap_comp (g : M ⟶ N) (h : N ⟶ P) (p : ℕ) :
    cechTermMap f (g ≫ h) p = (cechTermMap f h p).comp (cechTermMap f g p) := by
  refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, cechTermMap_lof, LinearMap.comp_apply, LinearMap.comp_apply,
    cechTermMap_lof, cechTermMap_lof, cechModMap_comp f g h s.1]
  rfl

end Free

/-! ### The induced map of complexes

`Cech.cechComplex f M` is a complex of `ModuleCat.{max u v} R`, and the functor below is an
endofunctor of `ModuleCat.{max u v} R`, so from here on the module universe is above the ring
universe. -/

variable {M N P : ModuleCat.{max u v} R}

/-- The map of extended alternating Čech complexes induced by a module map. -/
def cechComplexMap (g : M ⟶ N) : Cech.cechComplex f M ⟶ Cech.cechComplex f N where
  f p := ModuleCat.ofHom (cechTermMap f g p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    have hM : (Cech.cechComplex f M).d p (p + 1) = ModuleCat.ofHom (Cech.cechD f M p) := by
      simp only [Cech.cechComplex, CochainComplex.of_d]
    have hN : (Cech.cechComplex f N).d p (p + 1) = ModuleCat.ofHom (Cech.cechD f N p) := by
      simp only [Cech.cechComplex, CochainComplex.of_d]
    rw [hM, hN]
    exact ModuleCat.hom_ext (cechTermMap_comp_cechD f g p)

/-- The degree-`p` component of the induced map of complexes. -/
@[simp] theorem cechComplexMap_f (g : M ⟶ N) (p : ℕ) :
    (cechComplexMap f g).f p = ModuleCat.ofHom (cechTermMap f g p) := rfl

/-- The extended alternating Čech complex `C^•(f₁, …, f_r; -)` as a functor from `R`-modules to
`ℕ`-indexed cochain complexes of `R`-modules. -/
def cechFunctor : ModuleCat.{max u v} R ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ where
  obj M := Cech.cechComplex f M
  map g := cechComplexMap f g
  map_id M := HomologicalComplex.hom_ext _ _ fun p => by
    rw [cechComplexMap_f, cechTermMap_id, HomologicalComplex.id_f]
    rfl
  map_comp {M N P} g h := HomologicalComplex.hom_ext _ _ fun p => by
    rw [cechComplexMap_f, cechTermMap_comp, HomologicalComplex.comp_f, cechComplexMap_f,
      cechComplexMap_f]
    rfl

/-- The Čech functor at a module is the Čech complex of that module. -/
@[simp] theorem cechFunctor_obj : (cechFunctor.{v} f).obj M = Cech.cechComplex f M := rfl

/-- The Čech functor on a module map is the induced map of complexes. -/
@[simp] theorem cechFunctor_map (g : M ⟶ N) :
    (cechFunctor.{v} f).map g = cechComplexMap f g := rfl

/-- The map of integer-indexed Čech complexes induced by a module map. -/
def extendedCechComplexMap (g : M ⟶ N) :
    extendedCechComplex f M ⟶ extendedCechComplex f N :=
  HomologicalComplex.extendMap (cechComplexMap f g) ComplexShape.embeddingUpNat

/-- The extended alternating Čech complex in integer degrees, as a functor of the module. -/
def extendedCechFunctor :
    ModuleCat.{max u v} R ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ :=
  cechFunctor.{v} f ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{max u v} R)

/-- The integer-indexed Čech functor at a module is the integer-indexed Čech complex. -/
@[simp] theorem extendedCechFunctor_obj :
    (extendedCechFunctor.{v} f).obj M = extendedCechComplex f M := rfl

/-- The integer-indexed Čech functor on a module map is the induced map of complexes. -/
@[simp] theorem extendedCechFunctor_map (g : M ⟶ N) :
    (extendedCechFunctor.{v} f).map g = extendedCechComplexMap f g := rfl

/-- The identity induces the identity on the integer-indexed complex. -/
@[simp] theorem extendedCechComplexMap_id :
    extendedCechComplexMap f (𝟙 M) = 𝟙 (extendedCechComplex f M) :=
  (extendedCechFunctor.{v} f).map_id M

/-- A composite induces the composite on the integer-indexed complex. -/
theorem extendedCechComplexMap_comp (g : M ⟶ N) (h : N ⟶ P) :
    extendedCechComplexMap f (g ≫ h) =
      extendedCechComplexMap f g ≫ extendedCechComplexMap f h :=
  (extendedCechFunctor.{v} f).map_comp g h

/-- The Čech object of the derived category of `R`, functorially in the module. -/
def extendedCechObjectFunctor :
    ModuleCat.{max u v} R ⥤ DerivedCategory (ModuleCat.{max u v} R) :=
  extendedCechFunctor.{v} f ⋙ DerivedCategory.Q

/-- The Čech object functor at a module is the Čech object of that module. -/
@[simp] theorem extendedCechObjectFunctor_obj :
    (extendedCechObjectFunctor.{v} f).obj M = extendedCechObject f M := rfl

end Stacks.LocalCohomology

end
