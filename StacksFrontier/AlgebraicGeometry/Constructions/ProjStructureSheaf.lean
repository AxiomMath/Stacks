module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.RingTheory.HomogeneousLocalization.DegreeZero
public import StacksFrontier.RingTheory.Module.Localization.Exactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf associated to a graded module on Proj

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring. Its homogeneous spectrum carries the structure sheaf
`AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf`, whose sections over an open `U` are
the functions into the degree-zero homogeneous localizations at the points of `U` that are
locally a fraction `a / s` with `a` and `s` homogeneous of equal degree; this makes
`AlgebraicGeometry.Proj.toLocallyRingedSpace` a locally ringed space.

This file carries out the same construction for a graded module `M = ⨁_{i ∈ ℤ} 𝒨 i` over `A`.
The sections of the associated sheaf `M̃` over `U` are the functions into the localizations
`M_p` that are locally a fraction `m / s` with `m ∈ 𝒨 n` and `s ∈ 𝒜 n`; the local-fraction
condition is a `LocalPredicate`, so the result is a sheaf without any further work. The content
of the file is the comparison with the degree-zero localizations of `M`: on a standard open
`D₊(f)` of a homogeneous `f` of positive degree, the canonical map `M₍f₎ → Γ(D₊(f), M̃)` sending a
fraction to itself in every fibre is a linear isomorphism, and it carries the restriction maps
of `M̃` to the degree-zero restriction maps of `ProjectiveSpectrum.moduleRestrictionMaps`.

Injectivity is local-global: a degree-zero fraction vanishing in every fibre over `D₊(f)`
vanishes, because `D₊(f) = Spec A₍f₎` and a module element killed at every maximal ideal is
zero. Surjectivity uses that `D₊(f)` is quasi-compact
(`ProjectiveSpectrum.exists_finite_basicOpen_refinement`) to reduce an arbitrary section to a
finite family of fractions, and then the sheaf condition for the localizations `M₍gᵢ₎` of `M₍f₎`,
which is `IsLocalizedModule.Away.injective_pi_and_exact_of_span_range_eq_top` together with the
unit-ideal criterion of
`AlgebraicGeometry.Proj.basicOpen_le_iSup_iff_span_isLocalizationElem_eq_top`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf`: the sheaf `M̃`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroToSection`: the canonical linear map
  `M₍f₎ → Γ(D₊(f), M̃)`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`: the
  resulting identification `Γ(D₊(f), M̃) ≃ₗ M₍f₎`.

## Main results

* `degreeZeroToSection_injective` and `degreeZeroToSection_surjective`: the standard-open
  comparison is bijective for `f` homogeneous of positive degree.
* `degreeZeroToSection_fraction`: its value on a fraction.
* `degreeZeroToSection_restriction`: it intertwines restriction in `M̃` with the degree-zero
  restriction maps.
* `moduleSections_locally_degreeZeroToSection`: every section is locally in its image, with the
  denominator homogeneous of strictly positive degree.

## Implementation notes

The ring and the module have independent universes. A section is a dependent function on an open
subset of the homogeneous spectrum, so sections live in the maximum of the two; accordingly the
sheaf is a `SheafOfModules` in that universe rather than the universe-restricted
`AlgebraicGeometry.Scheme.Modules`.

The fibre `ModuleFiber 𝒜 x` is the full localization of `M` at the homogeneous prime `x`, not its
degree-zero part: the degree-zero condition is imposed on *sections*, by requiring local
homogeneous fraction representatives of equal numerator and denominator degree. This keeps the
fibres a plain `LocalizedModule` and makes the local-fraction predicate the only place where
grading is used.

The standard-open comparison is stated as a map linear over `A₍f₎`, with the scalar action on
sections transported along Mathlib's `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`.
Because `degreeZeroToSection_restriction` identifies restriction with the degree-zero map of
Tag 01M4, the comparison extends to the whole standard-open presheaf, not merely to its objects.

A graded ring acts on a ℤ-graded module by `VAdd ℕ ℤ`, supplied here as a file-local instance.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public section

add_to_stacks 01M6 "part (1), the structure sheaf"
  AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf

add_to_stacks 01M6 "part (2), the homogeneous spectrum as a locally ringed space"
  AlgebraicGeometry.Proj.toLocallyRingedSpace

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The action of `ℕ` on `ℤ` by addition: `n +ᵥ z = n + z`. -/
local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- The homogeneous ideal of a point of `Proj` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒜) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- Ambient module fiber at a homogeneous prime. The degree-zero condition is imposed on
sections, by requiring local homogeneous fraction representatives. -/
public abbrev ModuleFiber (x : ProjectiveSpectrum.top 𝒜) :=
  LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl M

/-- A homogeneous fraction with numerator and denominator of the same degree. -/
public def IsModuleFraction {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (a : ∀ x : U, ModuleFiber (M := M) 𝒜 x.1) : Prop :=
  ∃ (n : ℕ) (m : M) (s : S), m ∈ 𝒨 (n : ℤ) ∧ s ∈ 𝒜 n ∧
    ∃ hs : ∀ x : U, s ∉ x.1.asHomogeneousIdeal,
      ∀ x : U, a x = LocalizedModule.mk m ⟨s, hs x⟩

/-- Homogeneous fraction representatives restrict to smaller opens. -/
public def moduleFractionPrelocal : PrelocalPredicate (ModuleFiber (M := M) 𝒜) where
  pred := IsModuleFraction 𝒜 𝒨
  res := by
    rintro V U i a ⟨n, m, s, hm, hs, hn, ha⟩
    exact ⟨n, m, s, hm, hs, fun x => hn (i x), fun x => ha (i x)⟩

/-- The local degree-zero fraction condition defining the associated sheaf. -/
public def locallyModuleFraction : LocalPredicate (ModuleFiber (M := M) 𝒜) :=
  (moduleFractionPrelocal 𝒜 𝒨).sheafify

/-- Pointwise action of the structure sheaf on the ambient module fibers. -/
public noncomputable def moduleScalarMap (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U) →+*
      ∀ x : U, Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl where
  toFun r x := HomogeneousLocalization.val (r.1 x)
  map_zero' := funext fun _ => HomogeneousLocalization.val_zero
  map_one' := funext fun _ => HomogeneousLocalization.val_one
  map_add' _ _ := funext fun _ => HomogeneousLocalization.val_add _ _
  map_mul' _ _ := funext fun _ => HomogeneousLocalization.val_mul _ _

/-- The structure sheaf acts on the dependent functions into the module fibers. -/
public noncomputable instance moduleFunctionModule (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U))
      (∀ x : U, ModuleFiber (M := M) 𝒜 x.1) :=
  Module.compHom _ (moduleScalarMap 𝒜 U)

/-- Sections of the associated module sheaf, with their pointwise module structure. -/
public noncomputable def moduleSections (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Submodule ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U))
      (∀ x : U, ModuleFiber (M := M) 𝒜 x.1) where
  carrier := {a | (locallyModuleFraction 𝒜 𝒨).pred a}
  zero_mem' x := ⟨U, x.2, 𝟙 _, 0, 0, 1, zero_mem _,
    SetLike.one_mem_graded 𝒜, fun y => y.1.isPrime.one_notMem, fun y => by simp⟩
  add_mem' {a b} ha hb x := by
    obtain ⟨V, hxV, iV, n, m, s, hm, hs, hn, ha⟩ := ha x
    obtain ⟨W, hxW, iW, k, l, r, hl, hr, hp, hb⟩ := hb x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft _ _ ≫ iV,
      n + k, r • m + s • l, s * r, ?_, SetLike.mul_mem_graded hs hr,
      fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
        (hn ⟨y.1, y.2.1⟩) (hp ⟨y.1, y.2.2⟩), ?_⟩
    · apply add_mem
      · simpa only [Nat.cast_add, add_comm] using
          (show r • m ∈ 𝒨 ((k : ℤ) + n) from SetLike.GradedSMul.smul_mem hr hm)
      · simpa only [Nat.cast_add] using
          (show s • l ∈ 𝒨 ((n : ℤ) + k) from SetLike.GradedSMul.smul_mem hs hl)
    · intro y
      exact congrArg₂ (· + ·) (ha ⟨y.1, y.2.1⟩) (hb ⟨y.1, y.2.2⟩) |>.trans
        (LocalizedModule.mk_add_mk ..)
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, iV, n, ⟨b, hr⟩, ⟨s, hs⟩, hn, h⟩ := r.2 x
    obtain ⟨W, hxW, iW, k, m, t, hm, ht, hp, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft _ _ ≫ iV,
      n + k, b • m, t * s, ?_, ?_,
      fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
        (hp ⟨y.1, y.2.2⟩) (hn ⟨y.1, y.2.1⟩), ?_⟩
    · simpa only [Nat.cast_add] using
        (show b • m ∈ 𝒨 ((n : ℤ) + k) from SetLike.GradedSMul.smul_mem hr hm)
    · simpa [add_comm] using SetLike.mul_mem_graded ht hs
    · rintro ⟨y, hyV, hyW⟩
      change HomogeneousLocalization.val (r.1 (iV ⟨y, hyV⟩)) •
        a (iW ⟨y, hyW⟩) = _
      exact congrArg₂ (· • ·) (congrArg HomogeneousLocalization.val (h ⟨y, hyV⟩))
        (ha ⟨y, hyW⟩)

/-- The underlying presheaf of abelian groups of the associated sheaf. -/
public noncomputable def modulePresheaf : Presheaf AddCommGrpCat.{max u v}
    (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of (moduleSections 𝒜 𝒨 U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun a := ⟨fun x => a.1 (i.unop x),
        (locallyModuleFraction 𝒜 𝒨).res i.unop a.1 a.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- The sections of `modulePresheaf` are a module over the sections of the structure sheaf. -/
public noncomputable instance modulePresheafModule
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj U)
      ((modulePresheaf 𝒜 𝒨).obj U) :=
  inferInstanceAs (Module _ (moduleSections 𝒜 𝒨 U.unop))

omit [Decomposition 𝒨] in
/-- Restriction in `modulePresheaf` is semilinear over restriction in the structure sheaf. -/
public lemma modulePresheaf_map_smul {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (i : U ⟶ V) (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj U)
    (a : (modulePresheaf 𝒜 𝒨).obj U) :
    (modulePresheaf 𝒜 𝒨).map i (r • a) =
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.map i r •
        (modulePresheaf 𝒜 𝒨).map i a := rfl

/-- The actual sheaf associated to a graded module. Its sections are locally homogeneous
fractions of degree zero, and its restrictions are restrictions of dependent functions. -/
@[stacks 01M6 "part (3), the sheaf associated to a graded module", sga "6 VI 2.3.2" "affine base"]
public noncomputable def associatedModuleSheaf :
    SheafOfModules.{max u v}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜)) := by
  letI : ∀ U, Module
      (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj U) ((modulePresheaf 𝒜 𝒨).obj U) :=
    fun U => modulePresheafModule 𝒜 𝒨 U
  exact SheafOfModules.mk
    (PresheafOfModules.ofPresheaf
      (R := (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙ forget₂ CommRingCat RingCat)
      (modulePresheaf 𝒜 𝒨) (fun {_ _} i r a => modulePresheaf_map_smul 𝒜 𝒨 i r a)) (by
      rw [PresheafOfModules.ofPresheaf_presheaf]
      exact CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ (modulePresheaf 𝒜 𝒨)
        (forget AddCommGrpCat.{max u v})
        (subsheafToTypes (locallyModuleFraction 𝒜 𝒨)).property)

/-- The canonical map from the ordinary localization to the fiber at a point of `D₊(f)`. -/
public noncomputable def moduleToFiber (f : S) (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    LocalizedModule.Away (R := S) f M →ₗ[S] ModuleFiber (M := M) 𝒜 x.1 :=
  LocalizedModule.liftOfLE _ _ (Submonoid.powers_le.mpr x.2)

/-- `moduleToFiber` sends the fraction `m / s` to the same fraction `m / s` in the fiber. -/
@[simp]
public lemma moduleToFiber_mk (f : S) (x : ProjectiveSpectrum.basicOpen 𝒜 f)
    (m : M) (s : Submonoid.powers f) :
    moduleToFiber (M := M) 𝒜 f x (LocalizedModule.mk m s) =
      LocalizedModule.mk m ⟨s.1, (Submonoid.powers_le.mpr x.2) s.2⟩ := by
  simpa only [moduleToFiber, IsLocalizedModule.mk_eq_mk'] using
    IsLocalizedModule.liftOfLE_mk' (Submonoid.powers f)
      x.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr x.2)
      (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ M) m s

/-- Passing to a fiber is semilinear over the embedding of the degree-zero localization. -/
public lemma moduleToFiber_smul (f : S) (x : ProjectiveSpectrum.basicOpen 𝒜 f)
    (r : HomogeneousLocalization.Away 𝒜 f) (a : LocalizedModule.Away (R := S) f M) :
    moduleToFiber (M := M) 𝒜 f x (HomogeneousLocalization.val r • a) =
      HomogeneousLocalization.val
        (HomogeneousLocalization.mapId 𝒜
          (Q := x.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (Submonoid.powers_le.mpr x.2) r) •
          moduleToFiber (M := M) 𝒜 f x a := by
  obtain ⟨r, rfl⟩ := HomogeneousLocalization.mk_surjective r
  induction a using LocalizedModule.induction_on with
  | h m s =>
    show moduleToFiber 𝒜 f x (Localization.mk _ _ • LocalizedModule.mk m s) =
      Localization.mk _ _ • moduleToFiber 𝒜 f x (LocalizedModule.mk m s)
    simp only [LocalizedModule.mk_smul_mk, moduleToFiber_mk]
    rfl

/-- The image of a degree-zero localization element is locally a homogeneous fraction. -/
public lemma degreeZeroToSection_mem (f : S)
    (a : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    (fun x => moduleToFiber (M := M) 𝒜 f x a.1) ∈
      moduleSections 𝒜 𝒨 (ProjectiveSpectrum.basicOpen 𝒜 f) := by
  let := moduleFunctionModule (M := M) 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f)
  rcases a with ⟨a, ha⟩
  let F : LocalizedModule.Away (R := S) f M →ₗ[S]
      (∀ x : ProjectiveSpectrum.basicOpen 𝒜 f, ModuleFiber (M := M) 𝒜 x.1) :=
    LinearMap.pi (fun x => moduleToFiber 𝒜 f x)
  show F a ∈ _
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨d, n, hf, m, hm, rfl⟩ := ha
    intro x
    refine ⟨_, x.2, 𝟙 _, n * d, m, f ^ n, ?_, ?_,
      fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 n, ?_⟩
    · simpa only [nsmul_eq_mul, Nat.cast_mul] using hm
    · simpa using SetLike.pow_mem_graded n hf
    · intro y
      exact moduleToFiber_mk 𝒜 f y m _
  | zero =>
    rw [map_zero]
    exact (moduleSections 𝒜 𝒨 (ProjectiveSpectrum.basicOpen 𝒜 f)).zero_mem
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (moduleSections 𝒜 𝒨 (ProjectiveSpectrum.basicOpen 𝒜 f)).add_mem ha hb
  | smul r a _ ha =>
    have h := (moduleSections 𝒜 𝒨 (ProjectiveSpectrum.basicOpen 𝒜 f)).smul_mem
      (ProjectiveSpectrum.Proj.awayToSection 𝒜 f r) ha
    have heq : F (HomogeneousLocalization.val r • a) =
        (ProjectiveSpectrum.Proj.awayToSection 𝒜 f r) • F a :=
      funext fun x => moduleToFiber_smul 𝒜 f x r a
    exact heq.symm ▸ h

/-- Sections over a standard open are a module over the degree-zero localization there. -/
public noncomputable instance standardOpenModule (f : S) :
    Module (HomogeneousLocalization.Away 𝒜 f)
      (moduleSections 𝒜 𝒨 (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  Module.compHom _ (ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom

/-- The canonical standard-open comparison `M_(f) → Γ(D₊(f), M̃)`. It sends each
homogeneous fraction to that same fraction in every fiber. -/
public noncomputable def degreeZeroToSection (f : S) :
    GradedModuleDegreeZeroLocalization 𝒜 𝒨 f →ₗ[HomogeneousLocalization.Away 𝒜 f]
      moduleSections 𝒜 𝒨 (ProjectiveSpectrum.basicOpen 𝒜 f) where
  toFun a := ⟨fun x => moduleToFiber (M := M) 𝒜 f x a.1, degreeZeroToSection_mem 𝒜 𝒨 f a⟩
  map_add' a b := by ext x; exact map_add (moduleToFiber 𝒜 f x) a.1 b.1
  map_smul' r a := by ext x; exact moduleToFiber_smul 𝒜 f x r a.1

/-- A homogeneous fraction `m / f^n` in the degree-zero localization. -/
public noncomputable def degreeZeroFraction {f : S} {d : ℕ} (hf : f ∈ 𝒜 d)
    (n : ℕ) (m : M) (hm : m ∈ 𝒨 (n • (d : ℤ))) :
    GradedModuleDegreeZeroLocalization 𝒜 𝒨 f := by
  letI := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  exact ⟨LocalizedModule.mk m ⟨f ^ n, ⟨n, rfl⟩⟩,
    Submodule.subset_span ⟨d, n, hf, m, hm, rfl⟩⟩

/-- The standard-open comparison has the expected formula on homogeneous fractions. -/
@[simp]
public theorem degreeZeroToSection_fraction {f : S} {d : ℕ} (hf : f ∈ 𝒜 d)
    (n : ℕ) (m : M) (hm : m ∈ 𝒨 (n • (d : ℤ)))
    (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    (degreeZeroToSection 𝒜 𝒨 f (degreeZeroFraction 𝒜 𝒨 hf n m hm)).1 x =
      LocalizedModule.mk m
        ⟨f ^ n, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 n⟩ :=
  moduleToFiber_mk 𝒜 f x m _

/-- Every section is locally in the image of a standard-open degree-zero localization.
The denominator can always be chosen homogeneous of strictly positive degree. -/
public theorem moduleSections_locally_degreeZeroToSection
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (a : moduleSections 𝒜 𝒨 U) (x : U) :
    ∃ (V : Opens (ProjectiveSpectrum.top 𝒜)) (_ : x.1 ∈ V) (i : V ⟶ U)
      (f : S) (d : ℕ) (_ : 0 < d) (_ : f ∈ 𝒜 d)
      (hVf : V ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
      (b : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f),
      ∀ y : V, a.1 (i y) = (degreeZeroToSection 𝒜 𝒨 f b).1 ⟨y.1, hVf y.2⟩ := by
  obtain ⟨V, hxV, iV, n, m, s, hm, hs, hn, ha⟩ := a.2 x
  have hpos : ∃ (k : ℕ) (_ : 0 < k) (g : S), g ∈ 𝒜 k ∧ g ∉ x.1.asHomogeneousIdeal := by
    by_contra! h
    exact x.1.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr
      fun k hk g hg => h k hk g hg)
  obtain ⟨k, hk, g, hg, hgx⟩ := hpos
  let W := V ⊓ ProjectiveSpectrum.basicOpen 𝒜 g
  have hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 (s * g) := by
    rw [ProjectiveSpectrum.basicOpen_mul]
    exact fun y hy => ⟨hn ⟨y, hy.1⟩, hy.2⟩
  have hgm : g • m ∈ 𝒨 (1 • ((n + k : ℕ) : ℤ)) := by
    simpa only [one_smul, Nat.cast_add, add_comm] using
      (show g • m ∈ 𝒨 ((k : ℤ) + n) from SetLike.GradedSMul.smul_mem hg hm)
  refine ⟨W, ⟨hxV, hgx⟩, Opens.infLELeft _ _ ≫ iV, s * g, n + k,
    by omega, SetLike.mul_mem_graded hs hg, hW,
    degreeZeroFraction 𝒜 𝒨 (SetLike.mul_mem_graded hs hg) 1 (g • m) hgm, ?_⟩
  rintro ⟨y, hyV, hyg⟩
  show a.1 (iV ⟨y, hyV⟩) = _
  rw [degreeZeroToSection_fraction]
  refine (ha ⟨y, hyV⟩).trans
    ((LocalizedModule.mk_cancel_common_right
      (⟨s, hn ⟨y, hyV⟩⟩ : y.asHomogeneousIdeal.toIdeal.primeCompl) ⟨g, hyg⟩ m).symm.trans ?_)
  apply congrArg (LocalizedModule.mk (g • m))
  exact Subtype.ext (pow_one (s * g)).symm

/-- The localized restriction map `M_f → M_g`, regarded as an `S`-linear map. -/
private noncomputable def localizedRestrictionLinear (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    LocalizedModule.Away (R := S) f M →ₗ[S] LocalizedModule.Away (R := S) g M :=
  let maps := ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg
  let φ := ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg
  letI := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
    (LocalizedModule.Away (R := S) g M) φ.toRingHom
  { toFun := maps.localizedMap
    map_add' := maps.localizedMap.map_add
    map_smul' := fun r a => by
      have h := maps.localizedMap.map_smul (algebraMap S (Localization.Away f) r) a
      change maps.localizedMap (algebraMap S (Localization.Away f) r • a) =
        φ (algebraMap S (Localization.Away f) r) • maps.localizedMap a at h
      simpa only [φ.commutes, algebraMap_smul, RingHom.id_apply] using h }

/-- Localization restriction followed by evaluation is evaluation at the same prime. -/
public lemma moduleToFiber_restriction (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (x : ProjectiveSpectrum.basicOpen 𝒜 g) (a : LocalizedModule.Away (R := S) f M) :
    moduleToFiber 𝒜 g x
        ((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg).localizedMap a) =
      moduleToFiber 𝒜 f ⟨x.1, hfg x.2⟩ a := by
  let maps := ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg
  have heq : (moduleToFiber 𝒜 g x).comp (localizedRestrictionLinear 𝒜 𝒨 f g hf hg hfg) =
      moduleToFiber 𝒜 f ⟨x.1, hfg x.2⟩ := by
    apply IsLocalizedModule.ext (Submonoid.powers f)
      (LocalizedModule.mkLinearMap _ M) (fun s =>
        IsLocalizedModule.map_units
          (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (LocalizedModule.mkLinearMap x.1.asHomogeneousIdeal.toIdeal.primeCompl M)
          ⟨s.1, (Submonoid.powers_le.mpr (hfg x.2)) s.2⟩)
    ext m
    show moduleToFiber 𝒜 g x (maps.localizedMap (LocalizedModule.mkLinearMap _ M m)) = _
    rw [maps.map_mk]
    simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, moduleToFiber_mk]
    rfl
  exact DFunLike.congr_fun heq a

/-- Degree-zero restriction followed by evaluation is evaluation at the same prime. -/
private lemma moduleToFiber_degreeZeroMap (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (x : ProjectiveSpectrum.basicOpen 𝒜 g) (a : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    moduleToFiber (M := M) 𝒜 g x
        ((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg).degreeZeroMap a).1 =
      moduleToFiber 𝒜 f ⟨x.1, hfg x.2⟩ a.1 := by
  rw [(ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg).degreeZeroMap_val]
  exact moduleToFiber_restriction 𝒜 𝒨 f g hf hg hfg x a.1

/-- Localized restriction maps compose along `D₊(h) ≤ D₊(g) ≤ D₊(f)`. -/
private theorem localizedRestrictionLinear_comp (f g h : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hh : ∃ d : ℕ, 0 < d ∧ h ∈ 𝒜 d)
    (hgf : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hhg : ProjectiveSpectrum.basicOpen 𝒜 h ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    (localizedRestrictionLinear 𝒜 𝒨 g h hg hh hhg).comp
        (localizedRestrictionLinear 𝒜 𝒨 f g hf hg hgf) =
      localizedRestrictionLinear 𝒜 𝒨 f h hf hh (hhg.trans hgf) := by
  have ⟨d, hd, hfd⟩ := hf
  have ⟨e, he, hhe⟩ := hh
  have hfunit : IsUnit (algebraMap S (Localization.Away h) f) := by
    obtain ⟨k, hk, c, hc, hfactor⟩ :=
      ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le 𝒜 hfd hd hhe he (hhg.trans hgf)
    have hmul : IsUnit (algebraMap S (Localization.Away h) c *
        algebraMap S (Localization.Away h) f) := by
      rw [← map_mul, ← hfactor, map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit h).pow k
    exact isUnit_of_mul_isUnit_right hmul
  have hunit (s : Submonoid.powers f) :
      IsUnit (algebraMap S (Module.End S (LocalizedModule.Away (R := S) h M)) s) := by
    let : Module (Localization.Away h) (LocalizedModule.Away (R := S) h M) :=
      LocalizedModule.moduleOfIsLocalization
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (s : S) f).mp s.2
    have hs : IsUnit (algebraMap S (Localization.Away h) (s : S)) := by
      rw [← hk, map_pow]
      exact hfunit.pow k
    rw [Module.End.isUnit_iff]
    have hfun : ⇑(algebraMap S (Module.End S (LocalizedModule.Away (R := S) h M)) s) =
        fun z => algebraMap S (Localization.Away h) (s : S) • z :=
      funext fun z => (IsScalarTower.algebraMap_smul (Localization.Away h) (s : S) z).symm
    rw [hfun]
    exact hs.smul_bijective
  apply IsLocalizedModule.ext (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M) hunit
  ext m
  change (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 g h hg hh hhg).localizedMap
      ((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hgf).localizedMap
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m)) =
    (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f h hf hh
      (hhg.trans hgf)).localizedMap (LocalizedModule.mkLinearMap (Submonoid.powers f) M m)
  rw [(ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hgf).map_mk,
    (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 g h hg hh hhg).map_mk,
    (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f h hf hh
      (hhg.trans hgf)).map_mk]

/-- Degree-zero ring restriction maps compose along `D₊(h) ≤ D₊(g) ≤ D₊(f)`. -/
private theorem degreeZeroRingMap_comp (f g h : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hh : ∃ d : ℕ, 0 < d ∧ h ∈ 𝒜 d)
    (hgf : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hhg : ProjectiveSpectrum.basicOpen 𝒜 h ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 g h hg hh hhg).comp
        (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g hf hg hgf) =
      ProjectiveSpectrum.degreeZeroRingMap 𝒜 f h hf hh (hhg.trans hgf) := by
  have hloc : (ProjectiveSpectrum.localizedRingMap 𝒜 g h hg hh hhg).comp
      (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hgf) =
      ProjectiveSpectrum.localizedRingMap 𝒜 f h hf hh (hhg.trans hgf) := by
    apply Localization.algHom_ext (Submonoid.powers f)
    ext
  apply AlgHom.ext
  intro z
  apply HomogeneousLocalization.val_injective
  rw [AlgHom.comp_apply, ProjectiveSpectrum.val_degreeZeroRingMap,
    ProjectiveSpectrum.val_degreeZeroRingMap, ProjectiveSpectrum.val_degreeZeroRingMap]
  exact DFunLike.congr_fun hloc (HomogeneousLocalization.val z)

/-- The degree-zero restriction `M₍g₎ → M₍h₎` is linear over `A₍f₎` along
`D₊(h) ≤ D₊(g) ≤ D₊(f)`. -/
private noncomputable def degreeZeroRestrictionLinear (f g h : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hh : ∃ d : ℕ, 0 < d ∧ h ∈ 𝒜 d)
    (hgf : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hhg : ProjectiveSpectrum.basicOpen 𝒜 h ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    letI := Module.compHom (R := HomogeneousLocalization.Away 𝒜 g)
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g)
      (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g hf hg hgf).toRingHom
    letI := Module.compHom (R := HomogeneousLocalization.Away 𝒜 h)
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 h)
      (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f h hf hh (hhg.trans hgf)).toRingHom
    GradedModuleDegreeZeroLocalization 𝒜 𝒨 g →ₗ[HomogeneousLocalization.Away 𝒜 f]
      GradedModuleDegreeZeroLocalization 𝒜 𝒨 h :=
  letI := Module.compHom (R := HomogeneousLocalization.Away 𝒜 g)
    (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g)
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g hf hg hgf).toRingHom
  letI := Module.compHom (R := HomogeneousLocalization.Away 𝒜 h)
    (GradedModuleDegreeZeroLocalization 𝒜 𝒨 h)
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f h hf hh (hhg.trans hgf)).toRingHom
  letI := Module.compHom (R := HomogeneousLocalization.Away 𝒜 h)
    (GradedModuleDegreeZeroLocalization 𝒜 𝒨 h)
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 g h hg hh hhg).toRingHom
  let maps := ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 g h hg hh hhg
  { toFun := maps.degreeZeroMap
    map_add' := maps.degreeZeroMap.map_add
    map_smul' := fun r x => by
      change maps.degreeZeroMap
          ((ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g hf hg hgf).toRingHom r • x) =
        (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f h hf hh (hhg.trans hgf)).toRingHom r •
          maps.degreeZeroMap x
      rw [maps.degreeZeroMap.map_smul]
      exact congrArg (fun c => c • maps.degreeZeroMap x)
        (congrArg (fun φ => φ r) (degreeZeroRingMap_comp 𝒜 f g h hf hg hh hgf hhg)) }

/-- The standard-open comparison intertwines sheaf restriction with the canonical
degree-zero restriction map of 01M4. -/
public theorem degreeZeroToSection_restriction (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (a : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    (associatedModuleSheaf 𝒜 𝒨).val.map (homOfLE hfg).op
        (degreeZeroToSection 𝒜 𝒨 f a) =
      degreeZeroToSection 𝒜 𝒨 g
        ((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg).degreeZeroMap a) := by
  apply Subtype.ext
  funext x
  show moduleToFiber 𝒜 f ⟨x.1, hfg x.2⟩ a.1 =
    moduleToFiber 𝒜 g x
      ((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg).degreeZeroMap a).1
  exact (moduleToFiber_degreeZeroMap 𝒜 𝒨 f g hf hg hfg x a).symm

/-- The sections of the associated sheaf over an open are a module over the structure sheaf. -/
public noncomputable instance associatedModuleSheafSectionModule
    (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U))
      ((associatedModuleSheaf 𝒜 𝒨).val.obj (op U)) :=
  modulePresheafModule 𝒜 𝒨 (op U)

/-- The displayed section modules are the section modules of the constructed sheaf. -/
public noncomputable def associatedModuleSheafSectionsEquiv
    (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (associatedModuleSheaf 𝒜 𝒨).val.obj (op U) ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)]
      moduleSections 𝒜 𝒨 U := LinearEquiv.refl _ _

omit [Decomposition 𝒨] in
/-- In the section description, restriction is precomposition with the inclusion of opens. -/
@[simp]
public theorem associatedModuleSheaf_restrict_apply
    {U V : Opens (ProjectiveSpectrum.top 𝒜)} (i : V ⟶ U)
    (a : (associatedModuleSheaf 𝒜 𝒨).val.obj (op U)) (x : V) :
    (associatedModuleSheafSectionsEquiv 𝒜 𝒨 V
      ((associatedModuleSheaf 𝒜 𝒨).val.map i.op a)).1 x =
        (associatedModuleSheafSectionsEquiv 𝒜 𝒨 U a).1 (i x) := rfl

/-- The degree-zero localization is spanned by the fractions with homogeneous numerator and
denominator of equal degree, with no reference to a degree chosen for `f`. -/
private lemma degreeZeroLocalization_eq_homogeneousSpan (f : S) {d : ℕ}
    (hf : f ∈ 𝒜 d) :
    GradedModuleDegreeZeroLocalization 𝒜 𝒨 f =
      (letI := Module.compHom (R := Localization.Away f)
        (LocalizedModule.Away (R := S) f M)
        (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
       Submodule.span (HomogeneousLocalization.Away 𝒜 f)
        {z | ∃ (i : ℕ) (y : M) (g : Submonoid.powers f),
          y ∈ 𝒨 (i : ℤ) ∧ (g : S) ∈ 𝒜 i ∧
            z = LocalizedModule.mk y g}) := by
  let := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  change
    Submodule.span (HomogeneousLocalization.Away 𝒜 f)
      {z | ∃ (e n : ℕ) (hfe : f ∈ 𝒜 e) (y : M),
        y ∈ 𝒨 (n • (e : ℤ)) ∧
          z = LocalizedModule.mk y
            ⟨f ^ n, (Submonoid.mem_powers_iff (f ^ n) f).2 ⟨n, rfl⟩⟩} =
    Submodule.span (HomogeneousLocalization.Away 𝒜 f)
      {z | ∃ (i : ℕ) (y : M) (g : Submonoid.powers f),
        y ∈ 𝒨 (i : ℤ) ∧ (g : S) ∈ 𝒜 i ∧ z = LocalizedModule.mk y g}
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨e, n, hfe, y, hy, rfl⟩
    apply Submodule.subset_span
    refine ⟨n * e, y,
      ⟨f ^ n, (Submonoid.mem_powers_iff (f ^ n) f).2 ⟨n, rfl⟩⟩,
      ?_, SetLike.pow_mem_graded n hfe, rfl⟩
    simpa only [Nat.cast_mul, nsmul_eq_mul] using hy
  · apply Submodule.span_le.mpr
    rintro z ⟨i, y, g, hy, hg, rfl⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (g : S) f).mp g.2
    let sn : Submonoid.powers f :=
      ⟨f ^ n, (Submonoid.mem_powers_iff (f ^ n) f).2 ⟨n, rfl⟩⟩
    have hgval : g = ⟨f ^ n, (Submonoid.mem_powers_iff (f ^ n) f).2 ⟨n, rfl⟩⟩ :=
      Subtype.ext hn.symm
    subst g
    by_cases hpow : f ^ n = 0
    · have hz : LocalizedModule.mk y sn = 0 := by
        let hzmem : (0 : S) ∈ Submonoid.powers f :=
          (Submonoid.mem_powers_iff (0 : S) f).2 ⟨n, hpow⟩
        let : Subsingleton (LocalizedModule.Away (R := S) f M) :=
          LocalizedModule.subsingleton hzmem
        exact Subsingleton.elim _ _
      rw [hz]
      exact Submodule.zero_mem _
    · have hdeg := DirectSum.degree_eq_of_mem_mem 𝒜 hg
        (SetLike.pow_mem_graded n hf) hpow
      have hidx : (i : ℤ) = n • (d : ℤ) := by
        rw [hdeg]
        simp [Nat.cast_mul]
      have hy' : y ∈ 𝒨 (n • (d : ℤ)) := by
        simpa only [hidx] using hy
      apply Submodule.subset_span
      exact ⟨d, n, hf, y, hy', rfl⟩

/-- A degree-zero fraction vanishing in every fiber over `D₊(f)` is zero: the standard open is
`Spec A₍f₎`, and a module element vanishing at every maximal ideal of a ring is zero. -/
private lemma degreeZeroLocalization_eq_zero_of_fibers {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (a : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f)
    (ha : ∀ x : ProjectiveSpectrum.basicOpen 𝒜 f,
      moduleToFiber (M := M) 𝒜 f x a.1 = 0) : a = 0 := by
  classical
  let R := HomogeneousLocalization.Away 𝒜 f
  let := Module.compHom (R := Localization.Away f)
    (LocalizedModule.Away (R := S) f M) (algebraMap R (Localization.Away f))
  let N := Submodule.span R
    {z : LocalizedModule.Away (R := S) f M |
      ∃ (i : ℕ) (y : M) (g : Submonoid.powers f),
        y ∈ 𝒨 (i : ℤ) ∧ (g : S) ∈ 𝒜 i ∧ z = LocalizedModule.mk y g}
  have hEq : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f = N :=
    degreeZeroLocalization_eq_homogeneousSpan 𝒜 𝒨 f hf
  let a' : N := ⟨a.1, hEq ▸ a.2⟩
  have : IsIso (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base :=
    ProjectiveSpectrum.Proj.toSpec_base_isIso 𝒜 hf hd
  let e := asIso (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base
  let xOf (Q : Ideal R) [Q.IsMaximal] : ProjectiveSpectrum.basicOpen 𝒜 f :=
    e.inv ⟨Q, inferInstance⟩
  let pOf (Q : Ideal R) [Q.IsMaximal] := (xOf Q).1.asHomogeneousIdeal.toIdeal
  let qOf (Q : Ideal R) [Q.IsMaximal] : PrimeSpectrum R := ⟨Q, inferInstance⟩
  let (Q : Ideal R) [Q.IsMaximal] : (pOf Q).IsPrime := (xOf Q).1.isPrime
  let (Q : Ideal R) [Q.IsMaximal] : Module R
      (LocalizedModule (pOf Q).primeCompl M) :=
    Module.compHom _
      ((algebraMap (HomogeneousLocalization.AtPrime 𝒜 (pOf Q))
          (Localization (pOf Q).primeCompl)).comp
        (HomogeneousLocalization.mapId 𝒜
          (Submonoid.powers_le.mpr (xOf Q).2)))
  let T (Q : Ideal R) [Q.IsMaximal] :=
    Submodule.span R
      {z : LocalizedModule (pOf Q).primeCompl M |
        ∃ (i : ℕ) (y : M) (g : (pOf Q).primeCompl),
          y ∈ 𝒨 (i : ℤ) ∧ (g : S) ∈ 𝒜 i ∧ z = LocalizedModule.mk y g}
  let hloc (Q : Ideal R) [Q.IsMaximal] :
      ∃ ψ : N →ₗ[R] T Q,
        (∀ z : N, (ψ z : LocalizedModule (pOf Q).primeCompl M) =
          LocalizedModule.liftOfLE (Submonoid.powers f) (pOf Q).primeCompl
            (Submonoid.powers_le.mpr (xOf Q).2)
            (z : LocalizedModule.Away (R := S) f M)) ∧
          IsLocalizedModule Q.primeCompl ψ := by
    let hp : (pOf Q).IsPrime := (xOf Q).1.isPrime
    let := hp
    have hhom : (pOf Q).IsHomogeneous 𝒜 := (xOf Q).1.asHomogeneousIdeal.isHomogeneous
    have hnot : f ∉ pOf Q := (xOf Q).2
    have hq : ∀ z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f),
        HomogeneousLocalization.mk z ∈ Q ↔ z.num.1 ∈ pOf Q := by
      intro z
      show HomogeneousLocalization.mk z ∈ (qOf Q).asIdeal ↔ _
      have hpt : (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base (xOf Q) = qOf Q := by
        show (ConcreteCategory.hom e.hom) ((ConcreteCategory.hom e.inv) (qOf Q)) = qOf Q
        exact congrArg (fun g => (ConcreteCategory.hom g) (qOf Q)) e.inv_hom_id
      rw [← hpt]
      exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 (xOf Q) z
    let hsmul (i : ℕ) (j : ℤ) (r : S) (m : M)
        (hr : r ∈ 𝒜 i) (hm : m ∈ 𝒨 j) :=
      SetLike.GradedSMul.smul_mem hr hm
    exact HomogeneousLocalization.isLocalizedModule_atPrime
      𝒜 𝒨 hsmul (pOf Q) hhom hf hd hnot Q hq
  let φ (Q : Ideal R) [Q.IsMaximal] : N →ₗ[R] T Q := Classical.choose (hloc Q)
  have hφlocal (Q : Ideal R) [Q.IsMaximal] : IsLocalizedModule Q.primeCompl (φ Q) := by
    exact (Classical.choose_spec (hloc Q)).2
  have hφzero (Q : Ideal R) [Q.IsMaximal] : φ Q a' = 0 := by
    apply Subtype.ext
    show (φ Q a' : LocalizedModule (pOf Q).primeCompl M) = 0
    rw [(Classical.choose_spec (hloc Q)).1 a']
    simpa [moduleToFiber] using ha (xOf Q)
  have hNzero : a' = 0 :=
    @Module.eq_zero_of_localization_maximal R N _ _ _
      (fun Q => ↥(T Q)) _ _ φ (fun Q => hφlocal Q) a' hφzero
  apply Subtype.ext
  simpa [a'] using congrArg Subtype.val hNzero

/-- Distinct degree-zero fractions give distinct sections on a positive-degree standard open. -/
@[stacks 01M6 "part (3), injectivity of the standard-open comparison"]
public theorem degreeZeroToSection_injective {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Function.Injective (degreeZeroToSection 𝒜 𝒨 f) := by
  intro a b hab
  apply sub_eq_zero.mp
  have hsub : degreeZeroToSection 𝒜 𝒨 f (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hval : (degreeZeroToSection 𝒜 𝒨 f (a - b)).1 = 0 :=
    congrArg Subtype.val hsub
  have hfib : ∀ x : ProjectiveSpectrum.basicOpen 𝒜 f,
      moduleToFiber (M := M) 𝒜 f x (a.1 - b.1) = 0 := by
    intro x
    have hx := congrFun hval x
    change moduleToFiber (M := M) 𝒜 f x (a.1 - b.1) = 0 at hx
    exact hx
  exact degreeZeroLocalization_eq_zero_of_fibers 𝒜 𝒨 hf hd (a - b) hfib

/-- Every section on a positive-degree standard open comes from a degree-zero fraction. -/
@[stacks 01M6 "part (3), surjectivity of the standard-open comparison"]
public theorem degreeZeroToSection_surjective {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Function.Surjective (degreeZeroToSection 𝒜 𝒨 f) := by
  classical
  intro a
  let U := ProjectiveSpectrum.basicOpen 𝒜 f
  have hloc (x : U) :=
    moduleSections_locally_degreeZeroToSection 𝒜 𝒨 U a x
  choose V hxV incl f' d' hd' hf' hVf b hb using hloc
  have hcover : U ≤ ⨆ x : U, V x := by
    intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  obtain ⟨n, g, e, hge, hUeq, hsub⟩ :=
    ProjectiveSpectrum.exists_finite_basicOpen_refinement 𝒜 hf hd V hcover
  choose x hxsub using hsub
  let hgf (i : Fin n) : ProjectiveSpectrum.basicOpen 𝒜 (g i) ≤ U := by
    show ProjectiveSpectrum.basicOpen 𝒜 (g i) ≤ ProjectiveSpectrum.basicOpen 𝒜 f
    rw [hUeq]
    exact le_iSup (fun i => ProjectiveSpectrum.basicOpen 𝒜 (g i)) i
  let fi (i : Fin n) := f' (x i)
  let di (i : Fin n) := d' (x i)
  let hdi (i : Fin n) : 0 < di i := hd' (x i)
  let hfi (i : Fin n) : fi i ∈ 𝒜 (di i) := hf' (x i)
  let hfig (i : Fin n) :
      ProjectiveSpectrum.basicOpen 𝒜 (g i) ≤ ProjectiveSpectrum.basicOpen 𝒜 (fi i) :=
    le_trans (hxsub i) (hVf (x i))
  let bi' (i : Fin n) := b (x i)
  let maps (i : Fin n) :=
    ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 (fi i) (g i)
      ⟨di i, hdi i, hfi i⟩ ⟨e i, (hge i).1, (hge i).2⟩ (hfig i)
  let bi (i : Fin n) := (maps i).degreeZeroMap (bi' i)
  let F := (associatedModuleSheaf 𝒜 𝒨).val
  have hbi (i : Fin n) :
      F.map (homOfLE (hgf i)).op a = degreeZeroToSection 𝒜 𝒨 (g i) (bi i) := by
    have hres := degreeZeroToSection_restriction 𝒜 𝒨 (fi i) (g i)
      ⟨di i, hdi i, hfi i⟩ ⟨e i, (hge i).1, (hge i).2⟩ (hfig i) (bi' i)
    apply Subtype.ext
    funext y
    exact (hb (x i) ⟨y.1, hxsub i y.2⟩).trans (congrFun (congrArg Subtype.val hres) y)
  have hlocal (i : Fin n) (y : ProjectiveSpectrum.top 𝒜)
      (hy : y ∈ ProjectiveSpectrum.basicOpen 𝒜 (g i)) :
      moduleToFiber (M := M) 𝒜 (g i) ⟨y, hy⟩ (bi i).1 = a.1 ⟨y, hgf i hy⟩ :=
    (congrFun (congrArg Subtype.val (hbi i)) ⟨y, hy⟩).symm
  have hcover : ProjectiveSpectrum.basicOpen 𝒜 f ≤
      ⨆ i : Fin n, ProjectiveSpectrum.basicOpen 𝒜 (g i) := by
    rw [hUeq]
  have hspan : Ideal.span (Set.range fun i : Fin n =>
      HomogeneousLocalization.Away.isLocalizationElem hf (hge i).2) = ⊤ :=
    (AlgebraicGeometry.Proj.basicOpen_le_iSup_iff_span_isLocalizationElem_eq_top
      𝒜 hf hd g e (fun i => (hge i).2) (fun i => (hge i).1)).mp hcover
  let u (i : Fin n) : HomogeneousLocalization.Away 𝒜 f :=
    HomogeneousLocalization.Away.isLocalizationElem hf (hge i).2
  have hF : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d := ⟨d, hd, hf⟩
  have hG (i : Fin n) : ∃ d : ℕ, 0 < d ∧ g i ∈ 𝒜 d := ⟨e i, (hge i).1, (hge i).2⟩
  let baseMaps (i : Fin n) := ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f (g i) hF (hG i) (hgf i)
  let (i : Fin n) : Algebra (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away 𝒜 (g i)) :=
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f (g i) hF (hG i) (hgf i)).toRingHom.toAlgebra
  let (i : Fin n) : Module (HomogeneousLocalization.Away 𝒜 f)
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 (g i)) :=
    Module.compHom (R := HomogeneousLocalization.Away 𝒜 (g i))
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 (g i))
      (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f (g i) hF (hG i) (hgf i)).toRingHom
  let q (i : Fin n) :=
    let φ₀ := ProjectiveSpectrum.degreeZeroRingMap 𝒜 f (g i) hF (hG i) (hgf i)
    let : Algebra (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 (g i)) := φ₀.toRingHom.toAlgebra
    let := Module.compHom (R := HomogeneousLocalization.Away 𝒜 (g i))
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 (g i)) φ₀.toRingHom
    (baseMaps i).degreeZeroMap
  have hq (i : Fin n) : IsLocalizedModule.Away (u i) (q i) := by
    show IsLocalizedModule
      (Submonoid.powers (HomogeneousLocalization.Away.mk 𝒜 hf (e i)
        ((g i) ^ d) (by simpa [mul_comm] using SetLike.pow_mem_graded d (hge i).2)))
      (baseMaps i).degreeZeroMap
    exact ProjectiveSpectrum.isLocalizedModule_degreeZeroMap
      𝒜 𝒨 f (g i) d (e i) hd (hge i).1 hf (hge i).2 (hgf i)
  let p (i j : Fin n) := g i * g j
  let pe (i j : Fin n) := e i + e j
  have hpe (i j : Fin n) : p i j ∈ 𝒜 (pe i j) :=
    SetLike.mul_mem_graded (hge i).2 (hge j).2
  have hpos (i j : Fin n) : 0 < pe i j := by
    have hi := (hge i).1
    dsimp [pe]
    omega
  have hP (i j : Fin n) : ∃ d : ℕ, 0 < d ∧ p i j ∈ 𝒜 d := ⟨pe i j, hpos i j, hpe i j⟩
  have hpi (i j : Fin n) :
      ProjectiveSpectrum.basicOpen 𝒜 (p i j) ≤ ProjectiveSpectrum.basicOpen 𝒜 (g i) := by
    rw [ProjectiveSpectrum.basicOpen_mul]
    exact inf_le_left
  have hpj (i j : Fin n) :
      ProjectiveSpectrum.basicOpen 𝒜 (p i j) ≤ ProjectiveSpectrum.basicOpen 𝒜 (g j) := by
    rw [ProjectiveSpectrum.basicOpen_mul]
    exact inf_le_right
  let prodMaps (i j : Fin n) :=
    ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f (p i j) hF (hP i j)
      (le_trans (hpi i j) (hgf i))
  let (i j : Fin n) : Algebra (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away 𝒜 (p i j)) :=
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f (p i j) hF (hP i j)
      (le_trans (hpi i j) (hgf i))).toRingHom.toAlgebra
  let (i j : Fin n) : Module (HomogeneousLocalization.Away 𝒜 f)
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 (p i j)) :=
    Module.compHom (R := HomogeneousLocalization.Away 𝒜 (p i j))
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 (p i j))
      (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f (p i j) hF (hP i j)
        (le_trans (hpi i j) (hgf i))).toRingHom
  let qp (i j : Fin n) :=
    let φ₀ := ProjectiveSpectrum.degreeZeroRingMap 𝒜 f (p i j) hF (hP i j)
      (le_trans (hpi i j) (hgf i))
    let : Algebra (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 (p i j)) := φ₀.toRingHom.toAlgebra
    let := Module.compHom (R := HomogeneousLocalization.Away 𝒜 (p i j))
      (GradedModuleDegreeZeroLocalization 𝒜 𝒨 (p i j)) φ₀.toRingHom
    (prodMaps i j).degreeZeroMap
  let uprod (i j : Fin n) :=
    HomogeneousLocalization.Away.isLocalizationElem hf (hpe i j)
  have hqp (i j : Fin n) : IsLocalizedModule.Away (uprod i j) (qp i j) := by
    show IsLocalizedModule
      (Submonoid.powers (HomogeneousLocalization.Away.mk 𝒜 hf (pe i j)
        ((p i j) ^ d) (by simpa [mul_comm] using SetLike.pow_mem_graded d (hpe i j))))
      (prodMaps i j).degreeZeroMap
    exact ProjectiveSpectrum.isLocalizedModule_degreeZeroMap
      𝒜 𝒨 f (p i j) d (pe i j) hd (hpos i j) hf (hpe i j) (le_trans (hpi i j) (hgf i))
  let l (i j : Fin n) :=
    degreeZeroRestrictionLinear 𝒜 𝒨 f (g i) (p i j) hF (hG i) (hP i j) (hgf i) (hpi i j)
  let rmap (i j : Fin n) :=
    degreeZeroRestrictionLinear 𝒜 𝒨 f (g j) (p i j) hF (hG j) (hP i j) (hgf j) (hpj i j)
  have huProd (i j : Fin n) : uprod i j = u i * u j := by
    apply HomogeneousLocalization.val_injective
    simp [uprod, u, p, pe, HomogeneousLocalization.Away.isLocalizationElem,
      HomogeneousLocalization.Away.val_mk, Localization.mk_mul, mul_pow, pow_add]
  have hcomp (i j k : Fin n)
      (hk : ProjectiveSpectrum.basicOpen 𝒜 (p i j) ≤ ProjectiveSpectrum.basicOpen 𝒜 (g k)) :
      (degreeZeroRestrictionLinear 𝒜 𝒨 f (g k) (p i j) hF (hG k) (hP i j) (hgf k) hk).comp
        (q k) = qp i j := by
    apply LinearMap.ext
    intro z
    show (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 (g k) (p i j) (hG k) (hP i j) hk
        |>.degreeZeroMap ((baseMaps k).degreeZeroMap z)) = (prodMaps i j).degreeZeroMap z
    apply Subtype.ext
    rw [(ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 (g k) (p i j) (hG k) (hP i j) hk
        ).degreeZeroMap_val, (baseMaps k).degreeZeroMap_val, (prodMaps i j).degreeZeroMap_val]
    exact congrArg (fun F => F z.1)
      (localizedRestrictionLinear_comp 𝒜 𝒨 f (g k) (p i j) hF (hG k) (hP i j) (hgf k) hk)
  have hcompatible (i j : Fin n) : l i j (bi i) = rmap i j (bi j) := by
    apply sub_eq_zero.mp
    apply degreeZeroLocalization_eq_zero_of_fibers 𝒜 𝒨 (hpe i j) (hpos i j)
      ((l i j (bi i)) - (rmap i j (bi j)))
    intro y
    have heval :
        moduleToFiber (M := M) 𝒜 (p i j) y ((l i j (bi i)).1) =
          moduleToFiber (M := M) 𝒜 (p i j) y ((rmap i j (bi j)).1) :=
      (moduleToFiber_degreeZeroMap 𝒜 𝒨 (g i) (p i j) (hG i) (hP i j) (hpi i j) y (bi i)).trans
        ((hlocal i y.1 (hpi i j y.2)).trans (hlocal j y.1 (hpj i j y.2)).symm) |>.trans
        (moduleToFiber_degreeZeroMap 𝒜 𝒨 (g j) (p i j) (hG j) (hP i j) (hpj i j) y (bi j)).symm
    show moduleToFiber (M := M) 𝒜 (p i j) y
      ((l i j (bi i)).1 - (rmap i j (bi j)).1) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr heval
  let : ∀ i j, IsLocalizedModule.Away (u i * u j)
      ((l i j).comp (q i)) := fun i j => by
    rw [← huProd i j, hcomp i j i (hpi i j)]
    exact hqp i j
  have hglue := IsLocalizedModule.Away.injective_pi_and_exact_of_span_range_eq_top
    (g := q) l rmap hspan (fun i j => (hcomp i j i (hpi i j)).trans (hcomp i j j (hpj i j)).symm)
  have hkernel :
      (LinearMap.pi fun p : Fin n × Fin n =>
        (l p.1 p.2).comp (LinearMap.proj p.1) -
          (rmap p.1 p.2).comp (LinearMap.proj p.2)) bi = 0 := by
    ext p
    simp only [LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    exact congrArg Subtype.val (sub_eq_zero.mpr (hcompatible p.1 p.2))
  have hmem : bi ∈ LinearMap.range (LinearMap.pi q) := by
    have hrange : LinearMap.range (LinearMap.pi q) =
        LinearMap.ker (LinearMap.pi fun p : Fin n × Fin n =>
          (l p.1 p.2).comp (LinearMap.proj p.1) -
            (rmap p.1 p.2).comp (LinearMap.proj p.2)) :=
      (LinearMap.exact_iff.mp hglue.2).symm
    rw [hrange]
    exact LinearMap.mem_ker.mpr hkernel
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hmem
  refine ⟨z, ?_⟩
  apply Subtype.ext
  funext y
  have hySup : y.1 ∈ ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (g i) := by
    rw [← hUeq]
    exact y.2
  obtain ⟨i, hiy⟩ := Opens.mem_iSup.mp hySup
  have hres := degreeZeroToSection_restriction 𝒜 𝒨 f (g i) hF (hG i) (hgf i) z
  have hz_i : q i z = bi i := by
    simpa only [LinearMap.pi_apply] using congrFun hz i
  have hrestrict :
      F.map (homOfLE (hgf i)).op (degreeZeroToSection 𝒜 𝒨 f z) =
        F.map (homOfLE (hgf i)).op a :=
    (hres.trans (congrArg (degreeZeroToSection 𝒜 𝒨 (g i)) hz_i)).trans (hbi i).symm
  exact congrArg (fun sec => sec.1 ⟨y.1, hiy⟩) hrestrict

/-- Sections over a standard open are a module over the degree-zero localization there. -/
public noncomputable instance associatedModuleSheafStandardOpenModule (f : S) :
    Module (HomogeneousLocalization.Away 𝒜 f)
      ((associatedModuleSheaf 𝒜 𝒨).val.obj (.op (ProjectiveSpectrum.basicOpen 𝒜 f))) :=
  standardOpenModule 𝒜 𝒨 f

/-- The canonical linear identification of sections on `D₊(f)` with `M_(f)`.
Its inverse is evaluation of a degree-zero fraction in every homogeneous-prime fiber. -/
@[stacks 01M6 "part (3), canonical linear identification on standard opens"]
public noncomputable def associatedModuleSheafStandardOpenEquiv {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (associatedModuleSheaf 𝒜 𝒨).val.obj (.op (ProjectiveSpectrum.basicOpen 𝒜 f))
      ≃ₗ[HomogeneousLocalization.Away 𝒜 f]
        GradedModuleDegreeZeroLocalization 𝒜 𝒨 f :=
  (LinearEquiv.ofBijective (degreeZeroToSection 𝒜 𝒨 f)
    ⟨degreeZeroToSection_injective 𝒜 𝒨 hf hd,
      degreeZeroToSection_surjective 𝒜 𝒨 hf hd⟩).symm

end AlgebraicGeometry.ProjectiveSpectrum.Proj
