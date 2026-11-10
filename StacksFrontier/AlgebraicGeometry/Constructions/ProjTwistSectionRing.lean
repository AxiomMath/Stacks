module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Stalk

/-!
# The graded ring of twisted global sections on `Proj`

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring and `X = Proj 𝒮`. Each homogeneous
element of degree `n` gives a global section of the twist `𝒪_X(n)`, and these assemble into a
homomorphism of graded rings

`S ⟶ ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))`.

The target is graded by the actual groups of global sections, with multiplication the pointwise
product of local fractions; that product is well defined because the product of two sections of
`𝒪(n)` and `𝒪(m)`, read as fractions at each point, is a section of `𝒪(n + m)`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGlobalSections`: the group
  `Γ(X, 𝒪_X(n))` of global sections of the `n`-th twist.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`: the global section of `𝒪_X(n)`
  determined by a homogeneous element of degree `n`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSectionHom`: that section map in a fixed
  degree, as an additive group homomorphism.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.GlobalSectionsRingMap`: the graded ring of twisted
  global sections, the canonical ring map into it, and the equations that characterize both.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.globalSectionsRingMap`: the canonical such datum.

## Implementation notes

The target is the direct sum of the honest global-section groups, not a completion or a
product. The graded-ring structure and the ring map are packaged in a structure together with
the equations characterizing them — the product is pointwise on local fractions, and the ring
map is in each degree the canonical map of Tag 0AG2 — rather than being exposed as bare data,
because those equations are what pin the choice down; a `GCommRing` instance on the family of
section groups is not unique as data, but it is unique once its multiplication is prescribed
pointwise.

Multiplication is defined through
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafSectionsEquiv`, which presents a
section of the associated sheaf as a function into the module fibers satisfying the local
fraction condition; `twistSections_mul_mem` checks that the pointwise product of two such
functions again satisfies it, with the common refinement of the two witnessing opens.

The graded-monoid laws are stated separately as the `cast` equations
`twistSectionsOne_mul_cast`, `twistSectionsMul_one_cast`, `twistSectionsMul_assoc_cast` and
`twistSectionsMul_comm_cast`, each proved by `twistSections_ext` from the corresponding law in
the fibers. They are split out of the `GCommRing` term, rather than being discharged inside it,
so that each is elaborated on its own: a single declaration carrying all of them is far beyond
the default heartbeat allowance, and the sheaf-valued types involved make the term large.

`degreeSectionHom` is stated with the additive-group structure that the sections of a sheaf of
modules carry; it is not a `𝒮 0`-linear map, because its source is `𝒮 n` rather than a module
over `𝒮 0` for `n` positive.

The `VAdd ℕ ℤ` instance, which `SetLike.GradedSMul 𝒮 𝒨` needs for an `ℕ`-graded ring acting on a
`ℤ`-graded module, is the scoped `Stacks.GradedLocalization.instVAddNatInt` — the one the
global-sections map was constructed with.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open scoped Stacks.GradedLocalization

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The degree-`n` component of the graded ring of twisted global sections: the global sections
of `𝒪_{Proj 𝒮}(n)`. -/
public abbrev twistGlobalSections (n : ℕ) : Type u :=
  (twistingSheaf 𝒮 (n : ℤ)).val.obj (op ⊤)

/-- The global section of `𝒪_{Proj 𝒮}(n)` determined by a homogeneous element of degree `n`. -/
public noncomputable def degreeSection (n : ℕ) (a : 𝒮 n) : twistGlobalSections 𝒮 n :=
  degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
    ⟨a.1, by simp [twistGrading, integerGrading, homogeneousSubmodule]⟩

/-- The graded ring of twisted global sections, its canonical ring map from `S`, and the
formulas that characterize them: the product is the pointwise product of local fractions, and
the ring map is in each degree the canonical map from the homogeneous elements. -/
public structure GlobalSectionsRingMap where
  /-- The graded-ring structure on the family of twisted global-section groups. -/
  gradedRing : DirectSum.GCommRing (twistGlobalSections 𝒮)
  /-- The canonical ring map `S → ⨁ₙ Γ(Proj 𝒮, 𝒪(n))`. -/
  hom : letI := gradedRing
    S →+* (⨁ n : ℕ, twistGlobalSections 𝒮 n)
  /-- On a homogeneous element of degree `n` the ring map is the canonical section. -/
  map_homogeneous : letI := gradedRing
    ∀ (n : ℕ) (a : 𝒮 n), hom a.1 =
      DirectSum.of (twistGlobalSections 𝒮) n (degreeSection 𝒮 n a)
  /-- The homogeneous product of sections is their pointwise product in each fiber. -/
  mul_sections : letI := gradedRing
    ∀ (n m : ℕ) (s : twistGlobalSections 𝒮 n) (t : twistGlobalSections 𝒮 m)
      (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))),
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 ((n + m : ℕ) : ℤ)) ⊤).toFun
          (GradedMonoid.GMul.mul s t)).1 x =
        ((associatedModuleSheafSectionsEquiv 𝒮
          (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s).1 x *
        ((associatedModuleSheafSectionsEquiv 𝒮
          (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤).toFun t).1 x

/-- The pointwise product of a section of `𝒪(n)` and a section of `𝒪(m)` is a section of
`𝒪(n + m)`: on the common refinement of the two witnessing opens the two local fractions
multiply. -/
public lemma twistSections_mul_mem (n m : ℕ)
    (s : moduleSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤)
    (t : moduleSections 𝒮 (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤) :
    (fun x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) => s.1 x * t.1 x) ∈
      moduleSections 𝒮 (twistGrading (S := S) 𝒮 ((n + m : ℕ) : ℤ)) ⊤ := by
  intro x
  obtain ⟨U, hxU, iU, p, a, b, ha, hb, hbU, hrep⟩ := s.2 x
  obtain ⟨V, hxV, iV, q, c, d, hc, hd, hdV, hrep'⟩ := t.2 x
  have key : ∀ (k l : ℕ) (e : S),
      e ∈ integerGrading (S := S) 𝒮 ((k : ℤ) + (l : ℤ)) ↔ e ∈ 𝒮 (k + l) := fun k l e => by
    rw [← Nat.cast_add, integerGrading_natCast]
    exact mem_homogeneousSubmodule 𝒮 (k + l) e
  have hb' : b ∈ 𝒮 p := hb
  have hd' : d ∈ 𝒮 q := hd
  have hac : a * c ∈ 𝒮 ((p + q) + (n + m)) := by
    convert SetLike.mul_mem_graded ((key p n a).1 ha) ((key q m c).1 hc) using 1
    congr 1
    omega
  have hout : a * c ∈ (twistGrading (S := S) 𝒮 ((n + m : ℕ) : ℤ)) (p + q : ℤ) :=
    (key (p + q) (n + m) _).2 hac
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, Opens.infLELeft _ _ ≫ iU, p + q, a * c, b * d, hout,
    SetLike.mul_mem_graded hb' hd', fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hbU ⟨y.1, y.2.1⟩) (hdV ⟨y.1, y.2.2⟩), fun y => ?_⟩
  change s.1 (iU (Opens.infLELeft U V y)) * t.1 (iV (Opens.infLERight U V y)) = _
  have hU := hrep (Opens.infLELeft U V y)
  have hV := hrep' (Opens.infLERight U V y)
  change s.1 (iU (Opens.infLELeft U V y)) = _ at hU
  change t.1 (iV (Opens.infLERight U V y)) = _ at hV
  rw [hU, hV]
  exact LocalizedModule.mk_mul_mk

/-- The product of a section of `𝒪(n)` and a section of `𝒪(m)`, as a section of `𝒪(n + m)`. -/
private noncomputable def twistSectionsMul (n m : ℕ) (s : twistGlobalSections 𝒮 n)
    (t : twistGlobalSections 𝒮 m) : twistGlobalSections 𝒮 (n + m) :=
  ((associatedModuleSheafSectionsEquiv 𝒮
    (twistGrading (S := S) 𝒮 ((n + m : ℕ) : ℤ)) ⊤).symm).toFun
      ⟨fun x =>
          ((associatedModuleSheafSectionsEquiv 𝒮
            (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s).1 x *
          ((associatedModuleSheafSectionsEquiv 𝒮
            (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤).toFun t).1 x,
        twistSections_mul_mem 𝒮 n m
          ((associatedModuleSheafSectionsEquiv 𝒮
            (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s)
          ((associatedModuleSheafSectionsEquiv 𝒮
            (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤).toFun t)⟩

private theorem twistSectionsMul_apply (n m : ℕ) (s : twistGlobalSections 𝒮 n)
    (t : twistGlobalSections 𝒮 m) (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    ((associatedModuleSheafSectionsEquiv 𝒮
      (twistGrading (S := S) 𝒮 ((n + m : ℕ) : ℤ)) ⊤).toFun
        (twistSectionsMul 𝒮 n m s t)).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s).1 x *
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤).toFun t).1 x := rfl

private theorem twistSections_add_apply (n : ℕ) (s t : twistGlobalSections 𝒮 n)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    ((associatedModuleSheafSectionsEquiv 𝒮
      (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun (s + t)).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s).1 x +
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun t).1 x := rfl

/-- The unit section of `𝒪(0)`, namely the one determined by `1 ∈ 𝒮 0`. -/
private noncomputable def twistSectionsOne : twistGlobalSections 𝒮 0 :=
  degreeSection 𝒮 0 ⟨1, SetLike.one_mem_graded 𝒮⟩

private theorem twistSections_ext {n : ℕ} {s t : twistGlobalSections 𝒮 n}
    (h : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)),
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun t).1 x) : s = t :=
  (associatedModuleSheafSectionsEquiv 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).injective
    (Subtype.ext (funext h))

/-- The global section of `𝒪(n)` attached to a homogeneous element of degree `n` has local
value the fraction `a / 1` at every point, read through
`associatedModuleSheafSectionsEquiv`.

This is `Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply` with the section
presented as a function into the module fibers, which is the shape the multiplication formulas
below rewrite with. -/
private theorem degreeSection_sectionsEquiv_apply (n : ℕ) (a : 𝒮 n)
    (x : ProjectiveSpectrum.top 𝒮) :
    ((associatedModuleSheafSectionsEquiv 𝒮
      (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun (degreeSection 𝒮 n a)).1
        ⟨x, show x ∈ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) from trivial⟩ =
      LocalizedModule.mk a.1 (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
  unfold degreeSection
  rw [← associatedModuleSheafStalkEquiv_germ 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) x ⊤
    (show x ∈ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) from trivial)
    (degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
      ⟨a.1, by simp [twistGrading, integerGrading, homogeneousSubmodule]⟩)]
  exact degreeZeroToGlobalSections_stalk 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) x
    ⟨a.1, by simp [twistGrading, integerGrading, homogeneousSubmodule]⟩

private theorem twistSectionDegree_mul (n m : ℕ) (a : 𝒮 n) (b : 𝒮 m) :
    twistSectionsMul 𝒮 n m (degreeSection 𝒮 n a) (degreeSection 𝒮 m b) =
      degreeSection 𝒮 (n + m) ⟨a.1 * b.1, SetLike.mul_mem_graded a.2 b.2⟩ := by
  refine twistSections_ext 𝒮 fun x => ?_
  rw [twistSectionsMul_apply, degreeSection_sectionsEquiv_apply,
    degreeSection_sectionsEquiv_apply, degreeSection_sectionsEquiv_apply]
  simp

private theorem twistSectionsCast_apply {n m : ℕ} (h : n = m) (s : twistGlobalSections 𝒮 n)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    ((associatedModuleSheafSectionsEquiv 𝒮 (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤).toFun
      (cast (congrArg (twistGlobalSections 𝒮) h) s)).1 x =
    ((associatedModuleSheafSectionsEquiv 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s).1 x := by
  cases h
  rfl

/-! ### The graded-monoid laws

Each law is proved on its own, by `twistSections_ext` from the corresponding law in the module
fibers; assembling them into the `GCommRing` term is then cheap. -/

private theorem twistSectionsMul_zero (n m : ℕ) (a : twistGlobalSections 𝒮 n) :
    twistSectionsMul 𝒮 n m a 0 = 0 := by
  refine twistSections_ext 𝒮 fun x => ?_
  rw [twistSectionsMul_apply]
  simp

private theorem twistSectionsZero_mul (n m : ℕ) (b : twistGlobalSections 𝒮 m) :
    twistSectionsMul 𝒮 n m 0 b = 0 := by
  refine twistSections_ext 𝒮 fun x => ?_
  rw [twistSectionsMul_apply]
  simp

private theorem twistSectionsMul_add (n m : ℕ) (a : twistGlobalSections 𝒮 n)
    (b c : twistGlobalSections 𝒮 m) :
    twistSectionsMul 𝒮 n m a (b + c) =
      twistSectionsMul 𝒮 n m a b + twistSectionsMul 𝒮 n m a c := by
  refine twistSections_ext 𝒮 fun x => ?_
  simp only [twistSectionsMul_apply, twistSections_add_apply]
  exact mul_add _ _ _

private theorem twistSectionsAdd_mul (n m : ℕ) (a b : twistGlobalSections 𝒮 n)
    (c : twistGlobalSections 𝒮 m) :
    twistSectionsMul 𝒮 n m (a + b) c =
      twistSectionsMul 𝒮 n m a c + twistSectionsMul 𝒮 n m b c := by
  refine twistSections_ext 𝒮 fun x => ?_
  simp only [twistSectionsMul_apply, twistSections_add_apply]
  exact add_mul _ _ _

private theorem twistSectionsOne_mul_cast (j : ℕ) (s : twistGlobalSections 𝒮 j) :
    cast (congrArg (twistGlobalSections 𝒮) (zero_add j))
      (twistSectionsMul 𝒮 0 j (twistSectionsOne 𝒮) s) = s := by
  refine twistSections_ext 𝒮 fun x => ?_
  rw [twistSectionsCast_apply (𝒮 := 𝒮) (h := zero_add j), twistSectionsMul_apply]
  simp only [twistSectionsOne]
  rw [degreeSection_sectionsEquiv_apply]
  simpa [LocalizedModule.mk, OreLocalization.one_def] using
    (one_mul (((associatedModuleSheafSectionsEquiv 𝒮
      (twistGrading (S := S) 𝒮 (j : ℤ)) ⊤).toFun s).1 x))

private theorem twistSectionsMul_one_cast (j : ℕ) (s : twistGlobalSections 𝒮 j) :
    cast (congrArg (twistGlobalSections 𝒮) (add_zero j))
      (twistSectionsMul 𝒮 j 0 s (twistSectionsOne 𝒮)) = s := by
  refine twistSections_ext 𝒮 fun x => ?_
  rw [twistSectionsCast_apply (𝒮 := 𝒮) (h := add_zero j), twistSectionsMul_apply]
  simp only [twistSectionsOne]
  rw [degreeSection_sectionsEquiv_apply]
  simpa [LocalizedModule.mk, OreLocalization.one_def] using
    (mul_one (((associatedModuleSheafSectionsEquiv 𝒮
      (twistGrading (S := S) 𝒮 (j : ℤ)) ⊤).toFun s).1 x))

private theorem twistSectionsMul_assoc_cast (i j k : ℕ) (a : twistGlobalSections 𝒮 i)
    (b : twistGlobalSections 𝒮 j) (c : twistGlobalSections 𝒮 k) :
    cast (congrArg (twistGlobalSections 𝒮) (add_assoc i j k))
      (twistSectionsMul 𝒮 (i + j) k (twistSectionsMul 𝒮 i j a b) c) =
      twistSectionsMul 𝒮 i (j + k) a (twistSectionsMul 𝒮 j k b c) := by
  refine twistSections_ext 𝒮 fun x => ?_
  rw [twistSectionsCast_apply (𝒮 := 𝒮) (h := add_assoc i j k), twistSectionsMul_apply,
    twistSectionsMul_apply, twistSectionsMul_apply, twistSectionsMul_apply]
  exact mul_assoc _ _ _

private theorem twistSectionsMul_comm_cast (i j : ℕ) (a : twistGlobalSections 𝒮 i)
    (b : twistGlobalSections 𝒮 j) :
    cast (congrArg (twistGlobalSections 𝒮) (add_comm i j)) (twistSectionsMul 𝒮 i j a b) =
      twistSectionsMul 𝒮 j i b a := by
  refine twistSections_ext 𝒮 fun x => ?_
  rw [twistSectionsCast_apply (𝒮 := 𝒮) (h := add_comm i j), twistSectionsMul_apply,
    twistSectionsMul_apply]
  exact mul_comm _ _

/-- Two elements of the graded-monoid sigma type are equal if their degrees agree and the
components agree after casting along the degree equality. -/
private theorem sigma_ext_of_cast_eq {i j : ℕ} (h : i = j) {a : twistGlobalSections 𝒮 i}
    {b : twistGlobalSections 𝒮 j} (hab : cast (congrArg (twistGlobalSections 𝒮) h) a = b) :
    (⟨i, a⟩ : GradedMonoid (twistGlobalSections 𝒮)) = ⟨j, b⟩ :=
  Sigma.ext h (heq_of_cast_eq _ hab)

/-- The family of twisted global-section groups, with the pointwise product of local
fractions, is a commutative graded ring. -/
@[instance_reducible] private noncomputable def twistSectionsGradedRing :
    DirectSum.GCommRing (twistGlobalSections 𝒮) := by
  letI : GradedMonoid.GMul (twistGlobalSections 𝒮) := ⟨fun {n m} => twistSectionsMul 𝒮 n m⟩
  letI : GradedMonoid.GOne (twistGlobalSections 𝒮) := ⟨twistSectionsOne 𝒮⟩
  exact
    { mul := fun {n m} => twistSectionsMul 𝒮 n m
      one := twistSectionsOne 𝒮
      mul_zero := fun {n m} a => twistSectionsMul_zero 𝒮 n m a
      zero_mul := fun {n m} b => twistSectionsZero_mul 𝒮 n m b
      mul_add := fun {n m} a b c => twistSectionsMul_add 𝒮 n m a b c
      add_mul := fun {n m} a b c => twistSectionsAdd_mul 𝒮 n m a b c
      one_mul := by
        rintro ⟨j, s⟩
        exact sigma_ext_of_cast_eq 𝒮 (zero_add j) (twistSectionsOne_mul_cast 𝒮 j s)
      mul_one := by
        rintro ⟨j, s⟩
        exact sigma_ext_of_cast_eq 𝒮 (add_zero j) (twistSectionsMul_one_cast 𝒮 j s)
      mul_assoc := by
        rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
        exact sigma_ext_of_cast_eq 𝒮 (add_assoc i j k) (twistSectionsMul_assoc_cast 𝒮 i j k a b c)
      mul_comm := by
        rintro ⟨i, a⟩ ⟨j, b⟩
        exact sigma_ext_of_cast_eq 𝒮 (add_comm i j) (twistSectionsMul_comm_cast 𝒮 i j a b)
      natCast := fun k => k • twistSectionsOne 𝒮
      natCast_zero := by simp
      natCast_succ := fun k => by simp [succ_nsmul]
      intCast := fun z => z • twistSectionsOne 𝒮
      intCast_ofNat := fun k => by simp
      intCast_negSucc_ofNat := by
        intro k
        change (-(↑(k + 1 : ℕ) : ℤ)) • twistSectionsOne 𝒮 = -((k + 1 : ℕ) • twistSectionsOne 𝒮)
        rw [neg_zsmul]
        simp only [natCast_zsmul] }

/-- The degree-`n` section map `𝒮 n → Γ(Proj 𝒮, 𝒪(n))`, as an additive group homomorphism. -/
public noncomputable def degreeSectionHom (n : ℕ) : 𝒮 n →+ twistGlobalSections 𝒮 n where
  toFun := degreeSection 𝒮 n
  map_zero' := by
    unfold degreeSection
    exact map_zero _
  map_add' := by
    intro a b
    unfold degreeSection
    change degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) ⟨↑a + ↑b, _⟩ = _
    rw [← map_add]
    congr 1

/-- `degreeSectionHom 𝒮 n` sends `a : 𝒮 n` to the degree-`n` section `degreeSection 𝒮 n a`. -/
@[simp] public theorem degreeSectionHom_apply (n : ℕ) (a : 𝒮 n) :
    degreeSectionHom 𝒮 n a = degreeSection 𝒮 n a := rfl

/-- **The canonical homomorphism of graded rings `S → ⨁_{n ≥ 0} Γ(Proj 𝒮, 𝒪(n))`.** Its
multiplication on sections is the pointwise product of local fractions, and in each degree it is
the canonical map from the homogeneous elements; those two formulas determine it. -/
@[stacks 01MP]
public noncomputable def globalSectionsRingMap : GlobalSectionsRingMap 𝒮 :=
  Classical.choice (by
    let : DirectSum.GCommRing (twistGlobalSections 𝒮) := twistSectionsGradedRing 𝒮
    let homAux : (⨁ n : ℕ, 𝒮 n) →+* (⨁ n : ℕ, twistGlobalSections 𝒮 n) :=
      DirectSum.toSemiring
        (fun n => (DirectSum.of (twistGlobalSections 𝒮) n).comp (degreeSectionHom 𝒮 n))
        (by
          rw [AddMonoidHom.comp_apply, DirectSum.one_def]
          change DirectSum.of (twistGlobalSections 𝒮) 0
            (degreeSection 𝒮 0 ⟨1, SetLike.one_mem_graded 𝒮⟩) =
              DirectSum.of (twistGlobalSections 𝒮) 0 (twistSectionsOne 𝒮)
          congr 1)
        (by
          intro n m a b
          change DirectSum.of (twistGlobalSections 𝒮) (n + m)
              (degreeSection 𝒮 (n + m)
                (@GradedMonoid.GMul.mul ℕ (fun i => 𝒮 i) _ _ _ _ a b)) =
            DirectSum.of (twistGlobalSections 𝒮) n (degreeSection 𝒮 n a) *
              DirectSum.of (twistGlobalSections 𝒮) m (degreeSection 𝒮 m b)
          rw [DirectSum.of_mul_of]
          congr 1
          exact (twistSectionDegree_mul 𝒮 n m a b).symm)
    refine ⟨{
      gradedRing := inferInstance
      hom := homAux.comp (DirectSum.decomposeRingEquiv 𝒮).toRingHom
      map_homogeneous := ?_
      mul_sections := fun n m s t x => twistSectionsMul_apply 𝒮 n m s t x }⟩
    intro n a
    change homAux ((DirectSum.decomposeRingEquiv 𝒮) a.1) = _
    change DirectSum.toSemiring _ _ _ (DirectSum.decompose 𝒮 a.1) = _
    rw [DirectSum.decompose_of_mem 𝒮 a.2, DirectSum.toSemiring_of]
    rfl)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
