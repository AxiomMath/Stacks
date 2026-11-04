module

public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.Homology.DoubleMappingCone
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiPresentations
public import StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
public import StacksFrontier.Homology.TwoTermComplex.LineBaseChange
public import StacksFrontier.RingTheory.CompleteIntersection.CotangentDeterminant
public import StacksFrontier.RingTheory.CompleteIntersection.NaiveCotangentPerfect
public import StacksFrontier.RingTheory.Different.Formula.LocalizedCompleteIntersection
public import StacksFrontier.RingTheory.Syntomic.ConormalRank
import all StacksFrontier.RingTheory.CompleteIntersection.NaiveCotangentPerfect
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The determinant of the naive cotangent complex of a syntomic algebra

Let `A → B` be syntomic. The naive cotangent complex `NL_{B/A}` is a perfect object of `D(B)` of
Tor-amplitude in `[-1, 0]`, so it has a determinant `det(NL_{B/A})`, an invertible `B`-module
(More on Algebra, Section 0FJI). When `B` is moreover quasi-finite over `A` the complex has rank
zero and the determinant carries the canonical element `δ(NL_{B/A})`. This file names the two,
computes them on any finite family of generators with finite projective conormal module, and
gives the local generator of Stacks, Remark 0FKC, on the presentations
`B ≅ A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` of Stacks, Section 0BWH.

## Main definitions

* `Stacks.TateMap.detNL A B`: the invertible `B`-module `det(NL_{B/A})`, the value of the
  determinant functor `TwoTermDeterminant.det` at `NL_{B/A}`.
* `Stacks.TateMap.deltaNL A B`: the canonical element `δ(NL_{B/A})`.
* `Stacks.TateMap.nlPresentation`: the two-term presentation `I/I² → ⨁ᵢ B dxᵢ` of `NL_{B/A}`
  given by a finite family of generators.
* `Stacks.TateMap.detNLEquiv`: the resulting identification of `det(NL_{B/A})` with the
  determinant line of `I/I² → ⨁ᵢ B dxᵢ`.

## Main results

* `Stacks.TateMap.detNLEquiv_deltaNL`: that identification carries `δ(NL_{B/A})` to the
  canonical element of the determinant line.
* `Stacks.TateMap.exists_basis_deltaNL_eq_jacobian`: on a square pre-submersive presentation,
  `det(NL_{B/A})` is free on a generator `g` with `δ(NL_{B/A}) = J · g`, `J` the Jacobian.
* `Stacks.TateMap.exists_basis_deltaNL_eq_jacobianDet`: the same for
  `B ≅ A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` with `J = det(∂f_i/∂x_j)`.

## Implementation notes

A two-term complex `d : X₁ → X₀` is modelled in `D(B)` by the mapping cone of `d` read as a map of
complexes in degree `0`, `Stacks.TateMap.cone`, which is the model `NL_{B/A}` itself is defined
with. The identification of `NL(P)` with `NL_{B/A}` is the image in `D(B)` of the comparison map
of Stacks 00S1 with the canonical presentation, an isomorphism because that map is a homotopy
equivalence; homotopic chain maps have the same image, so the identification does not depend on
the morphism of presentations used.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
* [Stacks Project, Remark 0FKC](https://stacks.math.columbia.edu/tag/0FKC)
* [Stacks Project, Section 15.87 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.TateMap

attribute [local instance] HasDerivedCategory.standard

/-! ### The cochain model of a two-term complex -/

section Cone

variable {R : Type u} [CommRing R]

attribute [local implicit_reducible] CochainComplex.mappingCone

/-- A two-term complex `d : X₁ → X₀` of `R`-modules as a cochain complex in degrees `-1` and
`0`: the mapping cone of `d` regarded as a map of complexes concentrated in degree `0`. -/
abbrev cone (T : NaiveCotangent.TwoTerm.{u, u, u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (ModuleCat.ofHom T.d))

/-- The map of cochain models induced by a chain map of two-term complexes. -/
def coneMap {T T' : NaiveCotangent.TwoTerm.{u, u, u} R} (f : NaiveCotangent.ChainMap T T') :
    cone T ⟶ cone T' :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (ModuleCat.ofHom f.f₁))
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (ModuleCat.ofHom f.f₀))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact ModuleCat.hom_ext f.comm.symm)

/-- Homotopic chain maps of two-term complexes induce the same morphism in the derived
category. -/
theorem Q_map_coneMap_eq_of_homotopic {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    {f g : NaiveCotangent.ChainMap T T'} (h : NaiveCotangent.Homotopic f g) :
    DerivedCategory.Q.map (coneMap f) = DerivedCategory.Q.map (coneMap g) := by
  obtain ⟨k, hk₁, hk₀⟩ := h
  let S := CochainComplex.singleFunctor (ModuleCat.{u} R) 0
  have h₁ : S.map (ModuleCat.ofHom f.f₁) - S.map (ModuleCat.ofHom g.f₁) =
      S.map (ModuleCat.ofHom T.d) ≫ S.map (ModuleCat.ofHom k) := by
    rw [← S.map_comp, ← S.map_sub]
    congr 1
    exact ModuleCat.hom_ext (by simpa using hk₁)
  have h₀ : S.map (ModuleCat.ofHom f.f₀) - S.map (ModuleCat.ofHom g.f₀) =
      S.map (ModuleCat.ofHom k) ≫ S.map (ModuleCat.ofHom T'.d) := by
    rw [← S.map_comp, ← S.map_sub]
    congr 1
    exact ModuleCat.hom_ext (by simpa using hk₀)
  exact DerivedCategory.Q_map_eq_of_homotopy _
    (NaiveCotangent.mappingConeMapHomotopy _ _ _ _ _ _ _ _ _ h₁ h₀)

/-- A homotopy equivalence of two-term complexes induces an isomorphism in the derived
category. -/
theorem isIso_Q_map_coneMap {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    {f : NaiveCotangent.ChainMap T T'} (hf : NaiveCotangent.IsHomotopyEquiv f) :
    IsIso (DerivedCategory.Q.map (coneMap f)) := by
  obtain ⟨g, ⟨h, h₁, h₀⟩, ⟨k, k₁, k₀⟩⟩ := hf
  let S := CochainComplex.singleFunctor (ModuleCat.{u} R) 0
  refine (DerivedCategory.isIso_Q_map_iff_quasiIso _ (coneMap f)).2
    (NaiveCotangent.mappingConeHomotopyEquiv
      (S.map (ModuleCat.ofHom T.d)) (S.map (ModuleCat.ofHom T'.d))
      (S.map (ModuleCat.ofHom f.f₁)) (S.map (ModuleCat.ofHom f.f₀))
      (S.map (ModuleCat.ofHom g.f₁)) (S.map (ModuleCat.ofHom g.f₀)) ?_ ?_
      (S.map (ModuleCat.ofHom h)) (S.map (ModuleCat.ofHom k)) ?_ ?_ ?_ ?_).quasiIso_hom
  · rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact ModuleCat.hom_ext f.comm.symm
  · rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact ModuleCat.hom_ext g.comm.symm
  all_goals
    rw [← S.map_comp, ← S.map_id, ← S.map_sub, ← S.map_comp]
    congr 1
    refine ModuleCat.hom_ext ?_
  · simpa [NaiveCotangent.ChainMap.comp, NaiveCotangent.ChainMap.id] using h₁
  · simpa [NaiveCotangent.ChainMap.comp, NaiveCotangent.ChainMap.id] using h₀
  · simpa [NaiveCotangent.ChainMap.comp, NaiveCotangent.ChainMap.id] using k₁
  · simpa [NaiveCotangent.ChainMap.comp, NaiveCotangent.ChainMap.id] using k₀

/-- Degree `-1` of the cochain model of a two-term complex is its source. -/
def coneNegOneIso (T : NaiveCotangent.TwoTerm.{u, u, u} R) :
    ModuleCat.of R T.X₁ ≅ (cone T).X (-1) :=
  HomologicalComplex.singleConeNegOneIso (ModuleCat.ofHom T.d)

/-- Degree `0` of the cochain model of a two-term complex is its target. -/
def coneZeroIso (T : NaiveCotangent.TwoTerm.{u, u, u} R) :
    ModuleCat.of R T.X₀ ≅ (cone T).X 0 :=
  HomologicalComplex.singleConeZeroIso (ModuleCat.ofHom T.d)

/-- The differential of the cochain model of a two-term complex is its differential. -/
theorem cone_d_comm (T : NaiveCotangent.TwoTerm.{u, u, u} R) :
    T.d ∘ₗ (coneNegOneIso T).symm.toLinearEquiv.toLinearMap =
      (coneZeroIso T).symm.toLinearEquiv.toLinearMap ∘ₗ ((cone T).d (-1) 0).hom := by
  have h := HomologicalComplex.singleCone_d (ModuleCat.ofHom T.d)
  have h' : (cone T).d (-1) 0 ≫ (coneZeroIso T).inv =
      (coneNegOneIso T).inv ≫ ModuleCat.ofHom T.d := by
    rw [Iso.eq_inv_comp, ← Category.assoc]
    exact (h.trans (by rfl)).symm ▸ (by simp [coneZeroIso])
  exact (congrArg ModuleCat.Hom.hom h').symm

/-- In degree `-1` the cochain model of a chain map is its degree-one component. -/
theorem coneNegOneIso_hom_coneMap_f {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    (g : NaiveCotangent.ChainMap T T') :
    (coneNegOneIso T).hom ≫ (coneMap g).f (-1) =
      ModuleCat.ofHom g.f₁ ≫ (coneNegOneIso T').hom := by
  simp only [coneNegOneIso, HomologicalComplex.singleConeNegOneIso, coneMap,
    CochainComplex.mappingCone.map, Category.assoc]
  have e (U : NaiveCotangent.TwoTerm.{u, u, u} R) :
      HomologicalComplex.homotopyCofiber.inlX (HomologicalComplex.singleMap (ModuleCat.ofHom U.d))
        0 (-1) (by decide) =
      (CochainComplex.mappingCone.inl ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom U.d))).v 0 (-1) (by omega) := rfl
  rw [e, e, CochainComplex.mappingCone.inl_v_desc_f]
  simp only [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  change _ ≫ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map _).f 0 ≫ _ = _
  rw [HomologicalComplex.single_map_f_self]
  simp

/-- In degree `0` the cochain model of a chain map is its degree-zero component. -/
theorem coneZeroIso_hom_coneMap_f {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    (g : NaiveCotangent.ChainMap T T') :
    (coneZeroIso T).hom ≫ (coneMap g).f 0 =
      ModuleCat.ofHom g.f₀ ≫ (coneZeroIso T').hom := by
  simp only [coneZeroIso, HomologicalComplex.singleConeZeroIso, coneMap,
    CochainComplex.mappingCone.map, Category.assoc]
  have e (U : NaiveCotangent.TwoTerm.{u, u, u} R) :
      HomologicalComplex.homotopyCofiber.inrX (HomologicalComplex.singleMap (ModuleCat.ofHom U.d))
        0 =
      (CochainComplex.mappingCone.inr ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom U.d))).f 0 := rfl
  rw [e, e, CochainComplex.mappingCone.inr_f_desc_f]
  change _ ≫ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map _).f 0 ≫ _ = _
  rw [HomologicalComplex.single_map_f_self]
  simp

/-- The cochain model of a two-term complex vanishes outside degrees `-1` and `0`. -/
theorem isZero_cone_X (T : NaiveCotangent.TwoTerm.{u, u, u} R) (i : ℤ) (h₁ : i ≠ -1)
    (h₀ : i ≠ 0) : IsZero ((cone T).X i) := by
  refine (CochainComplex.mappingCone.isZero_X_iff _ i).2 ⟨?_, ?_⟩ <;>
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- The differential of the cochain model, elementwise. -/
theorem cone_d_coneNegOneIso_hom (T : NaiveCotangent.TwoTerm.{u, u, u} R) (y : T.X₁) :
    (cone T).d (-1) 0 ((coneNegOneIso T).hom y) = (coneZeroIso T).hom (T.d y) :=
  ConcreteCategory.congr_hom (HomologicalComplex.singleCone_d (ModuleCat.ofHom T.d)) y

/-- A quasi-isomorphism of two-term complexes gives a quasi-isomorphism of cochain models. -/
theorem quasiIso_coneMap {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    {g : NaiveCotangent.ChainMap T T'} (hg : NaiveCotangent.IsQuasiIso g) :
    QuasiIso (coneMap g) := by
  have f₁ (y : T.X₁) : (coneMap g).f (-1) ((coneNegOneIso T).hom y) =
      (coneNegOneIso T').hom (g.f₁ y) := by
    rw [← ConcreteCategory.comp_apply, coneNegOneIso_hom_coneMap_f, ConcreteCategory.comp_apply]
    rfl
  have f₀ (y : T.X₀) : (coneMap g).f 0 ((coneZeroIso T).hom y) =
      (coneZeroIso T').hom (g.f₀ y) := by
    rw [← ConcreteCategory.comp_apply, coneZeroIso_hom_coneMap_f, ConcreteCategory.comp_apply]
    rfl
  have b₁ (U : NaiveCotangent.TwoTerm.{u, u, u} R) : Function.Bijective (coneNegOneIso U).hom :=
    ConcreteCategory.bijective_of_isIso _
  have b₀ (U : NaiveCotangent.TwoTerm.{u, u, u} R) : Function.Bijective (coneZeroIso U).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine CochainComplex.quasiIso_of_isZero_X_of_bijective _ (isZero_cone_X T) (isZero_cone_X T')
    ?_ ?_ ?_ ?_
  · intro x hx hgx
    obtain ⟨y, rfl⟩ := (b₁ T).2 x
    rw [cone_d_coneNegOneIso_hom] at hx
    rw [f₁] at hgx
    have : (⟨y, (map_eq_zero_iff _ (b₀ T).1).1 hx⟩ : NaiveCotangent.H₁ T) = 0 :=
      hg.1.1 (Subtype.ext (by
        simpa [NaiveCotangent.onH₁_coe] using (map_eq_zero_iff _ (b₁ T').1).1 hgx))
    rw [show y = 0 from congrArg Subtype.val this, map_zero]
  · intro x hx
    obtain ⟨y, rfl⟩ := (b₁ T').2 x
    rw [cone_d_coneNegOneIso_hom] at hx
    obtain ⟨⟨z, hz⟩, hzy⟩ := hg.1.2 ⟨y, (map_eq_zero_iff _ (b₀ T').1).1 hx⟩
    refine ⟨(coneNegOneIso T).hom z, ?_, ?_⟩
    · rw [cone_d_coneNegOneIso_hom, show T.d z = 0 from hz, map_zero]
    · rw [f₁]
      exact congrArg _ (congrArg Subtype.val hzy)
  · intro x ⟨m, hm⟩
    obtain ⟨y, rfl⟩ := (b₀ T).2 x
    obtain ⟨m', rfl⟩ := (b₁ T').2 m
    rw [cone_d_coneNegOneIso_hom, f₀] at hm
    have h0 : g.onH₀ ((LinearMap.range T.d).mkQ y) = 0 :=
      (NaiveCotangent.onH₀_mkQ g y).trans
        ((Submodule.Quotient.mk_eq_zero _).2 ⟨m', (b₀ T').1 hm⟩)
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).1 (hg.2.1 (h0.trans (map_zero _).symm))
    exact ⟨(coneNegOneIso T).hom z, by rw [cone_d_coneNegOneIso_hom, hz]⟩
  · intro x
    obtain ⟨y, rfl⟩ := (b₀ T').2 x
    obtain ⟨m, z, hmz⟩ := NaiveCotangent.exists_add_d_of_surjective_onH₀ g hg.2.2 y
    refine ⟨(coneZeroIso T).hom m, (coneNegOneIso T').hom z, ?_⟩
    rw [f₀, cone_d_coneNegOneIso_hom, ← map_add, hmz]

end Cone


/-! ### Two-term presentations from two-term complexes -/

section Presentation

variable {R : Type u} [CommRing R]

/-- The cochain model of a two-term complex of finite projective modules is bounded in
`[-1, 0]` with finite projective terms. -/
theorem cone_finite_projective (T : NaiveCotangent.TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀] :
    (cone T).IsStrictlyGE (-1) ∧ (cone T).IsStrictlyLE 0 ∧
      (∀ i, Module.Finite R ((cone T).X i)) ∧ (∀ i, Module.Projective R ((cone T).X i)) :=
  NaiveCotangent.twoTermComplex_finite_projective T.d

/-- Each term of the cochain model of a two-term complex of finite projective modules is
finite. -/
instance cone_X_finite (T : NaiveCotangent.TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀] (i : ℤ) :
    Module.Finite R ((cone T).X i) :=
  (cone_finite_projective T).2.2.1 i

/-- Each term of the cochain model of a two-term complex of finite projective modules is
projective. -/
instance cone_X_projective (T : NaiveCotangent.TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀] (i : ℤ) :
    Module.Projective R ((cone T).X i) :=
  (cone_finite_projective T).2.2.2 i

/-- A two-term complex of finite projective modules, identified with a derived object, is a
two-term presentation of it. -/
def conePresentation (T : NaiveCotangent.TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀]
    {K : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ DerivedCategory.Q.obj (cone T)) :
    TwoTermDeterminant.TwoTermPresentation K where
  complex := cone T
  finite := (cone_finite_projective T).2.2.1
  projective := (cone_finite_projective T).2.2.2
  strictlyGE := (cone_finite_projective T).1
  strictlyLE := (cone_finite_projective T).2.1
  iso := e

/-- A derived object with a two-term presentation is perfect of Tor-amplitude in `[-1, 0]`. -/
theorem perfectTwoTermComplexProperty_of_presentation {K : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermDeterminant.TwoTermPresentation K) :
    TwoTermDeterminant.perfectTwoTermComplexProperty R K := by
  have := P.strictlyGE
  have := P.strictlyLE
  refine ⟨⟨P.complex, -1, 0, P.strictlyGE, P.strictlyLE, P.finite, P.projective, ⟨P.iso⟩⟩,
    P.complex, fun i => ?_, P.strictlyGE, P.strictlyLE, ⟨P.iso⟩⟩
  have := P.projective i
  infer_instance

end Presentation

/-! ### The naive cotangent complex of a finite presentation -/

section NL

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The comparison `NL(P) → NL_{B/A}` of the naive cotangent complex of a family of generators
with the one of the canonical presentation. -/
def nlCanonicalMap {ι : Type} (P : Algebra.Generators A B ι) :
    NaiveCotangent.ChainMap (NaiveCotangent.NL P)
      (NaiveCotangent.NL (NaiveCotangent.canonicalGenerators A B)) :=
  NaiveCotangent.nlMap P _ (P.defaultHom _)

/-- The comparison `nlCanonicalMap` becomes an isomorphism in the derived category. -/
instance isIso_Q_map_coneMap_nlCanonicalMap {ι : Type} (P : Algebra.Generators A B ι) :
    IsIso (DerivedCategory.Q.map (coneMap (nlCanonicalMap A B P))) :=
  isIso_Q_map_coneMap (NaiveCotangent.nlMap_isHomotopyEquiv_and_isQuasiIso
    (by simpa using Function.bijective_id) (by simpa using Function.bijective_id) P _ _).1

/-- The naive cotangent complex `NL_{B/A}` is computed by the two-term complex
`I/I² → ⨁ᵢ B dxᵢ` of any family of generators. -/
def nlConeIso {ι : Type} (P : Algebra.Generators A B ι) :
    DerivedCategory.Q.obj (cone (NaiveCotangent.NL P)) ≅
      NaiveCotangent.naiveCotangentObject A B :=
  asIso (DerivedCategory.Q.map (coneMap (nlCanonicalMap A B P)))

/-- For a finite family of generators with finite projective conormal module, the two-term
complex `I/I² → ⨁ᵢ B dxᵢ` is a two-term presentation of `NL_{B/A}`. -/
def nlPresentation {ι : Type} [Finite ι] (P : Algebra.Generators A B ι)
    [Module.Finite B P.toExtension.Cotangent] [Module.Projective B P.toExtension.Cotangent] :
    TwoTermDeterminant.TwoTermPresentation (NaiveCotangent.naiveCotangentObject A B) :=
  haveI : Module.Finite B (NaiveCotangent.NL P).X₁ :=
    ‹Module.Finite B P.toExtension.Cotangent›
  haveI : Module.Projective B (NaiveCotangent.NL P).X₁ :=
    ‹Module.Projective B P.toExtension.Cotangent›
  haveI : Module.Finite B (NaiveCotangent.NL P).X₀ :=
    Algebra.Generators.finite_cotangentSpace P
  haveI : Module.Projective B (NaiveCotangent.NL P).X₀ :=
    Module.Projective.of_basis P.cotangentSpaceBasis
  conePresentation (NaiveCotangent.NL P) (nlConeIso A B P).symm

/-- A syntomic algebra has a finite family of generators with finite projective conormal
module. -/
theorem exists_generators_finite_projective [Algebra.Syntomic A B] :
    ∃ (n : ℕ) (P : Algebra.Generators A B (Fin n)),
      Module.Finite B P.toExtension.Cotangent ∧ Module.Projective B P.toExtension.Cotangent := by
  obtain ⟨n, f, hf, -⟩ := Algebra.FinitePresentation.out (R := A) (A := B)
  have heval : MvPolynomial.aeval (fun i : Fin n => f (MvPolynomial.X i)) = f := by
    ext i
    simp
  let P : Algebra.Generators A B (Fin n) :=
    Algebra.Generators.ofSurjective (fun i => f (MvPolynomial.X i)) (by rwa [heval])
  have hlci : RingHom.IsLocalCompleteIntersection (algebraMap A B) :=
    (NaiveCotangent.hasTorAmplitude_tfae_syntomic A B (Algebra.Syntomic A B) (by simp)
      (RingHom.IsLocalCompleteIntersection (algebraMap A B)) (by simp)).mp
      ‹Algebra.Syntomic A B›
  exact ⟨n, P, P.cotangent_finite_projective_of_isLocalCompleteIntersection hlci⟩

/-- The naive cotangent complex of a syntomic algebra is perfect of Tor-amplitude `[-1, 0]`. -/
@[sga "6 0 4.3" "special case", sga "6 0 4.4" "special case"]
theorem perfectTwoTermComplexProperty_naiveCotangentObject [Algebra.Syntomic A B] :
    TwoTermDeterminant.perfectTwoTermComplexProperty B
      (NaiveCotangent.naiveCotangentObject A B) := by
  obtain ⟨n, P, h₁, h₂⟩ := exists_generators_finite_projective A B
  exact perfectTwoTermComplexProperty_of_presentation (nlPresentation A B P)

/-- `NL_{B/A}` of a syntomic algebra, as a perfect object of `D(B)` of Tor-amplitude
`[-1, 0]`. -/
def nlObject [Algebra.Syntomic A B] : TwoTermDeterminant.PerfectTwoTermComplex B :=
  ⟨NaiveCotangent.naiveCotangentObject A B,
    perfectTwoTermComplexProperty_naiveCotangentObject A B⟩

/-- **The determinant `det(NL_{B/A})`** of the naive cotangent complex of a syntomic algebra:
the value at `NL_{B/A}` of the determinant functor of More on Algebra, Section 0FJI. -/
def detNL [Algebra.Syntomic A B] : Type u :=
  ((TwoTermDeterminant.det B).obj ⟨nlObject A B⟩).of.obj

/-- The additive group structure on `det(NL_{B/A})`. -/
instance [Algebra.Syntomic A B] : AddCommGroup (detNL A B) :=
  inferInstanceAs (AddCommGroup ((TwoTermDeterminant.det B).obj ⟨nlObject A B⟩).of.obj)

/-- The `B`-module structure on `det(NL_{B/A})`. -/
instance [Algebra.Syntomic A B] : Module B (detNL A B) :=
  inferInstanceAs (Module B ((TwoTermDeterminant.det B).obj ⟨nlObject A B⟩).of.obj)

/-- `det(NL_{B/A})` is an invertible `B`-module. -/
instance [Algebra.Syntomic A B] : Module.Invertible B (detNL A B) :=
  ((TwoTermDeterminant.det B).obj ⟨nlObject A B⟩).of.property

/-- **The canonical element `δ(NL_{B/A})`** of the determinant of the naive cotangent complex of
a quasi-finite syntomic algebra, which has rank zero. -/
def deltaNL [Algebra.Syntomic A B] [Algebra.QuasiFinite A B] : detNL A B :=
  TwoTermDeterminant.delta (nlObject A B)
    Algebra.isRankZero_naiveCotangentObject_of_quasiFinite_syntomic

end NL

/-! ### `det(NL_{B/A})` on a finite family of generators -/

section Generators

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {ι : Type} [Finite ι] (P : Algebra.Generators A B ι)
variable [Module.Finite B P.toExtension.Cotangent] [Module.Projective B P.toExtension.Cotangent]

/-- The cotangent space of a family of generators is a projective module. -/
instance : Module.Projective B P.toExtension.CotangentSpace :=
  Module.Projective.of_basis P.cotangentSpaceBasis

/-- Degree `-1` of the cochain model of `NL(P)` is the conormal module. -/
def nlConeNegOneEquiv :
    (cone (NaiveCotangent.NL P)).X (-1) ≃ₗ[B] P.toExtension.Cotangent :=
  (coneNegOneIso (NaiveCotangent.NL P)).symm.toLinearEquiv

/-- Degree `0` of the cochain model of `NL(P)` is the cotangent space. -/
def nlConeZeroEquiv :
    (cone (NaiveCotangent.NL P)).X 0 ≃ₗ[B] P.toExtension.CotangentSpace :=
  (coneZeroIso (NaiveCotangent.NL P)).symm.toLinearEquiv

omit [Finite ι] [Module.Finite B P.toExtension.Cotangent]
  [Module.Projective B P.toExtension.Cotangent] in
/-- Under `nlConeNegOneEquiv` and `nlConeZeroEquiv`, the differential of the cochain model of
`NL(P)` is the map `I/I² → ⨁ᵢ B dxᵢ`. -/
theorem nlCone_d_comm :
    P.toExtension.cotangentComplex ∘ₗ (nlConeNegOneEquiv P).toLinearMap =
      (nlConeZeroEquiv P).toLinearMap ∘ₗ ((cone (NaiveCotangent.NL P)).d (-1) 0).hom :=
  cone_d_comm (NaiveCotangent.NL P)

/-- The conormal module `NL(P).X₁` is a finite module. -/
instance : Module.Finite B (NaiveCotangent.NL P).X₁ :=
  ‹Module.Finite B P.toExtension.Cotangent›

/-- The conormal module `NL(P).X₁` is a projective module. -/
instance : Module.Projective B (NaiveCotangent.NL P).X₁ :=
  ‹Module.Projective B P.toExtension.Cotangent›

/-- The cotangent space `NL(P).X₀` is a finite module. -/
instance : Module.Finite B (NaiveCotangent.NL P).X₀ :=
  Algebra.Generators.finite_cotangentSpace P

/-- The cotangent space `NL(P).X₀` is a projective module. -/
instance : Module.Projective B (NaiveCotangent.NL P).X₀ :=
  Module.Projective.of_basis P.cotangentSpaceBasis

/-- Degree `-1` of the cochain model of `NL(P)` is a finite module. -/
instance : Module.Finite B ((cone (NaiveCotangent.NL P)).X (-1)) :=
  Module.Finite.equiv (nlConeNegOneEquiv P).symm

/-- Degree `-1` of the cochain model of `NL(P)` is a projective module. -/
instance : Module.Projective B ((cone (NaiveCotangent.NL P)).X (-1)) :=
  Module.Projective.of_equiv (nlConeNegOneEquiv P).symm

/-- Degree `0` of the cochain model of `NL(P)` is a finite module. -/
instance : Module.Finite B ((cone (NaiveCotangent.NL P)).X 0) :=
  Module.Finite.equiv (nlConeZeroEquiv P).symm

/-- Degree `0` of the cochain model of `NL(P)` is a projective module. -/
instance : Module.Projective B ((cone (NaiveCotangent.NL P)).X 0) :=
  Module.Projective.of_equiv (nlConeZeroEquiv P).symm

/-- The identification of `det(NL_{B/A})` with the determinant line of the two-term complex
`I/I² → ⨁ᵢ B dxᵢ` of a finite family of generators with finite projective conormal module. -/
def detNLEquiv [Algebra.Syntomic A B] :
    detNL A B ≃ₗ[B] TwoTermComplex.determinantLine P.toExtension.cotangentComplex :=
  (TwoTermDeterminant.detPresentationIso (nlObject A B) (nlPresentation A B P)).trans
    (TwoTermComplex.lineCongr ((cone (NaiveCotangent.NL P)).d (-1) 0).hom
      P.toExtension.cotangentComplex
      (nlConeNegOneEquiv P) (nlConeZeroEquiv P))

/-- The identification `detNLEquiv` carries `δ(NL_{B/A})` to the canonical element of the
determinant line of `I/I² → ⨁ᵢ B dxᵢ`. -/
theorem detNLEquiv_deltaNL [Algebra.Syntomic A B] [Algebra.QuasiFinite A B]
    (hP : TwoTermComplex.IsRankZero P.toExtension.cotangentComplex) :
    detNLEquiv P (deltaNL A B) = TwoTermComplex.delta P.toExtension.cotangentComplex hP := by
  have hT : TwoTermComplex.IsRankZero ((cone (NaiveCotangent.NL P)).d (-1) 0).hom := fun p =>
    ((ProjectiveDeterminant.rankAtStalk_congr (nlConeNegOneEquiv P) p).trans (hP p)).trans
      (ProjectiveDeterminant.rankAtStalk_congr (nlConeZeroEquiv P) p).symm
  refine (congrArg (TwoTermComplex.lineCongr ((cone (NaiveCotangent.NL P)).d (-1) 0).hom
    P.toExtension.cotangentComplex (nlConeNegOneEquiv P) (nlConeZeroEquiv P))
    (TwoTermDeterminant.detPresentationIso_delta (nlObject A B) (nlPresentation A B P) hT)).trans ?_
  exact TwoTermComplex.lineCongr_delta _ _ _ _ (nlCone_d_comm P) hT hP

end Generators

/-! ### The local generator on a square presentation -/

section Jacobian

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- For a pre-submersive presentation with as many relations as variables whose relation `i`
is attached to the variable `i`, the Jacobian matrix of Stacks 0FKC has the Jacobian of the
presentation as determinant. -/
theorem det_relationJacobiMatrix_eq_jacobian {m : ℕ}
    (Q : Algebra.PreSubmersivePresentation A B (Fin m) (Fin m)) (hQ : ∀ i, Q.map i = i) :
    Q.toPresentation.relationJacobiMatrix.det = Q.jacobian := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, RingHom.map_det]
  congr 1
  ext i j
  rw [Algebra.Presentation.relationJacobiMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hQ, Algebra.Generators.algebraMap_apply]

/-- **The local generator of `det(NL_{B/A})`.** For a quasi-finite syntomic algebra with a
pre-submersive presentation by as many relations as variables, relation `i` attached to variable
`i`, the module `det(NL_{B/A})` is free of rank one on a generator `g` with
`δ(NL_{B/A}) = J · g`, `J` the Jacobian of the presentation. -/
theorem exists_basis_deltaNL_eq_jacobian [Algebra.Syntomic A B] [Algebra.QuasiFinite A B]
    {m : ℕ} (Q : Algebra.PreSubmersivePresentation A B (Fin m) (Fin m)) (hQ : ∀ i, Q.map i = i) :
    ∃ b : Module.Basis (Fin 1) B (detNL A B), deltaNL A B = Q.jacobian • b 0 := by
  have : Q.toPresentation.IsRelativeGlobalCompleteIntersection :=
    Q.toPresentation.isRelativeGlobalCompleteIntersection_of_card_eq rfl
  obtain ⟨b, hb⟩ := Q.toPresentation.exists_basis_cotangent_relation
  refine ⟨(Q.toPresentation.cotangentDeterminantBasis b).map
    (detNLEquiv Q.toPresentation.toGenerators).symm, ?_⟩
  apply (detNLEquiv Q.toPresentation.toGenerators).injective
  rw [detNLEquiv_deltaNL _ Q.toPresentation.isRankZero_cotangentComplex,
    Q.toPresentation.delta_cotangentComplex_eq b hb 0, map_smul, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, det_relationJacobiMatrix_eq_jacobian Q hQ]

end Jacobian

/-! ### The local generator for `A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` -/

section LocalizedCompleteIntersection

open Stacks.Discriminant

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {n : ℕ} {h : MvPolynomial (Fin n) A} {f : Fin n → MvPolynomial (Fin n) A}

/-- **The local generator of `det(NL_{B/A})` for a localized complete intersection.** If
`B ≅ A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` is quasi-finite over `A`, then `det(NL_{B/A})` is free of
rank one on a generator `g` with `δ(NL_{B/A}) = det(∂f_i/∂x_j) · g`. The Jacobian determinant
is written out; it is `Stacks.Discriminant.jacobianDet n h f`, an abbreviation. -/
theorem exists_basis_deltaNL_eq_jacobianDet [Algebra.Syntomic A B] [Algebra.QuasiFinite A B]
    (e : B ≃ₐ[A] localizedCompleteIntersection A n h f) :
    ∃ b : Module.Basis (Fin 1) B (detNL A B),
      deltaNL A B = e.symm (Matrix.det fun i j : Fin n ↦
        algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f)
          (MvPolynomial.pderiv j (f i))) • b 0 := by
  classical
  let C := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)
  let Lq := localizedQuotient A n h f
  let hC : C := algebraMap (MvPolynomial (Fin n) A) C h
  have : IsScalarTower A C Lq := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalization.Away hC Lq := isLocalization_away_localizedQuotient A n h f
  let N : Algebra.PreSubmersivePresentation A C (Fin n) (Fin n) :=
    Algebra.PreSubmersivePresentation.naive (v := f) id Function.injective_id
  let Lc : Algebra.PreSubmersivePresentation C Lq Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway Lq hC
  let ε : Fin (n + 1) ≃ Unit ⊕ Fin n := Fintype.equivOfCardEq (by simp [add_comm])
  let E : Lq ≃ₐ[A] B := (localizedQuotientEquiv A n h f).trans e.symm
  let Q : Algebra.PreSubmersivePresentation A B (Fin (n + 1)) (Fin (n + 1)) :=
    ((Lc.comp N).reindex ε ε).ofAlgEquiv E
  have hQ : ∀ i, Q.map i = i := fun i ↦ by
    change ε.symm (Sum.elim (fun rq ↦ Sum.inl (Lc.map rq)) (fun rp ↦ Sum.inr (N.map rp)) (ε i)) = i
    rcases hε : ε i with _ | j <;> exact ε.symm_apply_eq.2 hε.symm
  obtain ⟨b, hb⟩ := exists_basis_deltaNL_eq_jacobian Q hQ
  have hjac : Q.jacobian =
      e.symm (algebraMap (MvPolynomial (Fin n) A) _ h) * e.symm (Matrix.det fun i j : Fin n ↦
        algebraMap (MvPolynomial (Fin n) A) (localizedCompleteIntersection A n h f)
          (MvPolynomial.pderiv j (f i))) := by
    simp only [Q, Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
      Algebra.PreSubmersivePresentation.jacobian_reindex,
      Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Lc,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def, map_mul, E,
      AlgEquiv.trans_apply]
    rw [mul_comm]
    congr 2
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, RingHom.map_det,
      RingHom.map_det, show ∀ x, (localizedQuotientEquiv A n h f) x =
      (localizedQuotientEquiv A n h f).toRingHom x from fun _ => rfl, RingHom.map_det,
      ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    rfl
  have hu : IsUnit (e.symm (algebraMap (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n h f) h)) :=
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h).map
      (Ideal.Quotient.mk _)).map e.symm
  refine ⟨b.map (LinearEquiv.smulOfUnit hu.unit), ?_⟩
  rw [hb, hjac, Module.Basis.map_apply]
  change _ = _ • ((hu.unit : B) • b 0)
  rw [smul_smul, IsUnit.unit_spec, mul_comm]

end LocalizedCompleteIntersection

end Stacks.TateMap
