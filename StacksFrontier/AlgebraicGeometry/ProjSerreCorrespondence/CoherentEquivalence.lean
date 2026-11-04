module

public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.QuasiInverseNatural
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TruncatedSectionsSpan
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Serre correspondence of Tag 0BXF: the equivalence and its quasi-inverse

Let `A` be a Noetherian graded ring and `X = Proj(A)`. Stacks 0BXE makes the irrelevant finitely
generated graded `A`-modules a Serre subcategory of `Mod^fg_A`, for a degree `d` which is the
least common multiple of the degrees of a finite homogeneous generating set of `A` over `A₀`, and
Stacks 0BXF asserts that `M ↦ M̃` induces an **equivalence**

`Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Coh(𝒪_X)`

whose quasi-inverse is `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))`. This file proves that, as
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_coherentIrrelevantQuotientEquivalence`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentQuasiInverseFunctor`: the
  quasi-inverse `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))` as a functor `Coh(𝒪_X) ⥤ Mod^fg_A / Mod^fg_{A,
  irrelevant}`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentQuasiInverseUnit`: **the unit
  `𝟭 ≅ (M ↦ M̃) ⋙ (ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n)))` of the equivalence.**
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentIrrelevantQuotientEquivalence`: the
  equivalence itself, built from the unit and the counit.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_iso_coherentQuasiInverseFunctor_obj`:
  **the span of Stacks 0B5R, read in the quotient category.** Every finitely generated graded
  module `M` becomes isomorphic, in `Mod^fg_A / Mod^fg_{A, irrelevant}`, to
  `⨁_{n ≥ 0} Γ(X, M̃(n))`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.essSurj_coherentQuasiInverseFunctor`: the
  quasi-inverse is essentially surjective.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isEquivalence_coherentQuasiInverseFunctor`:
  the quasi-inverse is an equivalence.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_coherentIrrelevantQuotientEquivalence`:
  **Stacks 0BXF.**

## How the proof runs

Three facts already in the library are the input: the arrow
`coherentIrrelevantQuotientFunctor` is **faithful** (`faithful_coherentIrrelevantQuotientFunctor`,
through the kernel identification of Stacks 0BXE and Stacks 06XK); the counit
`(ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))) ⋙ (M ↦ M̃) ≅ 𝟭 Coh(𝒪_X)` is an isomorphism
(`coherentQuasiInverseCounit`, Tag 0AG5 made natural); and all six parts of Stacks 0B5R hold.

From the first two the quasi-inverse `Ḡ = (ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n)))` into the quotient category
is **fully faithful**: its composite with the arrow is isomorphic to the identity, hence full and
faithful, so `Ḡ` is faithful, and full because the arrow is faithful. What remains for `Ḡ` to be
an equivalence is that it be **essentially surjective**, and that is the span of Stacks 0B5R. For
`M` a finitely generated graded module, with `N' = ⨁_{n ≥ 0} Γ(X, M(n)~)` and
`N = ⨁_{n ≥ 0} Γ(X, M̃(n))`:

* replacing `M` by its truncation `M_{≥ 0}` changes nothing in the quotient — the inclusion is
  injective and onto in every degree `≥ 0` — and makes part (4) of Stacks 0B5R applicable;
* part (4) gives `M_{≥ 0} ⟶ N'` and part (5) makes it bijective in all large degrees;
* part (3) gives `N ⟶ N'` and part (6) makes it bijective in every degree divisible by `d`;
* each of the three is therefore an isomorphism modulo the irrelevant modules, by
  `isoModSerre_of_eventually_bijective_grade`, so `M`, `M_{≥ 0}`, `N'` and `N` all become
  isomorphic in the quotient — and `N` is the value of `Ḡ` at the coherent sheaf `(M_{≥ 0})~`.

With `Ḡ` an equivalence and `Ḡ ⋙ F̄ ≅ 𝟭`, the arrow `F̄` is isomorphic to the inverse of `Ḡ`, and
the unit of the proposition's equivalence is the counit of `Ḡ`'s read through that isomorphism.
`CategoryTheory.Equivalence.mk` then needs no triangle identity.

## Implementation notes

The grading carrier `σ` is in the ring's universe. That is clause (4) of Stacks 0B5Q, inherited
from Tag 0AG6's degree-one case through the Veronese reduction, and it is what the quasi-inverse
`coherentTruncatedTwistedSectionsFunctor` is available at; faithfulness of the arrow holds with
`σ` in any universe (`CoherentTarget.lean`), and the statement below specialises it. Nothing is
pinned down which the pieces leave free: there is no `σ : Type w` anywhere in this file to pin.

The degree `d` cannot be quantified away, and `exists_coherentIrrelevantQuotientEquivalence`
produces it the way Stacks 0BXE does, as the least common multiple of the degrees of a finite
homogeneous generating set; for `A = k[x]` with `deg x = 2` the module `A(1)` has vanishing
associated sheaf and is not irrelevant at `d = 1`, so the kernel identification, and with it
faithfulness, genuinely needs `d` to be a multiple of the generators' degrees.
`isEquivalence_coherentQuasiInverseFunctor` is stated for an arbitrary such `d`, and
`exists_coherentIrrelevantQuotientEquivalence` exhibits one.

The equivalence is assembled with `CategoryTheory.Equivalence.mk`, whose `functor` and `inverse`
are the two given functors on the nose, so that the two equations of
`exists_coherentIrrelevantQuotientEquivalence` — that the equivalence *is* the induced functor,
with the named quasi-inverse for its inverse — hold by `rfl` and the statement is about the
proposition's own two functors rather than about some equivalence merely isomorphic to them.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 0BXE](https://stacks.math.columbia.edu/tag/0BXE)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 06XK](https://stacks.math.columbia.edu/tag/06XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (truncationAbove truncationAboveGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] [IsNoetherianRing S]

section Degree

variable {d : ℕ}

/-! ### The quasi-inverse into the quotient category -/

/-- **The quasi-inverse of Stacks 0BXF, `ℱ ↦ ⨁_{n ≥ k} Γ(X, ℱ(n))`, as a functor into the
quotient category** `Mod^fg_A / Mod^fg_{A, irrelevant}`. The proposition's quasi-inverse is the
case `k = 0`. -/
public def coherentQuasiInverseFunctor (hd : 0 < d) (k : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮) ⥤
      IrrelevantQuotient 𝒮 hd :=
  coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 k ⋙ toIrrelevantQuotient.{u, u, u} 𝒮 hd

/-- The quasi-inverse into the quotient category is the quasi-inverse into `Mod^fg_A` followed
by the quotient functor. -/
public theorem coherentQuasiInverseFunctor_eq (hd : 0 < d) (k : ℤ) :
    coherentQuasiInverseFunctor 𝒮 hd k =
      coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 k ⋙
        toIrrelevantQuotient.{u, u, u} 𝒮 hd := rfl

/-- **The counit of Stacks 0BXF's equivalence**: the quasi-inverse into the quotient category
followed by the arrow of the proposition is the identity of `Coh(𝒪_X)`. This is
`coherentQuasiInverseCounit` composed with the factorization of `M ↦ M̃` through the
quotient. -/
public def coherentQuasiInverseFunctorCounit (hd : 0 < d) (k : ℤ) :
    coherentQuasiInverseFunctor 𝒮 hd k ⋙ coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd ≅
      𝟭 (_root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮)) :=
  Functor.associator (coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 k)
      (toIrrelevantQuotient.{u, u, u} 𝒮 hd) (coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd) ≪≫
    Functor.isoWhiskerLeft (coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 k)
      (coherentIrrelevantQuotientFunctorFac.{u, u} 𝒮 hd) ≪≫
    coherentQuasiInverseCounit.{u} 𝒮 k

/-! ### Essential surjectivity: the span of Stacks 0B5R in the quotient -/

/-- **The span of Stacks 0B5R, read in the quotient category.** For `A` Noetherian graded, `d`
positive with the degree-`d` standard opens covering `Proj(A)`, and `M` a finitely generated
graded `A`-module, the object `M` of `Mod^fg_A / Mod^fg_{A, irrelevant}` is isomorphic to the
value of the quasi-inverse at a coherent sheaf, namely at `(M_{≥ 0})~`.

The three legs are the inclusion `M_{≥ 0} ⟶ M`, which is bijective in every degree `≥ 0`; the map
`M_{≥ 0} ⟶ N'` of part (4), bijective in all large degrees by part (5); and the comparison
`N ⟶ N'` of part (3), bijective in every degree divisible by `d` by part (6). Each is an
isomorphism modulo the irrelevant modules. -/
public theorem exists_iso_coherentQuasiInverseFunctor_obj (hd : 0 < d)
    (hdtop : _root_.AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤)
    (X : FiniteGradedModules.{u, u, u} 𝒮) :
    ∃ F : _root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮),
      Nonempty ((coherentQuasiInverseFunctor 𝒮 hd 0).obj F ≅
        (toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj X) := by
  have := X.property
  have hdone : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hnd : ∀ n : ℕ, (0 : ℤ) ≤ (n : ℤ) * d := fun n => by positivity
  -- the degree-`≥ 0` truncation of `M`, which is where part (4) applies
  let Y : FiniteGradedModules.{u, u, u} 𝒮 :=
    ⟨gradedTruncation 𝒮 X.obj 0, moduleFinite_gradedTruncation 𝒮 X.obj X.property 0⟩
  have : Module.Finite S Y.obj.carrier := Y.property
  -- step 1: `M_{≥ 0} ⟶ M` is an isomorphism modulo the irrelevant modules
  have e₁ : (toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj Y ≅
      (toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj X :=
    toIrrelevantQuotientIsoOfBijectiveGrade 𝒮 hd
      (⟨gradedTruncationι 𝒮 X.obj 0⟩ : Y ⟶ X) (N₀ := 0)
      (fun _ _ x _ hx =>
        Stacks.GradedModule.eq_zero_of_truncationAbove_subtype_eq_zero 𝒮 X.obj.grade 0 hx)
      (fun n _ y hy => by
        obtain ⟨x, -, hxy⟩ := exists_gradedTruncationι_eq 𝒮 X.obj (hnd n) hy
        exact ⟨x, hxy⟩)
  -- `M_{≥ 0}` vanishes below degree `0`, which is part (4)'s hypothesis
  have hlow : ∀ n : ℤ, n < 0 → ∀ x ∈ Y.obj.grade n, x = (0 : Y.obj.carrier) := by
    intro n hn x hx
    have hx' : x ∈ (gradedTruncation 𝒮 X.obj 0).grade n := hx
    rw [grade_gradedTruncation_eq_bot 𝒮 X.obj hn] at hx'
    simpa using hx'
  -- step 2: part (4) and part (5)
  let N' : FiniteGradedModules.{u, u, u} 𝒮 :=
    ⟨shiftedTruncatedSectionsObj 𝒮 Y.obj.grade 0,
      moduleFinite_shiftedTruncatedSectionsObj 𝒮 Y.obj.grade 0⟩
  obtain ⟨n₀, hn₀⟩ :=
    ProjLargeDegrees.exists_bijective_degreeNToGlobalSections_of_isNoetherian 𝒮 Y.obj.grade
  have hbig : ∀ n : ℕ, (max n₀ 0).toNat ≤ n → n₀ ≤ (n : ℤ) * d := by
    intro n hn
    have : (n : ℤ) ≤ n * d := le_mul_of_one_le_right (by positivity) hdone
    omega
  have e₂ : (toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj Y ≅
      (toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj N' :=
    toIrrelevantQuotientIsoOfBijectiveGrade 𝒮 hd
      (⟨moduleToShiftedTruncation 𝒮 Y.obj 0 hlow⟩ : Y ⟶ N') (N₀ := (max n₀ 0).toNat)
      (fun n hn x hx hxz => eq_zero_of_moduleToShiftedTruncation_eq_zero 𝒮 Y.obj 0 hlow
        (hn₀ ((n : ℤ) * d) (hbig n hn)) x hx hxz)
      (fun n hn y hy => exists_moduleToShiftedTruncation_eq 𝒮 Y.obj 0 hlow
        (hn₀ ((n : ℤ) * d) (hbig n hn)) y hy)
  -- step 3: part (3) and part (6)
  have hbij6 : ∀ n : ℕ, Function.Bijective
      (ProjCoherentII.twistedToShiftedComponent 𝒮 Y.obj.grade ((n : ℤ) * d)) := fun n =>
    ProjCoherentII.bijective_twistedToShiftedComponent 𝒮 Y.obj.grade hdtop
      ⟨(n : ℤ), by ring⟩
  have e₃ : (toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj
        ((coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 0).obj
          ((coherentAssociatedSheafFunctor.{u, u} 𝒮).obj Y)) ≅
      (toIrrelevantQuotient.{u, u, u} 𝒮 hd).obj N' :=
    toIrrelevantQuotientIsoOfBijectiveGrade 𝒮 hd
      (⟨truncatedTwistedToShiftedMor 𝒮 Y.obj.grade 0⟩ :
        (coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 0).obj
          ((coherentAssociatedSheafFunctor.{u, u} 𝒮).obj Y) ⟶ N') (N₀ := 0)
      (fun n _ z hz hzz => eq_zero_of_truncatedTwistedToShiftedMor_eq_zero 𝒮 Y.obj.grade 0
        (hbij6 n) z hz hzz)
      (fun n _ y hy => exists_truncatedTwistedToShiftedMor_eq 𝒮 Y.obj.grade 0 (hnd n)
        (hbij6 n) y hy)
  exact ⟨(coherentAssociatedSheafFunctor.{u, u} 𝒮).obj Y, ⟨e₃ ≪≫ e₂.symm ≪≫ e₁⟩⟩

/-- **The quasi-inverse of Stacks 0BXF is essentially surjective.** Every object of the quotient
category is the image of a finitely generated graded module, and every such module becomes
isomorphic to `⨁_{n ≥ 0} Γ(X, ℱ(n))` for a coherent `ℱ` by the span of Stacks 0B5R. -/
public theorem essSurj_coherentQuasiInverseFunctor (hd : 0 < d)
    (hdtop : _root_.AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) :
    (coherentQuasiInverseFunctor 𝒮 hd 0).EssSurj where
  mem_essImage P := by
    have := isSerreClass_irrelevantModules.{u, u, u} 𝒮 hd
    have := Localization.essSurj (toIrrelevantQuotient.{u, u, u} 𝒮 hd)
      (ObjectProperty.isoModSerre (irrelevantModules.{u, u, u} 𝒮 d))
    obtain ⟨F, ⟨e⟩⟩ := exists_iso_coherentQuasiInverseFunctor_obj 𝒮 hd hdtop
      ((toIrrelevantQuotient.{u, u, u} 𝒮 hd).objPreimage P)
    exact ⟨F, ⟨e ≪≫ (toIrrelevantQuotient.{u, u, u} 𝒮 hd).objObjPreimageIso P⟩⟩

/-! ### The equivalence -/

section Main

variable {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
  (hf : ∀ i, f i ∈ 𝒮 (deg i))
  (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)

include f hdeg hf hgen in
/-- **The quasi-inverse of Stacks 0BXF is an equivalence.** It is faithful because its composite
with the arrow of the proposition is isomorphic to the identity, full because that arrow is
faithful, and essentially surjective by the span of Stacks 0B5R. -/
public theorem isEquivalence_coherentQuasiInverseFunctor (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d)
    (hdtop : _root_.AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) :
    (coherentQuasiInverseFunctor 𝒮 hd 0).IsEquivalence := by
  have := faithful_coherentIrrelevantQuotientFunctor 𝒮 f deg hdeg hf hgen hd hdvd
  have := Functor.Faithful.of_comp_iso (coherentQuasiInverseFunctorCounit 𝒮 hd 0)
  have := Functor.Full.of_comp_faithful_iso (coherentQuasiInverseFunctorCounit 𝒮 hd 0)
  have := essSurj_coherentQuasiInverseFunctor 𝒮 hd hdtop
  exact { }

/-- **The arrow of Stacks 0BXF is the inverse of the quasi-inverse's equivalence.** -/
public def coherentIrrelevantQuotientFunctorIsoInv (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d)
    (hdtop : _root_.AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) :
    haveI := isEquivalence_coherentQuasiInverseFunctor 𝒮 f deg hdeg hf hgen hd hdvd hdtop
    coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd ≅
      (coherentQuasiInverseFunctor 𝒮 hd 0).asEquivalence.inverse :=
  haveI := isEquivalence_coherentQuasiInverseFunctor 𝒮 f deg hdeg hf hgen hd hdvd hdtop
  ((coherentQuasiInverseFunctor 𝒮 hd 0).asEquivalence.invFunIdAssoc
        (coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd)).symm ≪≫
    Functor.isoWhiskerLeft (coherentQuasiInverseFunctor 𝒮 hd 0).asEquivalence.inverse
      (coherentQuasiInverseFunctorCounit 𝒮 hd 0) ≪≫
    (coherentQuasiInverseFunctor 𝒮 hd 0).asEquivalence.inverse.rightUnitor

include f hdeg hf hgen in
/-- **The unit of Stacks 0BXF's equivalence**: the natural isomorphism

`𝟭 (Mod^fg_A / Mod^fg_{A, irrelevant}) ≅ (M ↦ M̃) ⋙ (ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n)))`.

Its components are the span `M ⟶ N' ⟵ N` of parts (4) and (3) of Stacks 0B5R, inverted in the
quotient category by parts (5) and (6): that is what makes the quasi-inverse essentially
surjective, hence an equivalence, and this isomorphism is the counit of that equivalence read
through the identification of the arrow with its inverse. -/
public def coherentQuasiInverseUnit (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d)
    (hdtop : _root_.AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) :
    𝟭 (IrrelevantQuotient 𝒮 hd) ≅
      coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd ⋙ coherentQuasiInverseFunctor 𝒮 hd 0 :=
  haveI := isEquivalence_coherentQuasiInverseFunctor 𝒮 f deg hdeg hf hgen hd hdvd hdtop
  (coherentQuasiInverseFunctor 𝒮 hd 0).asEquivalence.counitIso.symm ≪≫
    Functor.isoWhiskerRight
      (coherentIrrelevantQuotientFunctorIsoInv 𝒮 f deg hdeg hf hgen hd hdvd hdtop).symm
      (coherentQuasiInverseFunctor 𝒮 hd 0)

include f hdeg hf hgen in
/-- **Stacks 0BXF, for an arbitrary degree of the kind Stacks 0BXE asks for.** The functor
`M ↦ M̃` induces an equivalence `Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Coh(𝒪_X)` whose quasi-inverse
is `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))`. -/
@[ega "III 2.3.3" "(F), special case"]
public def coherentIrrelevantQuotientEquivalence (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d)
    (hdtop : _root_.AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤) :
    IrrelevantQuotient 𝒮 hd ≌
      _root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮) :=
  CategoryTheory.Equivalence.mk (coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd)
    (coherentQuasiInverseFunctor 𝒮 hd 0)
    (coherentQuasiInverseUnit 𝒮 f deg hdeg hf hgen hd hdvd hdtop)
    (coherentQuasiInverseFunctorCounit 𝒮 hd 0)

end Main

end Degree

/-! ### The proposition -/

/-- **[Stacks, Tag 0BXF].** Let `A` be a Noetherian graded ring and `X = Proj(A)`. There is a
degree `d` of the kind [Stacks, Tag 0BXE] asks for — the least common multiple of the degrees of a
finite homogeneous generating set of `A` over `A₀` — and for it the functor `M ↦ M̃` induces an
**equivalence**

`Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Coh(𝒪_X)`

whose quasi-inverse is `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))`.

The two equations say that the equivalence *is* the proposition's two functors: its `functor` is
`coherentIrrelevantQuotientFunctor`, the arrow induced by `M ↦ M̃` on the quotient category, and
its `inverse` is `coherentTruncatedTwistedSectionsFunctor 𝒮 0` followed by the quotient functor,
which is `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))`.

The degree cannot be quantified away: for `A = k[x]` with `deg x = 2` the module `A(1)` has
vanishing associated sheaf and is not irrelevant at `d = 1`, so the subcategory of [Stacks, Tag
0BXE], and with it the quotient category, genuinely depends on `d` being a multiple of the
generators' degrees. `coherentIrrelevantQuotientEquivalence` is the same statement for every such
`d`. -/
@[stacks 0BXF "the proposition: for A a Noetherian graded ring and X = Proj(A), the functor \
M ↦ M~ induces an equivalence Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Coh(O_X) whose quasi-inverse \
is F ↦ ⨁_{n ≥ 0} Γ(X, F(n)). The degree d of Tag 0BXE, the lcm of the degrees of a finite \
homogeneous generating set of A over A_0, is produced here as the source produces it; the same \
statement for an arbitrary d divisible by those degrees is \
coherentIrrelevantQuotientEquivalence", ega "II 2.7.7" "Coherent noetherian case"]
public theorem exists_coherentIrrelevantQuotientEquivalence :
    ∃ (d : ℕ) (hd : 0 < d) (e : IrrelevantQuotient 𝒮 hd ≌
        _root_.AlgebraicGeometry.SheafOfModules.CoherentModules (projRingSheaf 𝒮)),
      e.functor = coherentIrrelevantQuotientFunctor.{u, u} 𝒮 hd ∧
        e.inverse = coherentTruncatedTwistedSectionsFunctor.{u} 𝒮 0 ⋙
          toIrrelevantQuotient.{u, u, u} 𝒮 hd := by
  classical
  obtain ⟨r, f, deg, hdeg, hf, hgen⟩ := exists_homogeneous_generators_of_isNoetherianRing 𝒮
  have hpos : 0 < Finset.univ.lcm deg := Nat.pos_of_ne_zero fun h0 => by
    obtain ⟨i, -, hi⟩ := Finset.lcm_eq_zero_iff.mp h0
    exact absurd hi (hdeg i).ne'
  exact ⟨Finset.univ.lcm deg, hpos,
    coherentIrrelevantQuotientEquivalence 𝒮 f deg hdeg hf hgen hpos
      (fun i => Finset.dvd_lcm (Finset.mem_univ i))
      (ProjCoherentII.degreeOpen_lcm_eq_top 𝒮 f deg hdeg hf hgen),
    rfl, rfl⟩

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
