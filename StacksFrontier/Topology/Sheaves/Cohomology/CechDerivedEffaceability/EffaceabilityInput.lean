module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Transport
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.CechIsTheDerivedFunctor

/-!
# The effaceability input of Stacks 01EN

Stacks 01EN compares the Čech cohomology δ-functor of a covering with the right-derived
δ-functor of its degree-zero part. Its proof has two inputs; this file is about the first,
the *effaceability* of the Čech δ-functor. `Stacks.Cohomology.CechDerived` carries that input
as the hypothesis

`∀ (n : ℕ) (I : Modules R), Injective I → IsZero ((cechCohomologyFunctor R 𝒰 (n + 1)).obj I)`,

the vanishing of the higher Čech cohomology of an injective presheaf of modules. This file
replaces that hypothesis by the strictly weaker `DeltaFunctor.Effaceable` — only *some*
monomorphism out of each object need be killed in each positive degree, and no injective
objects are needed — and records the reformulation of the vanishing as exactness of the Čech
complex, which is the shape in which the remaining mathematics is naturally proved.

## Main definitions

* `CategoryTheory.DeltaFunctor.appIso`: the degree-`n` component of an isomorphism of
  δ-functors, as an isomorphism of functors.

## Main results

* `isZero_cechCohomology_iff_exactAt`: degree-`n` Čech cohomology of `M` vanishes exactly when
  the Čech complex of `M` is exact in degree `n`.
* `effacement`: a monomorphism into a presheaf with vanishing degree-`n + 1` Čech cohomology is
  an effacement of the Čech δ-functor.
* `effaceable_of_exists_mono` and `effaceable_of_isZero_injective`: the two ways of producing
  effaceability; the second shows that 01EN's hypothesis implies the one used here.
* `cechDeltaFunctor_isUniversal`, `cechDeltaIsoRightDerived` and
  `cechDeltaIsoRightDerived_app_zero`: the 01EN conclusions with the effaceability hypothesis
  replaced by `Effaceable`.

## What is still missing

The effaceability itself is **not** proved here, and it does not follow from the project's
formalizations of Stacks 01EL and 01EM. Those two live in a different category: 01EL
(`StacksDraft.Ch20.Sec10.Tag01EL`) and 01EM (`StacksDraft.Ch20.Sec10.Tag01EM`) are stated for
the bespoke structure `StacksCechPresheaf.ModPresheaf X` of a ringed space `X`, which carries a
`Category` and a `Preadditive` instance and nothing more — no zero object, no kernels, no
abelian structure, hence no notion of injective object and no homology of its complexes — and
there is no comparison functor between it and the `CategoryTheory.PresheafOfModules` of 01EN.
The missing mathematics is therefore the Hom-complex presentation of the Čech complex *inside*
`PresheafOfModules`: the chain complex `K(𝒰)` of direct sums of extensions by zero, which is a
complex of projectives there because `PresheafOfModules.freeYoneda` is left adjoint to an exact
evaluation, together with the identification `Hom(K(𝒰), -) ≅ Č(𝒰, -)` of 01EL and the
positive-degree acyclicity of `K(𝒰)` of 01EM. For an injective `F` the functor `Hom(-, F)` is
exact, and the vanishing follows.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechDerived

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.CechEffaceable

variable {Y : TopCat} (R : (Opens Y)ᵒᵖ ⥤ RingCat) (𝒰 : CechOpenCover Y)

/-- Degree-`n` Čech cohomology of a presheaf of `R`-modules vanishes precisely when its Čech
complex is exact in degree `n`. Čech cohomology is by definition the homology of that complex,
so this is Mathlib's `HomologicalComplex.exactAt_iff_isZero_homology`. -/
theorem isZero_cechCohomology_iff_exactAt (M : PresheafOfModules R) (n : ℕ) :
    IsZero ((cechCohomologyFunctor R 𝒰 n).obj M) ↔
      ((cechComplexFunctor R 𝒰).obj M).ExactAt n :=
  (HomologicalComplex.exactAt_iff_isZero_homology ((cechComplexFunctor R 𝒰).obj M) n).symm

/-- **An effacement of the Čech δ-functor.** A monomorphism `ι : M ⟶ N` of presheaves of
`R`-modules whose target has vanishing degree-`n + 1` Čech cohomology effaces `M` in degree
`n + 1`: the induced map lands in a zero object, hence is zero. -/
def effacement {M N : PresheafOfModules R} (ι : M ⟶ N) [Mono ι] (n : ℕ)
    (hN : IsZero ((cechCohomologyFunctor R 𝒰 (n + 1)).obj N)) :
    (cechDeltaFunctor R 𝒰).Effacement M n where
  I := N
  ι := ι
  map_ι := hN.eq_of_tgt _ _

/-- **Effaceability of the Čech δ-functor from monomorphisms into Čech-acyclic presheaves.**
If every presheaf of `R`-modules admits, in every positive degree, a monomorphism into a
presheaf whose Čech cohomology vanishes in that degree, then the Čech δ-functor is effaceable.
This asks strictly less than vanishing on all injectives: the target may depend on the degree
and on the object, and need not be injective. -/
theorem effaceable_of_exists_mono
    (h : ∀ (n : ℕ) (M : PresheafOfModules R), ∃ (N : PresheafOfModules R) (ι : M ⟶ N),
      Mono ι ∧ IsZero ((cechCohomologyFunctor R 𝒰 (n + 1)).obj N)) :
    (cechDeltaFunctor R 𝒰).Effaceable where
  nonempty M n := by
    obtain ⟨N, ι, hι, hN⟩ := h n M
    exact ⟨effacement R 𝒰 ι n hN⟩

/-- **The effaceability hypothesis of Stacks 01EN implies the one used here.** If the higher
Čech cohomology of every injective presheaf of `R`-modules vanishes then the Čech δ-functor is
effaceable: embed each object in an injective one. -/
theorem effaceable_of_isZero_injective [EnoughInjectives (Modules R)]
    (hinj : ∀ (n : ℕ) (I : Modules R), Injective I →
      IsZero ((cechCohomologyFunctor R 𝒰 (n + 1)).obj I)) :
    (cechDeltaFunctor R 𝒰).Effaceable :=
  DeltaFunctor.Effaceable.of_isZero_injective _ fun n I _ ↦ hinj n I ‹_›

/-- **Universality of the Čech δ-functor from effaceability, Stacks 010T.** This is
`Stacks.Cohomology.CechDerived.cechDeltaFunctor_isUniversal` with its hypothesis weakened from
vanishing on injectives to effaceability, and with `EnoughInjectives` no longer required. -/
theorem cechDeltaFunctor_isUniversal [(cechDeltaFunctor R 𝒰).Effaceable] :
    (cechDeltaFunctor R 𝒰).IsUniversal :=
  DeltaFunctor.isUniversal_of_effaceable _

/-- **The Čech-to-derived δ-functor comparison from effaceability.** Let `G` be a δ-functor
whose degree-zero part is degree-zero Čech cohomology and whose components are the right
derived functors of that degree-zero part. If the Čech δ-functor is effaceable then it is
isomorphic to `G`, by the unique isomorphism that is the identity in degree zero. This is
`Stacks.Cohomology.CechDerived.cechDeltaIsoRightDerived` with its first hypothesis replaced
by `Effaceable`. -/
def cechDeltaIsoRightDerived [EnoughInjectives (Modules R)]
    [(cechDeltaFunctor R 𝒰).Effaceable]
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (hG0 : G.functor 0 = cechCohomologyFunctor R 𝒰 0)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) :
    cechDeltaFunctor R 𝒰 ≅ G :=
  letI := cechDeltaFunctor_isUniversal R 𝒰
  letI := isUniversal_of_functor_eq_rightDerived G hG
  DeltaFunctor.IsUniversal.isoOfIso (eqToIso hG0.symm)

/-- The comparison of `cechDeltaIsoRightDerived` is the identity in degree zero. -/
theorem cechDeltaIsoRightDerived_app_zero [EnoughInjectives (Modules R)]
    [(cechDeltaFunctor R 𝒰).Effaceable]
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (hG0 : G.functor 0 = cechCohomologyFunctor R 𝒰 0)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) :
    (cechDeltaIsoRightDerived R 𝒰 G hG0 hG).hom.app 0 = eqToHom hG0.symm :=
  let := cechDeltaFunctor_isUniversal R 𝒰
  let := isUniversal_of_functor_eq_rightDerived G hG
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (eqToIso hG0.symm)

end Stacks.Cohomology.CechEffaceable

namespace CategoryTheory.DeltaFunctor

section Componentwise

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] {B : Type u₂} [Category.{v₂} B]
  [Preadditive B]

/-- The degree-`n` component of an isomorphism of δ-functors is an isomorphism of functors:
composition and the identity of the category of δ-functors of Stacks 010R are componentwise. -/
def appIso {F G : DeltaFunctor A B} (α : F ≅ G) (n : ℕ) : F.functor n ≅ G.functor n where
  hom := α.hom.app n
  inv := α.inv.app n
  hom_inv_id := congrArg (fun h : F ⟶ F ↦ h.app n) α.hom_inv_id
  inv_hom_id := congrArg (fun h : G ⟶ G ↦ h.app n) α.inv_hom_id

/-- The forward map of `appIso` is the degree-`n` component of the isomorphism. -/
@[simp]
lemma appIso_hom {F G : DeltaFunctor A B} (α : F ≅ G) (n : ℕ) :
    (appIso α n).hom = α.hom.app n :=
  rfl

/-- The inverse map of `appIso` is the degree-`n` component of the inverse isomorphism. -/
@[simp]
lemma appIso_inv {F G : DeltaFunctor A B} (α : F ≅ G) (n : ℕ) :
    (appIso α n).inv = α.inv.app n :=
  rfl

end Componentwise

end CategoryTheory.DeltaFunctor

end
