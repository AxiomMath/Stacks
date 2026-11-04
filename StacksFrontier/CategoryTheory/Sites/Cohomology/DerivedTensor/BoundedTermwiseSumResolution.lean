module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionBySumsOfExtensionsByZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SieveIndexedSubcomplexGenerators
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# A bounded above complex is resolved by a single ladder rung

Stacks 077J (`exists_resolutionByDirectSumsExtensionsByZero`) resolves the upper truncations
`τ_{≤ n+1} G` of a complex of modules on a ringed site, by complexes whose terms are direct sums
of extensions by zero `j_{U!}O_U` of the structure sheaves of slices. Its *colimit* is what is
quasi-isomorphic to `G` itself, and the terms of that colimit are filtered colimits of sums of
extensions by zero rather than sums of them.

For a complex that is bounded above no colimit is needed: a single rung already does it. Once
`n + 1` is past the bound, `G.ιTruncLE (n+1)` is an isomorphism, so the rung
`Q_n ⟶ τ_{≤ n+1} G` composes with its inverse to a quasi-isomorphism `Q_n ⟶ G` whose terms are
honest direct sums of extensions by zero.

This is what a consumer needing the *presentation* rather than the flatness has to have: the
hypothesis `∀ n, IsColimit (cofanP O P U ιP n)` of
`Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex` asks that each term of the complex **be**
a direct sum of extensions by zero, and an epimorphism onto it — which is what the
extension-by-zero generation lemmas supply — is not enough.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedTensor.ResolutionByExtensionsByZero

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- **A complex of modules on a ringed site that is bounded above receives a quasi-isomorphism
from a bounded above complex each of whose terms is a direct sum of extensions by zero of the
structure sheaves of slices.**

Boundedness is not a weakening of 077J: it is the hypothesis under which the ladder of
`exists_resolutionByDirectSumsExtensionsByZero` can be read off at one rung instead of in the
limit, and it is what the consumers of the termwise presentation have anyway. -/
public theorem exists_isSum_quasiIso_of_isStrictlyLE (a : ℤ)
    (G : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    [G.IsStrictlyLE a] :
    ∃ (Q : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      (q : Q ⟶ G) (b : ℤ),
      QuasiIso q ∧ Q.IsStrictlyLE b ∧
        ∀ i : ℤ, IsSumOfExtensionByZeroStructureSheaves R (Q.X i) := by
  obtain ⟨L⟩ := exists_resolutionByDirectSumsExtensionsByZero R G
  have hself : a ≤ (a.toNat : ℤ) := Int.self_le_toNat a
  have : G.IsStrictlyLE ((a.toNat + 1 : ℕ) : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact G.isZero_of_isStrictlyLE a i (by push_cast at hi; omega)
  obtain ⟨b, hb⟩ := L.boundedAbove a.toNat
  have := L.quasiIso a.toNat
  exact ⟨L.system.obj a.toNat,
    L.toTruncation a.toNat ≫ G.ιTruncLE ((a.toNat + 1 : ℕ) : ℤ), b,
    inferInstance, hb, fun i => L.term_isSum a.toNat i⟩

/-- The family of extensions by zero indexed by a choice of slices in one degree. -/
public noncomputable abbrev sumFamily {I : Type u} (U : I → C) (α : I) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) :=
  (SheafOfModules.extensionByZero
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) (U α)).obj
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).over (U α)))

/-- **The termwise presentation, in the form the sieve-indexed subcomplex construction takes.**
`Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex` asks for index types, slices, structure
maps and a proof that each `cofanP` is a colimit; a complex whose terms are sums of extensions by
zero has exactly that data, the colimit being the coproduct cocone transported along the
isomorphism. `IsColimit` is data rather than a proposition, so it is returned under `Nonempty`. -/
public theorem exists_cofanP_isColimit_of_term_isSum
    (Q : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    (h : ∀ i : ℤ, IsSumOfExtensionByZeroStructureSheaves R (Q.X i)) :
    ∃ (I : ℤ → Type u) (U : ∀ n, I n → C)
      (ιP : ∀ (n : ℤ) (α : I n), sumFamily R (U n) α ⟶ Q.X n),
      Nonempty (∀ n : ℤ, IsColimit (Stacks.Sites.ExtensionByZero.cofanP
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) Q U ιP n)) := by
  choose I U e using h
  refine ⟨I, U, fun n α => Sigma.ι (fun β : I n => sumFamily R (U n) β) α ≫ (e n).some.hom,
    ⟨fun n => ?_⟩⟩
  exact IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cocone.ext (e n).some (by intro j; simp))

/-- **A bounded above complex whose terms are sums of extensions by zero is K-flat.** Stacks 06YQ
applied to the flatness of such a sum (Stacks 03EU). This is what the direct-summand step of
Stacks 0FPV needs of the replacement complex beyond the presentation itself: the comparison
between the derived and the total tensor product is available only on K-flat complexes. -/
public theorem isKFlat_of_term_isSum_of_isStrictlyLE
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).Additive]
    [∀ (K₁ K₂ : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R) (ComplexShape.up ℤ)]
    (b : ℤ)
    (Q : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    [Q.IsStrictlyLE b]
    (h : ∀ i : ℤ, IsSumOfExtensionByZeroStructureSheaves R (Q.X i)) :
    Stacks.SheafOfModules.IsKFlat R Q :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat R Q ⟨b, inferInstance⟩
    fun i =>
      Stacks.SheafOfModules.KFlatResolution.isFlat_of_isSumOfExtensionByZeroStructureSheaves
        R (Q.X i) (h i)

/-- **A bounded above complex of modules on a ringed site receives a quasi-isomorphism from a
complex presented, degreewise, as a direct sum of extensions by zero** — with the presentation
delivered as the `ιP`/`IsColimit`/vanishing triple that
`Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex` consumes.

This is the entry point for the sieve-indexed subcomplex construction: `exists_sieve_subcomplex`
cannot be applied to an arbitrary representative of an object of the derived category, and this
says what to replace one by first. -/
public theorem exists_quasiIso_cofanP_isColimit_of_isStrictlyLE
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).Additive]
    [∀ (K₁ K₂ : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R) (ComplexShape.up ℤ)]
    (a : ℤ)
    (G : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
    [G.IsStrictlyLE a] :
    ∃ (Q : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      (q : Q ⟶ G) (b : ℤ) (I : ℤ → Type u) (U : ∀ n, I n → C)
      (ιP : ∀ (n : ℤ) (α : I n), sumFamily R (U n) α ⟶ Q.X n),
      QuasiIso q ∧ (∀ n : ℤ, b < n → IsZero (Q.X n)) ∧
        Stacks.SheafOfModules.IsKFlat R Q ∧
        Nonempty (∀ n : ℤ, IsColimit (Stacks.Sites.ExtensionByZero.cofanP
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) Q U ιP n)) := by
  obtain ⟨Q, q, b, hq, hLE, hsum⟩ := exists_isSum_quasiIso_of_isStrictlyLE R a G
  obtain ⟨I, U, ιP, hc⟩ := exists_cofanP_isColimit_of_term_isSum R Q hsum
  have := hLE
  exact ⟨Q, q, b, I, U, ιP, hq, fun n hn => Q.isZero_of_isStrictlyLE b n hn,
    isKFlat_of_term_isSum_of_isStrictlyLE R b Q hsum, hc⟩

end Stacks.DerivedTensor.ResolutionByExtensionsByZero
