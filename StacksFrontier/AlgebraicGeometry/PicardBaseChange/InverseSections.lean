module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Sections

/-!
# Global sections of the tensor powers of an invertible module trivialized by base change

Let `X` be a quasi-compact, quasi-separated scheme over a ring `A`, let `φ : A →+* B` be
faithfully flat, and let `L` be an invertible `𝒪_X`-module whose pullback to `X_B` is trivial.
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/Sections.lean` proves the clause of Tag 0CDX
about `Γ(X, L)` itself. This file proves the clause about the inverse tensor power
`Γ(X, L^{⊗ -1})`, and in fact about every integer tensor power.

The one thing it has to add is that the trivializing hypothesis propagates from `L` to its
tensor powers: if `p^* L ≅ 𝒪_Y` then `p^*(L^{⊗ n}) ≅ 𝒪_Y`. That needs **no** comparison
between a pullback of a tensor power and the tensor power of the pullback. The defining
iteration `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` of Tag 01CU, the binary Tag 01CD comparison
`p^*(F ⊗ G) ≅ p^* F ⊗ p^* G`, and `p^* 𝒪_X ≅ 𝒪_Y` suffice: push the iteration through the
pullback one step at a time, in both directions, and cancel the trivialized factor with a
unitor.

## Main results

* `Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_pullback_tensorPower`: a pullback that
  trivializes an invertible module trivializes all of its integer tensor powers.
* `Stacks.AlgebraicGeometry.PicardBaseChange.invertible_globalSections_tensorPower_of_isTrivial`:
  Tag 0CDX's invertibility clause for every integer tensor power, for an arbitrary cartesian
  square with affine bases.
* `Stacks.AlgebraicGeometry.PicardBaseChange`
  `.invertible_globalSections_tensorInverse_of_faithfullyFlat_trivialization`:
  **Tag 0CDX, the clause about the global sections of the inverse sheaf.**

## Implementation notes

The integer tensor power is `Stacks.SheafOfModules.Invertible.tensorPower` of
`StacksFrontier/AlgebraicGeometry/Divisors/TensorPower.lean`, which is the tensor power of Tag 01CU
in the spelling the Chapter 33 decomposition uses: it takes
`AlgebraicGeometry.SheafOfModules.IsInvertible` as its instance argument, as the decomposition's
Tag 01CS's `IsInvertible` does. The repository also carries
`Stacks.SheafOfModules.TensorPower.tensorPower`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPower.lean`), with the same body but with
the instance argument `(tensorRightFunctor O hO L).IsEquivalence`. Nothing *here* identifies the
two, but the library does:
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerBridge.lean` derives that instance
argument from either invertibility predicate and proves the two powers equal by `rfl`
(`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower`), so a statement about one
applies to the other.

Invertibility of the tensor powers is `Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`
(`StacksFrontier/AlgebraicGeometry/Ample/AmpleCriteria.lean`), proved from Tag 01CT (1) and the
successor comparison and so independent of Tag 01CU's coherence structure, which is proved in
`StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/Basic.lean`.

The statement is given in the shape the decomposition states it, with the module structure on
`(L^{⊗ n}).val.obj (op ⊤)` supplied explicitly rather than by instance search: the tensor power
has type `SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
  X.ringCatSheaf.property)`, which
is only definitionally `X.Modules`, so the `Γ(·, ·)` notation's instances are not found for it.

**This file proves the two invertibility clauses; the third clause of Tag 0CDX is proved
elsewhere.** That the canonical multiplication
`Γ(X, L) ⊗_{Γ(X, 𝒪_X)} Γ(X, L^{⊗ -1}) → Γ(X, 𝒪_X)` is an isomorphism is reduced by
`Module.Invertible.exists_mulEquiv_of_lTensor_surjective` (`StacksFrontier/AlgebraicGeometry/PicardBaseChange/Basic.lean`)
to surjectivity of that multiplication after base change along
`Γ(X, 𝒪_X) → Γ(X_B, 𝒪_{X_B})`, with both invertibility hypotheses supplied from here. That
surjectivity, and with it the clause, is proved in
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/MulIsomorphism.lean`, against the pairing presented as a linear map by
`Stacks.SheafOfModules.Invertible.globalSectionsMulNegOneLinear`
(`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InversePairingLinear.lean`); the clause written with Tag 01CU's coherent
multiplication, which is where its `@[stacks 0CDX]` attribute sits, is in
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/CoherentMul.lean`. Neither route uses
`Stacks.RingedSpace.pullbackBilinear`.

## References

* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits (pullbackTensorIso)
open AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open Stacks.AlgebraicGeometry.SectionsBaseChange
open AlgebraicGeometry.SheafOfModules (IsInvertible IsTrivial)

namespace Stacks.AlgebraicGeometry.PicardBaseChange

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (L : X.Modules)
  [IsInvertible X.presheaf X.ringCatSheaf.property L]

/-- **A pullback that trivializes an invertible module trivializes all of its integer tensor
powers.**

No comparison between `p^*(L^{⊗ n})` and `(p^* L)^{⊗ n}` is used. In degree zero the tensor power
*is* the structure sheaf and the statement is `p^* 𝒪_X ≅ 𝒪_Y`. Each step up pushes the defining
iteration `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` through the binary comparison
`p^*(F ⊗ G) ≅ p^* F ⊗ p^* G` and contracts `𝒪_Y ⊗ 𝒪_Y` with a unitor; each step down reads the
same iteration backwards and cancels the trivialized factor `p^* L ≅ 𝒪_Y` with the right
unitor. -/
theorem isTrivial_pullback_tensorPower
    (hL : IsTrivial Y.presheaf Y.ringCatSheaf.property ((Scheme.Modules.pullback p).obj L))
    (n : ℤ) :
    IsTrivial Y.presheaf Y.ringCatSheaf.property
      ((Scheme.Modules.pullback p).obj
        (tensorPower X.presheaf X.ringCatSheaf.property L n)) := by
  obtain ⟨eL⟩ := hL
  induction n using Int.induction_on with
  | zero => exact ⟨pullbackUnitIso p⟩
  | succ k ih =>
      obtain ⟨ek⟩ := ih
      exact ⟨((Scheme.Modules.pullback p).mapIso
            (tensorPowerSuccIso X.presheaf X.ringCatSheaf.property L k)).symm ≪≫
          pullbackTensorIso p (tensorPower X.presheaf X.ringCatSheaf.property L k) L ≪≫
          tensorProductIso Y.presheaf Y.ringCatSheaf.property ek eL ≪≫
          tensorProductLeftUnitor Y.presheaf Y.ringCatSheaf.property _⟩
  | pred k ih =>
      obtain ⟨ek⟩ := ih
      refine ⟨(tensorProductRightUnitor Y.presheaf Y.ringCatSheaf.property
            ((Scheme.Modules.pullback p).obj
              (tensorPower X.presheaf X.ringCatSheaf.property L (-(k : ℤ) - 1)))).symm ≪≫
          tensorProductIso Y.presheaf Y.ringCatSheaf.property (Iso.refl _) eL.symm ≪≫
          (pullbackTensorIso p
            (tensorPower X.presheaf X.ringCatSheaf.property L (-(k : ℤ) - 1)) L).symm ≪≫
          (Scheme.Modules.pullback p).mapIso
            (tensorPowerSuccIso X.presheaf X.ringCatSheaf.property L (-(k : ℤ) - 1) ≪≫
              tensorPowerReindex X.presheaf X.ringCatSheaf.property L
                (by ring : -(k : ℤ) - 1 + 1 = -(k : ℤ))) ≪≫ ek⟩

/-- `invertible_appTop_of_isTrivial` with quasi-coherence of the module replaced by the
invertibility it follows from. Stating the module as a hypothesis of type `X.Modules`, rather
than ascribing that type to a tensor power inside a proof, is what lets the quasi-coherence
instance be found: a tensor power has type
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
  X.ringCatSheaf.property)`, which is
definitionally but not syntactically `X.Modules`, and instance search is syntactic. -/
theorem invertible_appTop_of_isTrivial_of_isInvertible
    {S T : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {k : Y ⟶ T}
    (H : IsPullback p k iX q) [IsAffine S] [IsAffine T] [Flat q]
    [CompactSpace X] [QuasiSeparatedSpace X] (N : X.Modules)
    (hN : IsInvertible X.presheaf X.ringCatSheaf.property N)
    [Algebra Γ(X, ⊤) Γ(Y, ⊤)]
    (halg : ∀ r, algebraMap Γ(X, ⊤) Γ(Y, ⊤) r = (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom r)
    [Module.FaithfullyFlat Γ(X, ⊤) Γ(Y, ⊤)]
    (hN' : IsTrivial Y.presheaf Y.ringCatSheaf.property ((Scheme.Modules.pullback p).obj N)) :
    Module.Invertible Γ(X, ⊤) Γ(N, ⊤) :=
  have _hN'' : IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN
  have _ : N.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_of_isInvertible N
  invertible_appTop_of_isTrivial H N halg hN'

/-- **Invertibility of the global sections of every integer tensor power**, for an arbitrary
cartesian square with affine bases. This is `invertible_appTop_of_isTrivial` applied to
`L^{⊗ n}`, whose invertibility — hence quasi-coherence — comes from Tag 01CT (1), and whose
trivialization after pullback is `isTrivial_pullback_tensorPower`. -/
theorem invertible_globalSections_tensorPower_of_isTrivial
    {S T : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {k : Y ⟶ T}
    (H : IsPullback p k iX q) [IsAffine S] [IsAffine T] [Flat q]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [Algebra Γ(X, ⊤) Γ(Y, ⊤)]
    (halg : ∀ r, algebraMap Γ(X, ⊤) Γ(Y, ⊤) r = (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom r)
    [Module.FaithfullyFlat Γ(X, ⊤) Γ(Y, ⊤)]
    (hL : IsTrivial Y.presheaf Y.ringCatSheaf.property ((Scheme.Modules.pullback p).obj L))
    (n : ℤ) :
    letI : Module Γ(X, ⊤)
        ((tensorPower X.presheaf X.ringCatSheaf.property L n).val.obj (.op ⊤)) :=
      ((tensorPower X.presheaf X.ringCatSheaf.property L n).val.obj (.op ⊤)).isModule
    Module.Invertible Γ(X, ⊤)
      ((tensorPower X.presheaf X.ringCatSheaf.property L n).val.obj (.op ⊤)) :=
  invertible_appTop_of_isTrivial_of_isInvertible p H
    (tensorPower X.presheaf X.ringCatSheaf.property L n)
    (tensorPower_isInvertible X.presheaf X.ringCatSheaf.property L n) halg
    (isTrivial_pullback_tensorPower p L hL n)

/-- **Stacks Project, Tag 0CDX, the clause about the global sections of the inverse sheaf.** For
a quasi-compact, quasi-separated scheme `X` over `A`, a faithfully flat ring map `φ : A →+* B`
and an invertible `𝒪_X`-module `L` whose pullback to `X_B` is trivial, the global sections
`Γ(X, L^{⊗ -1})` of the inverse tensor power form an invertible module over the global functions
`Γ(X, 𝒪_X)`. -/
@[stacks 0CDX "global sections of the inverse sheaf"]
theorem invertible_globalSections_tensorInverse_of_faithfullyFlat_trivialization
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.FaithfullyFlat)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules)
    [hinv : IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hL : IsTrivial
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).ringCatSheaf.property
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj L)) :
    letI : Module Γ(X, ⊤)
        ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤)) :=
      ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤)).isModule
    Module.Invertible Γ(X, ⊤)
      ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤)) := by
  have hninv : IsInvertible X.presheaf X.ringCatSheaf.property
      (tensorPower X.presheaf X.ringCatSheaf.property L (-1)) :=
    tensorPower_isInvertible X.presheaf X.ringCatSheaf.property L (-1)
  exact invertible_globalSections_of_faithfullyFlat_trivialization φ hφ f
    (tensorPower X.presheaf X.ringCatSheaf.property L (-1))
    (isTrivial_pullback_tensorPower
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))) L hL (-1))

end Stacks.AlgebraicGeometry.PicardBaseChange

end
