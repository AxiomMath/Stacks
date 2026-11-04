module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.TwistHomNaturality
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.ProperMapping

/-!
# The completion of a finite sum of negative twists, and maps out of it

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `d : ℤ` and `t : ℕ`. This file builds the
`t`-fold direct sum `(L ^⊗ (-d)) ^⊕ t` as a coherent `𝒪_X`-module, applies the completion functor
of [Stacks, Tag 0880] to it, and assembles a family of `t` compatible sections into a morphism
from that completion into an arbitrary coherent adic system.

This is the target object of the generation argument of [Stacks, Tag 0885]. In the source's
notation, [Stacks, Tag 01Q3] clause (8) presents a coherent module as a quotient of a finite sum
of negative twists of an `f`-ample `L`; the generation statement needs that sum's *completion* to
map onto a given object of `Coh(X, 𝓘)`, and the map is built from a family of `t` sections of
`𝓕_n ⊗ L ^⊗ d` compatible across the system. Nothing here constructs such a family: the family is
a binder of `Stacks.Algebraization.descCompletionNegativeTwistSum`, and producing it — from the
`H¹`-vanishing of [Stacks, Tag 0884] through the long exact sequence and the lifting of a
generating family — is the rest of that argument.

## Main definitions

* `Stacks.Algebraization.negativeTwistSum` — the `t`-fold direct sum `(L ^⊗ (-d)) ^⊕ t` as an
  `𝒪_X`-module, with `Stacks.Algebraization.negativeTwistSumι` its inclusions and
  `Stacks.Algebraization.negativeTwistSumDesc` the map out of it determined by `t` morphisms out
  of `L ^⊗ (-d)`.
* `Stacks.Algebraization.negativeTwistSumCoherent` — the same sum as an object of
  `AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf`, on a locally Noetherian `X`.
* `Stacks.Algebraization.completionNegativeTwistSum` — its completion along a quasi-coherent
  ideal, an object of `Stacks.Coherent.CoherentAdicSystems`.
* `Stacks.Algebraization.descCompletionNegativeTwistSum` — the morphism from that completion into
  a coherent adic system determined by a compatible family of `t` sections, recorded as morphisms
  out of the negative twist.
* `Stacks.Algebraization.descCompletionNegativeTwistSumOfSections` — the same morphism from the
  family given as genuine global sections of the twists `𝓕_n ⊗ L ^⊗ d`, whose compatibility is
  carried by the twisted transition maps of the system. This is the form the lifting step of the
  generation argument delivers.

## Main results

* `Stacks.Algebraization.isCoherent_negativeTwistSum` — the sum is coherent: a tensor power of an
  invertible module is invertible, an invertible module on a locally Noetherian scheme is
  coherent ([Stacks, Tag 01XZ]), and coherent modules are closed under finite direct sums.
* `Stacks.Algebraization.completionNegativeTwistSum_obj` — the levelwise description: the `n`-th
  term of the completion is `((L ^⊗ (-d)) ^⊕ t) / 𝓘 ^ (n + 1)`.
* `Stacks.Algebraization.completionProjection_descCompletionNegativeTwistSum` — the
  normalization that pins the assembled morphism down: at level `n`, precomposed with the
  projection of the sum onto the `n`-th term of its completion, it is the map assembled from the
  family at level `n`. Since that projection is an epimorphism this determines the morphism, and
  it is what a proof that the morphism is an epimorphism has to work with.
  `Stacks.Algebraization.completionProjection_descCompletionNegativeTwistSumOfSections` is the
  same for the section-indexed form.

## Implementation notes

The assembly consumes a section of `𝓕_n ⊗ L ^⊗ d` as a morphism `L ^⊗ (-d) ⟶ 𝓕_n`, the two
being identified by `Hom(L ^⊗ (-d), 𝓕_n) ≅ Hom(𝒪_X, 𝓕_n ⊗ L ^⊗ d) ≅ Γ(X, 𝓕_n ⊗ L ^⊗ d)` for
invertible `L`; that identification is this library's `Stacks.AmpleCharacterization.twistHom`.
So `Stacks.Algebraization.descCompletionNegativeTwistSum` asks only that each of the `t`
morphisms commute with the transition maps of the system one step at a time, and
`Stacks.Algebraization.descCompletionNegativeTwistSumOfSections` asks the corresponding thing of
the sections themselves, naturality of `twistHom`
(`Stacks.AmpleCharacterization.twistHom_app_comp`) passing between the two.

`Stacks.Ample.tensorPowModule X L` is the family of integer tensor powers of [Stacks, Tag 01CU]
as a single function `ℤ → X.Modules`, so the negative twist `L ^⊗ (-d)` is that same constant at
`-d`; there is no separate constant for negative degree.

The direct sum is the biproduct of `X.Modules`, which has finite biproducts because it is
preadditive with finite products; the instance is not global and is turned on locally here, as in
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily`. Consumers of the definitions below
need not turn it on: the instance is baked into the terms.

The morphism out of the completion is built through the adjunction of
`Stacks.Algebraization.completionHomLimitEquiv` — maps out of a completion are maps into the
inverse limit — so the family only has to be turned into a cone on the system, which
`CategoryTheory.NatTrans.ofOpSequence` does from the one-step compatibility.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (d : ℤ) (t : ℕ)

/-! ### The finite sum of negative twists -/

/-- **The `t`-fold direct sum `(L ^⊗ (-d)) ^⊕ t` of a negative twist of an invertible module.**
The twist is `Stacks.Ample.tensorPowModule` of [Stacks, Tag 01CU] at `-d`; the sum is the
biproduct of `X.Modules`. -/
public def negativeTwistSum : X.Modules :=
  ⨁ fun _ : Fin t => Stacks.Ample.tensorPowModule X L (-d)

/-- The inclusion of the `j`-th summand of `Stacks.Algebraization.negativeTwistSum`. -/
public def negativeTwistSumι (j : Fin t) :
    Stacks.Ample.tensorPowModule X L (-d) ⟶ negativeTwistSum L d t :=
  biproduct.ι (fun _ : Fin t => Stacks.Ample.tensorPowModule X L (-d)) j

/-- **The map out of `(L ^⊗ (-d)) ^⊕ t` determined by `t` morphisms out of `L ^⊗ (-d)`.** -/
public def negativeTwistSumDesc {M : X.Modules}
    (g : Fin t → (Stacks.Ample.tensorPowModule X L (-d) ⟶ M)) : negativeTwistSum L d t ⟶ M :=
  biproduct.desc g

/-- The `j`-th inclusion into `(L ^⊗ (-d)) ^⊕ t` followed by the map determined by `g` is `g j`. -/
@[simp]
public theorem negativeTwistSumι_desc {M : X.Modules}
    (g : Fin t → (Stacks.Ample.tensorPowModule X L (-d) ⟶ M)) (j : Fin t) :
    negativeTwistSumι L d t j ≫ negativeTwistSumDesc L d t g = g j :=
  biproduct.ι_desc g j

/-- A morphism out of `(L ^⊗ (-d)) ^⊕ t` is determined by its restrictions to the summands. -/
public theorem negativeTwistSum_hom_ext {M : X.Modules} (f g : negativeTwistSum L d t ⟶ M)
    (h : ∀ j : Fin t, negativeTwistSumι L d t j ≫ f = negativeTwistSumι L d t j ≫ g) : f = g :=
  biproduct.hom_ext' _ _ h

/-- **The finite sum of negative twists is coherent:** on a locally Noetherian scheme,
`(L ^⊗ (-d)) ^⊕ t` is a coherent `𝒪_X`-module. -/
public theorem isCoherent_negativeTwistSum [AlgebraicGeometry.IsLocallyNoetherian X] :
    (negativeTwistSum L d t).IsCoherent := by
  let P : ObjectProperty X.Modules := fun N => N.IsCoherent
  let _ : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
  exact P.prop_of_iso
    (biproduct.isoCoproduct fun _ : Fin t => Stacks.Ample.tensorPowModule X L (-d)).symm
    (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_sigma_modules _ fun _ =>
      Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible
        (X := X) (Stacks.Ample.tensorPowModule X L (-d)))

/-- **`(L ^⊗ (-d)) ^⊕ t` as an object of `Coh(𝒪_X)`**, the category the completion functor of
[Stacks, Tag 0880] takes its argument in. -/
public def negativeTwistSumCoherent [AlgebraicGeometry.IsLocallyNoetherian X] :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨negativeTwistSum L d t, isCoherent_negativeTwistSum L d t⟩

/-- The underlying `𝒪_X`-module of `Stacks.Algebraization.negativeTwistSumCoherent` is
`Stacks.Algebraization.negativeTwistSum`. -/
@[simp]
public theorem negativeTwistSumCoherent_obj [AlgebraicGeometry.IsLocallyNoetherian X] :
    (negativeTwistSumCoherent L d t).obj = negativeTwistSum L d t :=
  rfl

/-! ### Its completion -/

variable [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- **The completion of `(L ^⊗ (-d)) ^⊕ t` along a quasi-coherent ideal**, an object of
`Coh(X, I)`. -/
public def completionNegativeTwistSum : Stacks.Coherent.CoherentAdicSystems I :=
  (completionFunctor X I).obj (negativeTwistSumCoherent L d t)

/-- **The levelwise description of the completion of `(L ^⊗ (-d)) ^⊕ t`:** its `n`-th term is the
quotient of the sum by `I ^ (n + 1)`. -/
public theorem completionNegativeTwistSum_obj (n : ℕ) :
    (completionNegativeTwistSum L d t I).obj.obj (op n) =
      idealPowerQuotient I (n + 1) (negativeTwistSum L d t) :=
  completionFunctor_obj X I (negativeTwistSumCoherent L d t) n

/-! ### Mapping out of the completion -/

variable (𝓕 : Stacks.Coherent.CoherentAdicSystems I)
  (σ : Fin t → (n : ℕ) → (Stacks.Ample.tensorPowModule X L (-d) ⟶ 𝓕.obj.obj (op n)))

/-- The cone on a coherent adic system with vertex `(L ^⊗ (-d)) ^⊕ t` assembled from a compatible
family of `t` sections: at level `n` it is the map out of the sum whose `j`-th component is the
`j`-th member of the family at that level. -/
public def negativeTwistSumCone
    (hσ : ∀ (j : Fin t) (n : ℕ),
      σ j (n + 1) ≫ 𝓕.obj.map (homOfLE (Nat.le_succ n)).op = σ j n) :
    Cone 𝓕.obj where
  pt := negativeTwistSum L d t
  π := NatTrans.ofOpSequence (fun n => negativeTwistSumDesc L d t fun j => σ j n) fun n =>
    (Category.id_comp (negativeTwistSumDesc L d t fun j => σ j n)).trans
      (negativeTwistSum_hom_ext L d t _ _ fun j =>
        (negativeTwistSumι_desc L d t (fun j => σ j n) j).trans
          ((hσ j n).symm.trans
            ((congrArg (fun k => k ≫ 𝓕.obj.map (homOfLE (Nat.le_succ n)).op)
                  (negativeTwistSumι_desc L d t (fun j => σ j (n + 1)) j)).symm.trans
              (Category.assoc _ _ _))))

/-- **The morphism out of the completion of `(L ^⊗ (-d)) ^⊕ t` determined by a compatible family
of `t` sections.** A section of `𝓕_n ⊗ L ^⊗ d` is recorded as a morphism `L ^⊗ (-d) ⟶ 𝓕_n`;
`hσ` asks that each of the `t` members commute with the transition maps of the system one step at
a time.

The morphism is the one the adjunction `Stacks.Algebraization.completionHomLimitEquiv` attaches
to the induced map `(L ^⊗ (-d)) ^⊕ t ⟶ lim 𝓕_n`. -/
public def descCompletionNegativeTwistSum
    (hσ : ∀ (j : Fin t) (n : ℕ),
      σ j (n + 1) ≫ 𝓕.obj.map (homOfLE (Nat.le_succ n)).op = σ j n) :
    completionNegativeTwistSum L d t I ⟶ 𝓕 :=
  homToAdicSystem (negativeTwistSumCoherent L d t) 𝓕
    (limit.lift 𝓕.obj (negativeTwistSumCone L d t I 𝓕 σ hσ))

/-- **The normalization of `Stacks.Algebraization.descCompletionNegativeTwistSum`.** At level `n`,
precomposing with the projection of the sum onto the `n`-th term of its completion gives back the
map assembled from the family at level `n`. -/
public theorem completionProjection_descCompletionNegativeTwistSum
    (hσ : ∀ (j : Fin t) (n : ℕ),
      σ j (n + 1) ≫ 𝓕.obj.map (homOfLE (Nat.le_succ n)).op = σ j n) (n : ℕ) :
    completionProjection X I (negativeTwistSumCoherent L d t) n ≫
        (descCompletionNegativeTwistSum L d t I 𝓕 σ hσ).hom.app (op n) =
      negativeTwistSumDesc L d t fun j => σ j n :=
  (completionProjection_homToAdicSystem (negativeTwistSumCoherent L d t) 𝓕
    (limit.lift 𝓕.obj (negativeTwistSumCone L d t I 𝓕 σ hσ)) (op n)).trans
      (limit.lift_π (negativeTwistSumCone L d t I 𝓕 σ hσ) (op n))

/-! ### The same, from a compatible family of sections of the twists -/

section Sections

open CategoryTheory.MonoidalCategory

attribute [local instance] Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **The morphism out of the completion of `(L ^⊗ (-d)) ^⊕ t` determined by `t` families of
global sections of the twists `𝓕_n ⊗ L ^⊗ d`, compatible across the system.** The
compatibility `hs` says that the transition map of the system, twisted by `L ^⊗ d`, carries the
section at level `n + 1` to the section at level `n`.

Each section is turned into a morphism `L ^⊗ (-d) ⟶ 𝓕_n` by
`Stacks.AmpleCharacterization.twistHom`, and `Stacks.AmpleCharacterization.twistHom_app_comp`
turns `hs` into the compatibility of those morphisms. -/
public def descCompletionNegativeTwistSumOfSections
    (s : Fin t → (n : ℕ) → Γ(𝓕.obj.obj (op n) ⊗ Stacks.Ample.tensorPowModule X L d, ⊤))
    (hs : ∀ (j : Fin t) (n : ℕ),
      ((𝓕.obj.map (homOfLE (Nat.le_succ n)).op ▷
        Stacks.Ample.tensorPowModule X L d).app ⊤) (s j (n + 1)) = s j n) :
    completionNegativeTwistSum L d t I ⟶ 𝓕 :=
  descCompletionNegativeTwistSum L d t I 𝓕
    (fun j n => Stacks.AmpleCharacterization.twistHom L (𝓕.obj.obj (op n)) d (s j n))
    fun j n =>
      (Stacks.AmpleCharacterization.twistHom_app_comp L
          (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) d (s j (n + 1))).symm.trans
        (congrArg (Stacks.AmpleCharacterization.twistHom L (𝓕.obj.obj (op n)) d) (hs j n))

/-- **The normalization of `Stacks.Algebraization.descCompletionNegativeTwistSumOfSections`**: at
level `n`, precomposing with the projection of the sum onto the `n`-th term of its completion
gives the map out of the sum whose `j`-th component is the morphism
`Stacks.AmpleCharacterization.twistHom` attaches to the `j`-th section at that level. -/
public theorem completionProjection_descCompletionNegativeTwistSumOfSections
    (s : Fin t → (n : ℕ) → Γ(𝓕.obj.obj (op n) ⊗ Stacks.Ample.tensorPowModule X L d, ⊤))
    (hs : ∀ (j : Fin t) (n : ℕ),
      ((𝓕.obj.map (homOfLE (Nat.le_succ n)).op ▷
        Stacks.Ample.tensorPowModule X L d).app ⊤) (s j (n + 1)) = s j n) (n : ℕ) :
    completionProjection X I (negativeTwistSumCoherent L d t) n ≫
        (descCompletionNegativeTwistSumOfSections L d t I 𝓕 s hs).hom.app (op n) =
      negativeTwistSumDesc L d t fun j =>
        Stacks.AmpleCharacterization.twistHom L (𝓕.obj.obj (op n)) d (s j n) :=
  completionProjection_descCompletionNegativeTwistSum L d t I 𝓕 _ _ n

end Sections

end Stacks.Algebraization

end
