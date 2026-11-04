module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DiagonalConormal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
import StacksCore.Tactic.StacksAttribute

/-!
# The split sequence of the diagonal: `0 → Ω_{X/S} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S} → 0`

Let `f : X ⟶ S` be a morphism of schemes, write `W = X ×_S X` with projections `pr_1`, `pr_2`
and structure morphism `pr_1 ≫ f`, and let `Δ : X ⟶ W` be the diagonal.  [Stacks, Tag 01V1]
gives `Ω_{W/S} = pr_1^* Ω_{X/S} ⊕ pr_2^* Ω_{X/S}`; pulling this back along the diagonal, and
using `Δ ≫ pr_i = id`, identifies

```
Δ^* Ω_{W/S} = Ω_{X/S} ⊕ Ω_{X/S}
```

Under that identification the second arrow `Δ^* Ω_{W/S} ⟶ Ω_{X/S}` of the conormal sequence of
`Δ` — the canonical map of [Stacks, Tag 01UV] — is `(1, 1)`, and it is a *split* surjection
because `Δ` has the global left inverse `pr_1` over `S` ([Stacks, Tag 0474]).  Its kernel is
`Ω_{X/S}` embedded by `(-1, 1)`, and that is the left arrow of the canonical short exact
sequence

```
0 → 𝒞_{X/W} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S} → 0
```

of [Stacks, Tag 060N], the left-hand term being identified with `Ω_{X/S}` by
[Stacks, Tag 08S2] (`Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal`).  The
sign is fixed by the source's convention `d_{X/S} b = s_2(b) - s_1(b)`, and the footnote of the
remark is `Stacks.DiagonalSplitSequence.pullbackSection_d_diffSection`: the section
`p_2^♯ b - p_1^♯ b` of the ideal sheaf of `Δ` has `Δ^* d_{W/S}(p_2^♯ b - p_1^♯ b) =
pr_2^* d_{X/S} b - pr_1^* d_{X/S} b`.

## Main definitions

* `Stacks.DiagonalSplitSequence.retractionComparison`: for `i ≫ p = 𝟙 Z`, the comparison
  isomorphism `M ⟶ i^* p^* M` built from the pullback pseudofunctor, together with its action on
  sections.
* `Stacks.DiagonalSplitSequence.diagonalDifferentialsMap`: the right arrow, i.e. the canonical
  map `Δ^* Ω_{W/S} ⟶ Ω_{X/S}` of [Stacks, Tag 01UV].
* `Stacks.DiagonalSplitSequence.projInclusion`: for a projection `p` with `Δ ≫ p = 𝟙 X`, the
  inclusion `Ω_{X/S} ⟶ Δ^* Ω_{W/S}` it determines; `fstInclusion` and `sndInclusion` are its two
  instances.
* `Stacks.DiagonalSplitSequence.diagonalBiprodIso`: **[Stacks, Tag 060N]**, the identification
  `Ω_{X/S} ⊕ Ω_{X/S} ≅ Δ^* Ω_{W/S}`.
* `Stacks.DiagonalSplitSequence.leftArrow`: the map `(-1, 1)` into `Δ^* Ω_{W/S}`.
* `Stacks.DiagonalSplitSequence.shortComplex` and
  `Stacks.DiagonalSplitSequence.splitting`: the three-term complex
  `Ω_{X/S} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S}` with arrows `(-1, 1)` and `(1, 1)`, and its splitting.

## Main results

* `Stacks.DiagonalSplitSequence.projInclusion_comp_diagonalDifferentialsMap`: each projection
  inclusion is a section of the right arrow.
* `Stacks.DiagonalSplitSequence.diagonalBiprodIso_hom_comp_diagonalDifferentialsMap`:
  **[Stacks, Tag 060N]**, the right arrow is `(1, 1)`.
* `Stacks.DiagonalSplitSequence.isSplitEpi_diagonalDifferentialsMap`: **[Stacks, Tag 060N]**, the
  right arrow is a split surjection.
* `Stacks.DiagonalSplitSequence.leftArrow_eq`: **[Stacks, Tag 060N]**, the left arrow is the
  difference `sndInclusion - fstInclusion` of the two projection inclusions, which is `(-1, 1)`.
* `Stacks.DiagonalSplitSequence.pullbackSection_d_diffSection`: **[Stacks, Tag 060N]**, the
  footnote, on sections.
* `Stacks.DiagonalSplitSequence.shortComplex_shortExact`: **[Stacks, Tag 060N]**, the canonical
  short exact sequence.

## Implementation notes

The identification of the middle term is `biprod.desc fstInclusion sndInclusion`.  It is an
isomorphism because it factors as the isomorphism `biprod.map` of the two comparison
isomorphisms `Ω_{X/S} ≅ Δ^* pr_i^* Ω_{X/S}`, followed by `Functor.mapBiprod` for the pullback
along `Δ` — which preserves binary biproducts, being a left adjoint — followed by the pullback
along `Δ` of the isomorphism of [Stacks, Tag 01V1].

The retraction identity `projInclusion ≫ diagonalDifferentialsMap = 𝟙` is the uniqueness part of
[Stacks, Tag 01UV]: the composite is the canonical map of `Δ ≫ pr_i = 𝟙 X`, which is the
comparison isomorphism `(𝟙 X)^* Ω_{X/S} ≅ Ω_{X/S}`.  This is the argument that
`Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_of_retraction` runs for a
general left inverse; recorded here as the explicit equation, which is what identifies the right
arrow with `(1, 1)` rather than merely exhibiting it as split.

The left-hand term of the source's sequence is the conormal sheaf `𝒞_{X/W}`, and the source
states the left arrow after identifying it with `Ω_{X/S}` by [Stacks, Tag 08S2]; that is how the
sequence is written here.  Composites mixing the conormal sheaf, which the repository builds in
`SheafOfModules (ringSheaf X.toRingedSpace)`, with `biprod` in `X.Modules` are not formed: the
two spellings of that category are definitionally but not syntactically equal, and
instance search for `HasBinaryBiproduct` and for the zero morphism does not see through the
difference.

The first arrow `𝒞_{Z/X} ⟶ i^* Ω_{X/S}` of the conormal sequence of [Stacks, Tag 01UZ] is not
available in this repository for a general immersion, so the left arrow is given through the
direct sum decomposition rather than as that map specialized to `Δ`.  What ties the two together
is the footnote `Stacks.DiagonalSplitSequence.pullbackSection_d_diffSection`, which computes
`Δ^* d_{W/S}` on the generator `p_2^♯ b - p_1^♯ b` of the ideal sheaf of the diagonal and finds
exactly `(-1, 1)` applied to `d_{X/S} b`.

## References

* [Stacks Project, Tag 060N](https://stacks.math.columbia.edu/tag/060N)
* [Stacks Project, Tag 01V1](https://stacks.math.columbia.edu/tag/01V1)
* [Stacks Project, Tag 0474](https://stacks.math.columbia.edu/tag/0474)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.DiagonalSplitSequence

/-! ### The comparison isomorphism attached to a retraction -/

section Retraction

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ Z)

/-- The unit of `(𝟙)^* ⊣ (𝟙)_*` is undone by the identification of the pullback along an
identity with the identity functor. -/
private theorem pullbackId_hom_val_app_pullbackSection {Z : Scheme.{u}} (M : Z.Modules)
    (U : Z.Opens) (h : U ≤ (𝟙 Z) ⁻¹ᵁ U) (s : M.val.obj (op U)) :
    (((Scheme.Modules.pullbackId Z).hom.app M).val.app (op U))
        (Scheme.Modules.pullbackSection (𝟙 Z) M U U h s) = s := by
  rw [show Scheme.Modules.pullbackSection (𝟙 Z) M U U h s =
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)).unit.app M).val.app (op U)) s from
    Stacks.Conormal.pullbackSection_self (𝟙 Z) M U s]
  have key := congrArg (fun q : M ⟶ (Scheme.Modules.pushforward (𝟙 Z)).obj M =>
      (Scheme.Modules.Hom.app q U) s) (AlgebraicGeometry.pullbackId_unit M)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardId_inv_app_app] at key
  exact key

/-- An open of `Z` lies in the preimage under a retracted morphism of the preimage of itself. -/
theorem le_preimage_preimage (hp : i ≫ p = 𝟙 Z) (U : Z.Opens) : U ≤ i ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hp, Scheme.Hom.id_preimage]

/-- **The comparison map `M ⟶ i^* p^* M` of a retraction `i ≫ p = 𝟙`**, the composite of the
three structural comparisons of the pullback pseudofunctor. -/
noncomputable def retractionComparison (hp : i ≫ p = 𝟙 Z) (M : Z.Modules) :
    M ⟶ (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackId Z).inv.app M ≫ (Scheme.Modules.pullbackCongr hp).inv.app M ≫
    (Scheme.Modules.pullbackComp i p).inv.app M

/-- The inverse of `Stacks.DiagonalSplitSequence.retractionComparison`. -/
noncomputable def retractionComparisonInv (hp : i ≫ p = 𝟙 Z) (M : Z.Modules) :
    (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback p).obj M) ⟶ M :=
  (Scheme.Modules.pullbackComp i p).hom.app M ≫ (Scheme.Modules.pullbackCongr hp).hom.app M ≫
    (Scheme.Modules.pullbackId Z).hom.app M

/-- `Stacks.DiagonalSplitSequence.retractionComparisonInv` is a left inverse of
`Stacks.DiagonalSplitSequence.retractionComparison`. -/
theorem retractionComparison_comp (hp : i ≫ p = 𝟙 Z) (M : Z.Modules) :
    retractionComparison i p hp M ≫ retractionComparisonInv i p hp M = 𝟙 M := by
  simp [retractionComparison, retractionComparisonInv]

/-- `Stacks.DiagonalSplitSequence.retractionComparisonInv` is an isomorphism. -/
instance isIso_retractionComparisonInv (hp : i ≫ p = 𝟙 Z) (M : Z.Modules) :
    IsIso (retractionComparisonInv i p hp M) := by
  rw [retractionComparisonInv]; infer_instance

/-- The comparison map `M ⟶ i^* p^* M` of a retraction `i ≫ p = 𝟙` is an isomorphism. -/
instance isIso_retractionComparison (hp : i ≫ p = 𝟙 Z) (M : Z.Modules) :
    IsIso (retractionComparison i p hp M) := by
  rw [retractionComparison]; infer_instance

/-- `Stacks.DiagonalSplitSequence.retractionComparison` as an isomorphism. -/
noncomputable def retractionIso (hp : i ≫ p = 𝟙 Z) (M : Z.Modules) :
    M ≅ (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback p).obj M) :=
  asIso (retractionComparison i p hp M)

private theorem retractionComparisonInv_app_pullbackSection (hp : i ≫ p = 𝟙 Z)
    (M : Z.Modules) (U : Z.Opens) (s : M.val.obj (op U)) :
    (Scheme.Modules.Hom.app (retractionComparisonInv i p hp M) U)
        (Scheme.Modules.pullbackSection i ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) U
          (le_preimage_preimage i p hp U)
          (Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl s)) = s := by
  have h₁ : U ≤ (i ≫ p) ⁻¹ᵁ U := by rw [hp]; exact le_rfl
  have h₂ : U ≤ (𝟙 Z) ⁻¹ᵁ U := le_rfl
  show (((Scheme.Modules.pullbackId Z).hom.app M).val.app (op U))
    ((((Scheme.Modules.pullbackCongr hp).hom.app M).val.app (op U))
      ((((Scheme.Modules.pullbackComp i p).hom.app M).val.app (op U)) _)) = s
  rw [Scheme.Modules.pullbackSection_comp i p M U (p ⁻¹ᵁ U) U le_rfl
      (le_preimage_preimage i p hp U) h₁ s,
    Scheme.Modules.pullbackSection_congr hp M U U h₁ h₂ s]
  exact pullbackId_hom_val_app_pullbackSection M U h₂ s

/-- **The comparison map of a retraction, on sections.**  For `i ≫ p = 𝟙 Z` the map
`M ⟶ i^* p^* M` carries a section of `M` over `U` to its pullback along `p` and then along
`i`. -/
theorem retractionComparison_val_app (hp : i ≫ p = 𝟙 Z) (M : Z.Modules) (U : Z.Opens)
    (s : M.val.obj (op U)) :
    ((retractionComparison i p hp M).val.app (op U)) s =
      Scheme.Modules.pullbackSection i ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) U
        (le_preimage_preimage i p hp U)
        (Scheme.Modules.pullbackSection p M U (p ⁻¹ᵁ U) le_rfl s) := by
  refine (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (retractionComparisonInv i p hp M) U)).injective ?_
  rw [retractionComparisonInv_app_pullbackSection i p hp M U s]
  show ((retractionComparison i p hp M ≫ retractionComparisonInv i p hp M).val.app (op U)) s = s
  rw [retractionComparison_comp]
  rfl

end Retraction

/-! ### The two arrows -/

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Pulling a section of the structure sheaf back is additive. -/
private theorem pullbackSection_sub {Z C : Scheme.{u}} (a : Z ⟶ C) (F : C.Modules)
    (U : C.Opens) (V : Z.Opens) (h : V ≤ a ⁻¹ᵁ U) (x y : F.val.obj (op U)) :
    Scheme.Modules.pullbackSection a F U V h (x - y) =
      Scheme.Modules.pullbackSection a F U V h x -
        Scheme.Modules.pullbackSection a F U V h y :=
  (congrArg
      (ConcreteCategory.hom (((Scheme.Modules.pullback a).obj F).val.map (homOfLE h).op))
      (map_sub (ConcreteCategory.hom
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app F).val.app (op U)))
        x y)).trans
    (map_sub _ _ _)

/-- The diagonal is a morphism over `S`, for the structure morphism `pr₁ ≫ f` of `X ×_S X`. -/
theorem diagonal_comp_structureMorphism :
    pullback.diagonal f ≫ (pullback.fst f f ≫ f) = f ≫ 𝟙 S := by simp

/-- **The second arrow of the conormal sequence of the diagonal**: the canonical map
`Δ^* Ω_{X ×_S X/S} ⟶ Ω_{X/S}` of [Stacks, Tag 01UV]. -/
noncomputable def diagonalDifferentialsMap :
    (Scheme.Modules.pullback (pullback.diagonal f)).obj
        (relativeDifferentials (pullback.fst f f ≫ f)) ⟶ relativeDifferentials f :=
  relativeDifferentialsMap (pullback.diagonal f) (pullback.fst f f ≫ f) f (𝟙 S)
    (diagonal_comp_structureMorphism f)

/-- **The inclusion of a projection**: for a morphism `p : X ×_S X ⟶ X` over `S` which is a left
inverse of the diagonal, the composite of the comparison `Ω_{X/S} ≅ Δ^* p^* Ω_{X/S}` with the
pullback along `Δ` of the canonical map `p^* Ω_{X/S} ⟶ Ω_{X ×_S X/S}` of [Stacks, Tag 01UV]. -/
noncomputable def projInclusion (p : pullback f f ⟶ X)
    (hp : pullback.diagonal f ≫ p = 𝟙 X) (hpf : p ≫ f = pullback.fst f f ≫ f) :
    relativeDifferentials f ⟶ (Scheme.Modules.pullback (pullback.diagonal f)).obj
      (relativeDifferentials (pullback.fst f f ≫ f)) :=
  retractionComparison (pullback.diagonal f) p hp (relativeDifferentials f) ≫
    (Scheme.Modules.pullback (pullback.diagonal f)).map
      (relativeDifferentialsMap p f (pullback.fst f f ≫ f) (𝟙 S)
        (hpf.trans (Category.comp_id _).symm))

/-- **Each projection inclusion is a section of the second arrow.**  This is the splitting of
[Stacks, Tag 0474] for the diagonal, whose left inverses `pr₁` and `pr₂` are global, in the
explicit form of the identity `pr_i ∘ Δ = id` on differentials. -/
theorem projInclusion_comp_diagonalDifferentialsMap (p : pullback f f ⟶ X)
    (hp : pullback.diagonal f ≫ p = 𝟙 X) (hpf : p ≫ f = pullback.fst f f ≫ f) :
    projInclusion f p hp hpf ≫ diagonalDifferentialsMap f = 𝟙 (relativeDifferentials f) := by
  have hA : IsRelativeDifferentialsMap p f (pullback.fst f f ≫ f)
      (relativeDifferentialsMap p f (pullback.fst f f ≫ f) (𝟙 S)
        (hpf.trans (Category.comp_id _).symm)) :=
    (isRelativeDifferentialsMap_iff_eq p f (pullback.fst f f ≫ f) (𝟙 S) _ _).mpr rfl
  have hB : IsRelativeDifferentialsMap (pullback.diagonal f) (pullback.fst f f ≫ f) f
      (diagonalDifferentialsMap f) :=
    (isRelativeDifferentialsMap_iff_eq (pullback.diagonal f) (pullback.fst f f ≫ f) f (𝟙 S)
      (diagonal_comp_structureMorphism f) _).mpr rfl
  have e1 := ((hA.comp hB).congr_left hp).unique (𝟙 S) (by simp)
    (isRelativeDifferentialsMap_id f)
  rw [projInclusion, diagonalDifferentialsMap, retractionComparison]
  simp only [Category.assoc]
  rw [show (Scheme.Modules.pullbackCongr hp).inv.app (relativeDifferentials f) ≫
      (Scheme.Modules.pullbackComp (pullback.diagonal f) p).inv.app (relativeDifferentials f) ≫
        (Scheme.Modules.pullback (pullback.diagonal f)).map
          (relativeDifferentialsMap p f (pullback.fst f f ≫ f) (𝟙 S)
            (hpf.trans (Category.comp_id _).symm)) ≫
        relativeDifferentialsMap (pullback.diagonal f) (pullback.fst f f ≫ f) f (𝟙 S)
          (diagonal_comp_structureMorphism f) =
      (Scheme.Modules.pullbackId X).hom.app (relativeDifferentials f) from e1]
  exact (Scheme.Modules.pullbackId X).inv_hom_id_app (relativeDifferentials f)

/-- **The projection inclusion, on sections.**  It carries the universal differential `d b` of a
local section `b` of `𝒪_X` over `U` to the pullback along `Δ` of the universal differential of
`p^♯ b`. -/
theorem projInclusion_val_app_d (p : pullback f f ⟶ X)
    (hp : pullback.diagonal f ≫ p = 𝟙 X) (hpf : p ≫ f = pullback.fst f f ≫ f)
    (U : X.Opens) (b : Γ(X, U)) :
    ((projInclusion f p hp hpf).val.app (op U)) ((universalRelativeDerivation f).d b) =
      Scheme.Modules.pullbackSection (pullback.diagonal f)
        (relativeDifferentials (pullback.fst f f ≫ f)) (p ⁻¹ᵁ U) U
        (le_preimage_preimage (pullback.diagonal f) p hp U)
        ((universalRelativeDerivation (pullback.fst f f ≫ f)).d ((p.app U).hom b)) := by
  show ((((Scheme.Modules.pullback (pullback.diagonal f)).map
      (relativeDifferentialsMap p f (pullback.fst f f ≫ f) (𝟙 S)
        (hpf.trans (Category.comp_id _).symm))).val.app (op U)))
    (((retractionComparison (pullback.diagonal f) p hp
      (relativeDifferentials f)).val.app (op U))
        ((universalRelativeDerivation f).d b)) = _
  rw [retractionComparison_val_app, Scheme.Modules.pullbackSection_naturality,
    Scheme.Hom.relativeDifferentialsMap_pullbackSection, Scheme.Hom.appLE_preimage_self]

/-! ### The direct sum decomposition of the pullback along the diagonal -/

/-- The inclusion `Ω_{X/S} ⟶ Δ^* Ω_{X ×_S X/S}` attached to the first projection. -/
noncomputable def fstInclusion :
    relativeDifferentials f ⟶ (Scheme.Modules.pullback (pullback.diagonal f)).obj
      (relativeDifferentials (pullback.fst f f ≫ f)) :=
  projInclusion f (pullback.fst f f) (pullback.diagonal_fst f) rfl

/-- The inclusion `Ω_{X/S} ⟶ Δ^* Ω_{X ×_S X/S}` attached to the second projection. -/
noncomputable def sndInclusion :
    relativeDifferentials f ⟶ (Scheme.Modules.pullback (pullback.diagonal f)).obj
      (relativeDifferentials (pullback.fst f f ≫ f)) :=
  projInclusion f (pullback.snd f f) (pullback.diagonal_snd f) pullback.condition.symm

/-- The map `Ω_{X/S} ⊕ Ω_{X/S} ⟶ Δ^* Ω_{X ×_S X/S}` given by the two projection inclusions is
an isomorphism. -/
instance isIso_biprodDesc_inclusion :
    IsIso (biprod.desc (fstInclusion f) (sndInclusion f)) := by
  have h01V1 := isIso_biprodDesc_relativeDifferentialsMap (pullback.fst f f)
    (pullback.snd f f) f f (IsPullback.of_hasPullback f f)
  have hpres : PreservesBinaryBiproduct
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentials f))
      ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentials f))
      (Scheme.Modules.pullback (pullback.diagonal f)) :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  rw [show biprod.desc (fstInclusion f) (sndInclusion f) =
      (biprod.mapIso
            (retractionIso (pullback.diagonal f) (pullback.fst f f)
              (pullback.diagonal_fst f) (relativeDifferentials f))
            (retractionIso (pullback.diagonal f) (pullback.snd f f)
              (pullback.diagonal_snd f) (relativeDifferentials f))).hom ≫
        ((Scheme.Modules.pullback (pullback.diagonal f)).mapBiprod _ _).inv ≫
          (Scheme.Modules.pullback (pullback.diagonal f)).map
            (biprod.desc
              (relativeDifferentialsMap (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 S)
                (Category.comp_id _).symm)
              (relativeDifferentialsMap (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 S)
                (pullback.condition.symm.trans (Category.comp_id _).symm))) from ?_]
  · infer_instance
  · rw [Limits.biprod.mapBiprod_inv_map_desc]
    refine biprod.hom_ext' _ _ ?_ ?_ <;>
      simp [fstInclusion, sndInclusion, projInclusion, retractionIso]

/-- **[Stacks, Tag 060N]: `Δ^* Ω_{X ×_S X/S} = Ω_{X/S} ⊕ Ω_{X/S}`.**  The direct sum
decomposition `Ω_{X ×_S X/S} = pr_1^* Ω_{X/S} ⊕ pr_2^* Ω_{X/S}` of [Stacks, Tag 01V1], pulled
back along the diagonal: the two summands become `Ω_{X/S}` because `Δ ≫ pr_i = id`. -/
@[stacks 060N "the middle term: Δ^*Ω_{X ×_S X/S} = Ω_{X/S} ⊕ Ω_{X/S}"]
noncomputable def diagonalBiprodIso :
    relativeDifferentials f ⊞ relativeDifferentials f ≅
      (Scheme.Modules.pullback (pullback.diagonal f)).obj
        (relativeDifferentials (pullback.fst f f ≫ f)) :=
  asIso (biprod.desc (fstInclusion f) (sndInclusion f))

/-- **[Stacks, Tag 060N]: the right arrow is `(1, 1)`.**  Under the identification
`Δ^* Ω_{X ×_S X/S} = Ω_{X/S} ⊕ Ω_{X/S}` the canonical map `Δ^* Ω_{X ×_S X/S} ⟶ Ω_{X/S}` of
[Stacks, Tag 01UV] — the second arrow of the conormal sequence of `Δ` — is `(1, 1)`. -/
@[stacks 060N "the right arrow is (1,1)"]
theorem diagonalBiprodIso_hom_comp_diagonalDifferentialsMap :
    (diagonalBiprodIso f).hom ≫ diagonalDifferentialsMap f =
      biprod.desc (𝟙 (relativeDifferentials f)) (𝟙 (relativeDifferentials f)) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
    simp [diagonalBiprodIso, fstInclusion, sndInclusion,
      projInclusion_comp_diagonalDifferentialsMap]

/-- **[Stacks, Tag 060N]: the right arrow is a split surjection.**  The diagonal has the global
left inverse `pr_1` over `S`, so the second arrow of its conormal sequence is a split
epimorphism; this is [Stacks, Tag 0474] for `Δ`. -/
@[stacks 060N "the right arrow is a split surjection"]
instance isSplitEpi_diagonalDifferentialsMap : IsSplitEpi (diagonalDifferentialsMap f) :=
  IsSplitEpi.mk' ⟨fstInclusion f,
    projInclusion_comp_diagonalDifferentialsMap f (pullback.fst f f)
      (pullback.diagonal_fst f) rfl⟩

/-- **The left arrow `(-1, 1)` of [Stacks, Tag 060N]**, as a map into
`Δ^* Ω_{X ×_S X/S}` through the identification
`Stacks.DiagonalSplitSequence.diagonalBiprodIso`. -/
noncomputable def leftArrow :
    relativeDifferentials f ⟶ (Scheme.Modules.pullback (pullback.diagonal f)).obj
      (relativeDifferentials (pullback.fst f f ≫ f)) :=
  biprod.lift (-𝟙 (relativeDifferentials f)) (𝟙 (relativeDifferentials f)) ≫
    (diagonalBiprodIso f).hom

/-- The second projection of the direct sum decomposition, a retraction of the left arrow. -/
noncomputable def middleToDiff :
    (Scheme.Modules.pullback (pullback.diagonal f)).obj
        (relativeDifferentials (pullback.fst f f ≫ f)) ⟶ relativeDifferentials f :=
  (diagonalBiprodIso f).inv ≫ biprod.snd

/-- **[Stacks, Tag 060N]: the left arrow is `(-1, 1)`.**  Written through the identification
`Δ^* Ω_{X ×_S X/S} = Ω_{X/S} ⊕ Ω_{X/S}` it is the difference of the two projection
inclusions. -/
@[stacks 060N "the left arrow is (-1,1)"]
theorem leftArrow_eq : leftArrow f = sndInclusion f - fstInclusion f := by
  rw [leftArrow, diagonalBiprodIso, asIso_hom, biprod.lift_desc, Preadditive.neg_comp,
    Category.id_comp, Category.id_comp]
  abel

/-- `Stacks.DiagonalSplitSequence.middleToDiff` is a retraction of
`Stacks.DiagonalSplitSequence.leftArrow`. -/
theorem leftArrow_comp_middleToDiff :
    leftArrow f ≫ middleToDiff f = 𝟙 (relativeDifferentials f) := by
  rw [leftArrow, middleToDiff, Category.assoc, ← Category.assoc (diagonalBiprodIso f).hom,
    Iso.hom_inv_id, Category.id_comp, biprod.lift_snd]

/-- The left arrow `Ω_{X/S} ⟶ Δ^* Ω_{X ×_S X/S}` is a split monomorphism. -/
instance isSplitMono_leftArrow : IsSplitMono (leftArrow f) :=
  IsSplitMono.mk' ⟨middleToDiff f, leftArrow_comp_middleToDiff f⟩

/-- The composite of the left arrow with the second arrow `Δ^* Ω_{X ×_S X/S} ⟶ Ω_{X/S}` is zero. -/
theorem leftArrow_comp_diagonalDifferentialsMap :
    leftArrow f ≫ diagonalDifferentialsMap f = 0 := by
  rw [leftArrow, Category.assoc, diagonalBiprodIso_hom_comp_diagonalDifferentialsMap,
    biprod.lift_desc, Preadditive.neg_comp, Category.id_comp, neg_add_cancel]

/-! ### The footnote: the left arrow on sections -/

/-- Restricting a section of `𝒪_{X ×_S X}` pulled back along a projection, before taking its
universal differential and pulling that back along the diagonal, changes nothing. -/
private theorem pullbackSection_d_appLE (p : pullback f f ⟶ X) (hp : pullback.diagonal f ≫ p = 𝟙 X)
    (U : X.Opens) (e : Stacks.Diagonal.prodOpen f U ≤ p ⁻¹ᵁ U) (b : Γ(X, U)) :
    Scheme.Modules.pullbackSection (pullback.diagonal f)
        (relativeDifferentials (pullback.fst f f ≫ f)) (Stacks.Diagonal.prodOpen f U) U
        (Stacks.Diagonal.le_diagonal_preimage_prodOpen f U)
        ((universalRelativeDerivation (pullback.fst f f ≫ f)).d
          ((p.appLE U (Stacks.Diagonal.prodOpen f U) e).hom b)) =
      Scheme.Modules.pullbackSection (pullback.diagonal f)
        (relativeDifferentials (pullback.fst f f ≫ f)) (p ⁻¹ᵁ U) U
        (le_preimage_preimage (pullback.diagonal f) p hp U)
        ((universalRelativeDerivation (pullback.fst f f ≫ f)).d ((p.app U).hom b)) := by
  have happ : (p.appLE U (Stacks.Diagonal.prodOpen f U) e).hom b =
      ((pullback f f).presheaf.map (homOfLE e).op).hom ((p.app U).hom b) := by
    rw [Scheme.Hom.appLE]
    exact CommRingCat.comp_apply (p.app U)
      ((pullback f f).presheaf.map (homOfLE e).op) b
  have hdm : (universalRelativeDerivation (pullback.fst f f ≫ f)).d
        (((pullback f f).presheaf.map (homOfLE e).op).hom ((p.app U).hom b)) =
      ((relativeDifferentials (pullback.fst f f ≫ f)).val.map (homOfLE e).op)
        ((universalRelativeDerivation (pullback.fst f f ≫ f)).d ((p.app U).hom b)) :=
    (universalRelativeDerivation (pullback.fst f f ≫ f)).d_map (homOfLE e).op ((p.app U).hom b)
  rw [happ, hdm]
  exact (Stacks.Conormal.pullbackSection_restrict_source (pullback.diagonal f)
    (relativeDifferentials (pullback.fst f f ≫ f)) (p ⁻¹ᵁ U)
    (Stacks.Diagonal.prodOpen f U) e U
    (Stacks.Diagonal.le_diagonal_preimage_prodOpen f U)
    ((universalRelativeDerivation (pullback.fst f f ≫ f)).d ((p.app U).hom b))).symm

/-- The pullback along the diagonal of the universal differential of a difference. -/
private theorem pullbackSection_d_sub (U : X.Opens)
    (hd : U ≤ pullback.diagonal f ⁻¹ᵁ Stacks.Diagonal.prodOpen f U)
    (x y : Γ(pullback f f, Stacks.Diagonal.prodOpen f U)) :
    Scheme.Modules.pullbackSection (pullback.diagonal f)
        (relativeDifferentials (pullback.fst f f ≫ f)) (Stacks.Diagonal.prodOpen f U) U hd
        ((universalRelativeDerivation (pullback.fst f f ≫ f)).d (x - y)) =
      Scheme.Modules.pullbackSection (pullback.diagonal f)
          (relativeDifferentials (pullback.fst f f ≫ f)) (Stacks.Diagonal.prodOpen f U) U hd
          ((universalRelativeDerivation (pullback.fst f f ≫ f)).d x) -
        Scheme.Modules.pullbackSection (pullback.diagonal f)
          (relativeDifferentials (pullback.fst f f ≫ f)) (Stacks.Diagonal.prodOpen f U) U hd
          ((universalRelativeDerivation (pullback.fst f f ≫ f)).d y) := by
  rw [show (universalRelativeDerivation (pullback.fst f f ≫ f)).d (x - y) =
      (universalRelativeDerivation (pullback.fst f f ≫ f)).d x -
        (universalRelativeDerivation (pullback.fst f f ≫ f)).d y from map_sub _ _ _]
  exact pullbackSection_sub (pullback.diagonal f)
    (relativeDifferentials (pullback.fst f f ≫ f)) (Stacks.Diagonal.prodOpen f U) U hd _ _

/-- **[Stacks, Tag 060N], the footnote.**  The local section `d_{X/S} b = p_2^♯ b - p_1^♯ b` of
the ideal sheaf of the diagonal is carried by `d_{X ×_S X/S}`, pulled back along `Δ`, to
`pr_2^* d_{X/S} b - pr_1^* d_{X/S} b`; that is, to the image of `d_{X/S} b` under the map
`(-1, 1)` of the direct sum decomposition.  This is what fixes the sign of the left arrow. -/
@[stacks 060N "the footnote: the left arrow on sections"]
theorem pullbackSection_d_diffSection (U : X.Opens) (b : Γ(X, U)) :
    Scheme.Modules.pullbackSection (pullback.diagonal f)
        (relativeDifferentials (pullback.fst f f ≫ f)) (Stacks.Diagonal.prodOpen f U) U
        (Stacks.Diagonal.le_diagonal_preimage_prodOpen f U)
        ((universalRelativeDerivation (pullback.fst f f ≫ f)).d
          (Stacks.Diagonal.diffSection f U b)) =
      ((leftArrow f).val.app (op U)) ((universalRelativeDerivation f).d b) := by
  rw [leftArrow_eq]
  show _ = ((sndInclusion f).val.app (op U)) ((universalRelativeDerivation f).d b) -
    ((fstInclusion f).val.app (op U)) ((universalRelativeDerivation f).d b)
  rw [sndInclusion, fstInclusion, projInclusion_val_app_d, projInclusion_val_app_d]
  unfold Stacks.Diagonal.diffSection
  rw [pullbackSection_d_sub,
    pullbackSection_d_appLE f (pullback.snd f f) (pullback.diagonal_snd f) U
      (Stacks.Diagonal.prodOpen_le_snd f U) b,
    pullbackSection_d_appLE f (pullback.fst f f) (pullback.diagonal_fst f) U
      (Stacks.Diagonal.prodOpen_le_fst f U) b]

/-! ### The canonical split short exact sequence -/

/-- **The splitting identity for `(-1, 1)` and `(1, 1)`.**  The second projection and the first
inclusion of a direct sum `M ⊕ M` satisfy the compatibility `r ≫ f + g ≫ s = 𝟙` for the arrows
`f = (-1, 1)` and `g = (1, 1)`. -/
theorem biprod_snd_lift_add_desc_inl (M : X.Modules) :
    biprod.snd ≫ biprod.lift (-𝟙 M) (𝟙 M) + biprod.desc (𝟙 M) (𝟙 M) ≫ biprod.inl =
      𝟙 (M ⊞ M) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- **[Stacks, Tag 060N]: the canonical short exact sequence**
`0 → Ω_{X/S} → Ω_{X/S} ⊕ Ω_{X/S} → Ω_{X/S} → 0`, with left arrow `(-1, 1)` and right arrow
`(1, 1)`.  The left-hand term is the conormal sheaf `𝒞_{X/X ×_S X}` of the diagonal through the
identification of [Stacks, Tag 08S2]
(`Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal`); the middle term is
`Δ^* Ω_{X ×_S X/S}` through `Stacks.DiagonalSplitSequence.diagonalBiprodIso`, under which the
right arrow is the canonical map of `Δ`. -/
noncomputable def shortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (biprod.lift (-𝟙 (relativeDifferentials f)) (𝟙 (relativeDifferentials f)))
    (biprod.desc (𝟙 (relativeDifferentials f)) (𝟙 (relativeDifferentials f)))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, Category.id_comp, neg_add_cancel])

/-- **[Stacks, Tag 060N]: the sequence is split.**  The retraction of the left arrow is the
second projection of the direct sum and the section of the right arrow is the first
inclusion. -/
noncomputable def splitting : (shortComplex f).Splitting where
  r := biprod.snd
  s := biprod.inl
  f_r := by simp [shortComplex]
  s_g := by simp [shortComplex]
  id := biprod_snd_lift_add_desc_inl (relativeDifferentials f)

/-- **[Stacks, Tag 060N]: the canonical short exact sequence.** -/
@[stacks 060N "the canonical short exact sequence"]
theorem shortComplex_shortExact : (shortComplex f).ShortExact := (splitting f).shortExact


end Diagonal

end Stacks.DiagonalSplitSequence

end
