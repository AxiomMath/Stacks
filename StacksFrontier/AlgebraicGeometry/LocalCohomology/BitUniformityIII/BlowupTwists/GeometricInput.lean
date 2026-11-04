module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwists.AmbientComposite

/-!
# Tag 0GA7 for the blowup: the ambient sequence, `GeometricInput` and the four clauses

This part builds the twisted ideal sequence `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`, the canonical
maps `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))`, the structure `GeometricInput`, and proves the four clauses of
[Stacks, Tag 0GA7] from it.

## Where the Tag 0GA7 attributes are, and why they are not here

**Nothing in this file carries an attribute for Tag 0GA7.** The four registrations sit on
`Stacks.LocalCohomology.UniformityIII.Situation.subsingleton_Hdiv`, `.bijective_cdiv`,
`.subsingleton_Hamb` and `.bijective_camb` of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/BoundQAndD.lean`, which prove the
same four clauses about a different carrier: `Situation` there is an abstract structure whose
*cohomology groups themselves* are data (`Hdiv`, `Hamb` are bare `ModuleCat A`-valued families),
whose long exact sequences are fields (`div_exact_mid`, `div_exact_right`, `amb_exact_mid`,
`amb_exact_right`), and which assumes both of Serre's theorems. `GeometricInput` is the stronger
input in every one of those respects — the groups are the derived functors of `Γ(X, -)` on the
actual sheaves, the exactness is derived from the δ-functor and from left exactness of
`Γ(X, -)`, and neither of Serre's theorems is assumed — so moving the four registrations here
would strengthen all four, and that is what inhabiting `GeometricInput` is for. Until it is
inhabited, neither carrier is unconditional and neither deserves an unscoped attribute;
`Situation` is also the base of the tower `ModuleSituation`, `TwistedModuleSituation`,
`DualSituation` of `PullbackCohomology.lean` and `DivisibleMaps.lean`, so it is not going away.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.thickeningSheaf`: `𝒪_{Yₙ}`.
* `Stacks.LocalCohomology.UniformityIII.thickeningTwist`: `𝒪_{Yₙ}(q)`.
* `Stacks.LocalCohomology.UniformityIII.thickeningRestrict`,
  `Stacks.LocalCohomology.UniformityIII.thickeningTwistRestrict`: the canonical
  `𝒪_{Yₘ} ⟶ 𝒪_{Yₙ}` and `𝒪_{Yₘ}(q) ⟶ 𝒪_{Yₙ}(q)` for `n ≤ m`.
* `Stacks.LocalCohomology.UniformityIII.blowupH`: `Hⁱ(X, ℱ)`.
* `Stacks.LocalCohomology.UniformityIII.thickeningSections`: the canonical comparison map
  `Iᑫ ⟶ H⁰(X, 𝒪_{Yₙ}(q))`. Its ambient counterpart
  `Stacks.LocalCohomology.UniformityIII.ambientSections`, and with it `𝒪_X(q)` and `Γ(X, -)`, are
  one file upstream in
  `StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/AmbientSections.lean`, where
  the two files proving [Stacks, Tag 0AG6] part (3) on the blowup can reach them.
* `Stacks.LocalCohomology.UniformityIII.GeometricInput`: the Situation of Tag 0GA6 on `X`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.exact_blowupHMap`: the long exact cohomology sequence
  of a short exact sequence of sheaves, in every positive degree.
* `Stacks.LocalCohomology.UniformityIII.injective_blowupΓMap`,
  `Stacks.LocalCohomology.UniformityIII.exact_blowupΓMap`: the same in degree `0`, from left
  exactness of global sections.
* `Stacks.LocalCohomology.UniformityIII.blowupΓMap_ambientTwistMap_ambientSections`: the
  left-hand square of the diagram for the ambient sequence, which was the field `amb_sq_left`.
* `Stacks.LocalCohomology.UniformityIII.app_top_thickeningProj_one_eq_zero`: **`I` kills
  `𝒪_{Y₁}`** — the global section of `𝒪_X` pulled back from an element of `I` is zero on the
  exceptional divisor. This is the ideal-sheaf half of the comparison the complex condition
  needs; `app_thickeningProj_one_restrict_eq_zero` and
  `app_thickeningProj_one_map_restrict_eq_zero` are the same on an arbitrary open.
* `Stacks.LocalCohomology.UniformityIII.ambientTwistMap_comp_thickeningTwistProj`: the
  interchange identity of the second sequence, which reduces the complex condition to the single
  vanishing `thickeningSheaf I 1 ◁ ambientTwistMap I q = 0`. That reduction is *not* how the
  complex condition is proved; see the obstruction register above.
* `Stacks.LocalCohomology.UniformityIII.val_appTop_toSpec`: the global function on `X` that an
  element of `A` pulls back to has the constant fraction `b/1` as its value at every point.
* `Stacks.LocalCohomology.UniformityIII.map_app_thickeningProj_one`: the section of `1` under
  `𝒪_X ⟶ 𝒪_{Yₙ}` restricts to the section of `1`, which is the left factor of the pure tensor
  the complex condition reduces to.
* `Stacks.LocalCohomology.UniformityIII.app_thickeningTwistProj`: the canonical
  `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)` on a local section is that pure tensor.
* `Stacks.LocalCohomology.UniformityIII.exists_tensorObjTmul_app_one_eq_zero`: the pure tensor
  vanishes near every point of its open, from the local factorisation
  `Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`.
* `Stacks.LocalCohomology.UniformityIII.ambientTwistMap_comp_thickeningTwistProj_eq_zero`:
  **the second sequence is a complex**, which was the field `amb_comp`.
* `Stacks.LocalCohomology.UniformityIII.thickeningSections_one_eq_zero_of_mem`: the canonical
  map `Iᑫ → H⁰(X, 𝒪_Y(q))` kills `I^{q+1}`, which is therefore not assumed.
* `Stacks.LocalCohomology.UniformityIII.subsingleton_baseH`: `Hⁱ(X, 𝒪_Y(q)) = 0` for every
  `i ≥ 1` and `q ≥ q₀`, from the two `n = 1` vanishing fields.
* `Stacks.LocalCohomology.UniformityIII.amb_serre`: Serre vanishing on `X`, which is therefore
  not assumed.
* `Stacks.LocalCohomology.UniformityIII.subsingleton_thickeningH`: clause (1).
* `Stacks.LocalCohomology.UniformityIII.thickeningSections_surjective_and_ker`: clause (2).
* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupH`: clause (3).
* `Stacks.LocalCohomology.UniformityIII.bijective_ambientSections`: clause (4).

## Implementation notes

Clause (2) says `H⁰(X, 𝒪_{Yₙ}(q)) = Iᑫ/I^{q+n}`. It is stated here as: the canonical map
`Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))` is surjective and its kernel is exactly `I^{q+n}`. That is equivalent to
bijectivity of the induced map out of the subquotient, and it has the advantage that *both*
halves are conclusions: a formulation through the subquotient would have to assume, in order to
build the map at all, that the canonical map kills `I^{q+n}` — which is the easy half of the
clause.

Accordingly `Stacks.LocalCohomology.UniformityIII.surjective_and_ker_of_step` is used here in
place of `Stacks.LocalCohomology.UniformityIII.bijective_of_exact_rows`, the short five lemma of
`BoundQAndD.lean`: it is the same argument, run on maps out of `Iᑫ` and `I^{q+1}` rather than out
of their subquotients, and it serves both the induction on `n` of clause (2) and the descending
induction on `q` of clause (4).

Twists are indexed by `ℕ`. All four clauses concern `q ≥ q₀ ≥ 0` only, and the inductions move
`q` by one in either direction inside that range, so nothing is lost.

Degree `0` is `Γ(X, -)` and positive degrees are the right derived functors, so the proof never
has to compare the two. Carrying the clauses with degree `0` read as `H⁰ = Γ` through
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` was tried and abandoned: the unifier exhausts
its heartbeats on the resulting derived-functor types in all four clauses. It is not needed.
What the degree-`0` statements actually require is only that `Γ(X, -)` be left exact, and that
is elementary: `secF R ⊤` is `SheafOfModules.toSheaf` followed by evaluation at `⊤`, both of
which preserve finite limits, so it carries a short exact sequence of sheaves to a left exact
sequence of abelian groups. Nothing about derived functors enters.

That left exactness is stated abstractly in `exact_map_of_shortExact` and
`mono_map_f_of_shortExact`: a functor preserving finite limits carries the kernel presentation
of a short exact sequence to a kernel.

Two further obstacles of the same kind were met and are worked around rather than suppressed —
raising the heartbeat limit is not available here.

* `X.Modules` and `SheafOfModules X.ringCatSheaf` are two spellings of one category, and a goal
  mentioning both is not type-correct at `implicit` transparency, so no `rw` fires inside it.
  The associativity step of the whiskering argument is therefore
  `Stacks.LocalCohomology.UniformityIII.comp_whiskerRight_comp`, proved in an abstract monoidal
  category where there is nothing to unfold, and the rest is `congrArg` in term mode.
* `sheafSectionsPreservesFiniteLimits` must be polymorphic in the universe of `AddCommGrpCat`
  as well as in the space: fixed at the ambient `u` it is not found inside `secF`.
* the same two spellings are why the complex condition is proved by evaluating the composite on
  a section rather than through the interchange identity;
  `Stacks.SheafOfModules.OnSpace.tensor_hom_ext` applies to
  `thickeningSheaf I 1 ◁ ambientTwistMap I q = 0`, but the goal it leaves mentions both
  spellings, is reported as not type-correct at `implicit` transparency, and writes the two
  tensor factors as `(ULift.equivalence.symm.inverse.obj _).down` — the `ULift` copy on which
  `Stacks.SheafOfModules.OnSpace.monoidal` is transported — so `whiskerLeft_tmul` does not
  rewrite. See the obstruction register above.
* every statement proved about the local factorisation is placed in its own declaration, because
  **the 200 000-heartbeat budget is per declaration.** Four distinct ways of exceeding it are
  recorded in
  `StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/TwistShiftLocal.lean`: forcing the inverse of the `asIso` comparison isomorphism into `whnf`; making
  an equation that names `associatedModuleSheafMap` the body of an `∃`, whose anonymous
  constructor then has to compare that map's implicit `Decomposition` and `SetLike.GradedSMul`
  instances for the truncation; leaving the two sections of an `Eq` to be recovered from a
  pointwise hypothesis, which is a higher-order unification problem; and — the one that cost the
  factorisation itself — **destructuring anything by `rcases` while the goal is the
  factorisation**, which abstracts that goal into a `casesOn` motive. Term-mode `Exists.elim`
  costs nothing in its place. The statement is *not* what spends the budget; an earlier note
  there said it was, and that is corrected.
* the scalar of the local factorisation is handed to
  `tensorObjTmul_app_one_eq_zero_of_restrict_eq_smul` as a variable rather than written out as
  `(…).obj.map i r`, because written out it has to be elaborated against the module structure of
  the tensor factor and the `HSMul` instance is then not found: the target of
  `PresheafOfModules.map` is wrapped in `ModuleCat.restrictScalars`, and the carrier underneath
  is reached only through the `def` `AlgebraicGeometry.Scheme.Modules`, which instance search
  does not unfold. The same equation over `Proj` directly, where no such `def` intervenes, needs
  no such care — `Stacks.Blowup.map_eq_smul_of_pointwise` states it and proves it by
  `Subtype.ext`.

The ring `A` is assumed Noetherian in the four clauses, both for faithfulness to the Situation
of Tag 0GA6 and because the two theorems standing in for Serre's need it: a Noetherian ring is
what supplies the finite generating family of `I` presenting `X` inside projective space, and
Noetherianity of the Rees algebra is what makes the torsion elements of the kernel finitely
generated. `GeometricInput` itself does not require it, and clauses (1) and (2) — the two that
call neither `Stacks.LocalCohomology.UniformityIII.amb_serre` nor
`Stacks.Blowup.exists_forall_bijective_ambientSections` — do not use it.

## References

* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 07ZE](https://stacks.math.columbia.edu/tag/07ZE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGlobalSections degreeSection)

universe u
universe v w

namespace Stacks.LocalCohomology.UniformityIII

section Objects

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
  sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

section AmbShortExact

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-! ### The twisted ideal sequence, and what is left of the exactness of the second sequence

The second sequence of Tag 0GA7 is the ideal sequence of the exceptional divisor
(`Stacks.IdealSheafSequence.divisorIdeal_shortExact` at `thickeningIdeal I 1`, [Stacks,
Tag 0C6K]) tensored by `𝒪_X(q)`. This section builds the twisted sequence and reduces the field
`amb_shortExact` to a single isomorphism. -/

/-- **Right whiskering is the canonical induced map on sheafified tensor products.** This is
`Stacks.SheafOfModules.OnSpace.tensorHom_eq` at a second factor which is an identity; it is the
bridge between the monoidal spelling `f ▷ ℱ` the sequences of Tag 0GA7 are written in and the
spelling `tensorSheafMap` in which Tag 01CC's exactness statements are proved. -/
theorem whiskerRight_eq_tensorSheafMap {F G : (blowupScheme I).Modules} (f : F ⟶ G)
    (H : (blowupScheme I).Modules) :
    (f ▷ H) = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((blowupScheme I).toRingedSpace)).presheaf,
        (((blowupScheme I).toRingedSpace)).IsSheaf⟩)).map
      ((f, (𝟙 H)) : (_, _) ⟶ (_, _))) :=
  (MonoidalCategory.tensorHom_id f H).symm.trans
    (Stacks.SheafOfModules.OnSpace.tensorHom_eq _ f (𝟙 H))

/-- Whiskering the zero morphism gives the zero morphism. -/
theorem zero_whiskerRight_eq_zero {F G : (blowupScheme I).Modules}
    (H : (blowupScheme I).Modules) : ((0 : F ⟶ G) ▷ H) = 0 :=
  (whiskerRight_eq_tensorSheafMap I 0 H).trans
    (AlgebraicGeometry.SheafOfModules.tensorSheafMap_zero_left _ (𝟙 H))

/-- **Whiskering an epimorphism on the right is an epimorphism.** The obstruction register above
recorded that instance search does not find this; it is [Stacks, Tag 01CC], exactness at the
right term, read through `whiskerRight_eq_tensorSheafMap`. The hypothesis is an explicit
argument rather than an instance because the class `Epi` has two spellings here, one for each
spelling of the category. -/
theorem epi_whiskerRight_of_epi {F G : (blowupScheme I).Modules} (f : F ⟶ G) (hf : Epi f)
    (H : (blowupScheme I).Modules) : Epi (f ▷ H) := by
  rw [whiskerRight_eq_tensorSheafMap]
  exact @AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi _ F G H f hf

/-- **`𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)` is an epimorphism**, so the second map of the second sequence of
Tag 0GA7 is surjective for every `n` and `q`: the untwisted `𝒪_X ⟶ 𝒪_{Yₙ}` is an epimorphism
by `epi_thickeningProj`, and tensoring preserves that. -/
instance epi_thickeningTwistProj (n q : ℕ) : Epi (thickeningTwistProj I n q) :=
  epi_leftUnitor_inv_comp_whiskerRight (thickeningProj I n)
    (epi_whiskerRight_of_epi I (thickeningProj I n) (epi_thickeningProj I n) (blowupTwist I q))

/-- **Every twist on the blowup is finite locally free**, at the spelling of [Stacks, Tag 01C6]
part (2) that the flatness criterion of [Stacks, Tag 05P2] is stated over. It is
`Stacks.Blowup.isInvertible_blowUpTwist` ([Stacks, Tag 02NS] part (2)) carried to that rank
predicate by `Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`. -/
theorem isFiniteLocallyFree_blowupTwist (q : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (blowupScheme I).ringCatSheaf) (blowupTwist I q) :=
  have : Stacks.SheafOfModules.IsInvertible (blowupScheme I).toRingedSpace.presheaf
      (structureSheafRing (blowupScheme I).toRingedSpace).property (blowupTwist I q) :=
    Stacks.Blowup.isInvertible_blowUpTwist I (q : ℤ)
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} _ 1
    (hM := Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
      (X := (blowupScheme I).toRingedSpace) (blowupTwist I q))

/-- **Every twist on the blowup is flat**, by [Stacks, Tag 05P2] from finite local freeness.
This is what makes `- ⊗ 𝒪_X(q)` left exact as well as right exact, so that the twisted ideal
sequence is short exact and not merely exact at its last two terms. -/
theorem isFlat_blowupTwist (q : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (blowupScheme I).sheaf) (blowupTwist I q) :=
  AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
    (isFiniteLocallyFree_blowupTwist I q)

/-- **Whiskering a monomorphism by a twist is a monomorphism**: the twist is flat, so tensoring
by it preserves finite limits, hence monomorphisms. -/
theorem mono_whiskerRight_blowupTwist {F G : (blowupScheme I).Modules} (f : F ⟶ G) (hf : Mono f)
    (q : ℕ) : Mono (f ▷ blowupTwist I q) := by
  rw [whiskerRight_eq_tensorSheafMap]
  have hm : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (blowupScheme I).sheaf).flip.obj (blowupTwist I q))).PreservesMonomorphisms :=
    have : PreservesFiniteLimits (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (blowupScheme I).sheaf).flip.obj (blowupTwist I q))) := (isFlat_blowupTwist I q).1
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  let tensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (blowupScheme I).sheaf
  have equation := (congrArg (((tensor.map f).app (blowupTwist I q)) ≫ ·)
    ((tensor.obj G).map_id (blowupTwist I q))).trans (Category.comp_id _)
  exact (congrArg Mono equation).mpr (@Functor.map_mono _ _ _ _ _ hm _ _ f hf)

/-- **The ideal sheaf `ℐ_{Yₙ}` of the thickening**, as the kernel of `𝒪_X ⟶ 𝒪_{Yₙ}`. This is
`Stacks.ClosedImmersion.idealSheaf` of the closed immersion `Yₙ ↪ X` on the nose: the ideal
sheaf is *defined* as that kernel, and `Stacks.IdealSheafSequence.divisorIdealMap` is its
inclusion. -/
abbrev thickeningIdealSheaf (n : ℕ) : (blowupScheme I).Modules := kernel (thickeningProj I n)

/-- The inclusion `ℐ_{Yₙ} ⟶ 𝒪_X`, i.e. `Stacks.IdealSheafSequence.divisorIdealMap` at
`thickeningIdeal I n`. -/
abbrev thickeningIdealι (n : ℕ) :
    thickeningIdealSheaf I n ⟶ SheafOfModules.unit (blowupScheme I).ringCatSheaf :=
  kernel.ι (thickeningProj I n)

/-- **The first map of the twisted ideal sequence**, `ℐ_{Yₙ} ⊗ 𝒪_X(q) ⟶ 𝒪_X(q)`: the inclusion
of the ideal sheaf whiskered by the twist and read through the left unitor. For `n = 1` this is
the map the first map `ambientTwistMap` of the second sequence of Tag 0GA7 has to be identified
with; see `shortExact_ambientTwistMap_of_isIso_kernelLift`. -/
abbrev twistedThickeningIdealMap (n q : ℕ) :
    (thickeningIdealSheaf I n ⊗ blowupTwist I q : (blowupScheme I).Modules) ⟶ blowupTwist I q :=
  (thickeningIdealι I n ▷ blowupTwist I q) ≫ (λ_ (blowupTwist I q)).hom

/-- **The twisted ideal sequence is a complex**: the whiskering of
`ℐ_{Yₙ} ⟶ 𝒪_X ⟶ 𝒪_{Yₙ}`, which is zero because the first map is the kernel inclusion of the
second. -/
theorem twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero (n q : ℕ) :
    twistedThickeningIdealMap I n q ≫ thickeningTwistProj I n q = 0 :=
  (whiskerRight_comp_leftUnitor_comp (thickeningIdealι I n) (thickeningProj I n)).trans
    ((congrArg (fun φ : thickeningIdealSheaf I n ⟶ thickeningSheaf I n =>
          φ ▷ blowupTwist I q)
        (kernel.condition (thickeningProj I n))).trans
      (zero_whiskerRight_eq_zero I (blowupTwist I q)))

/-- **The first map of the twisted ideal sequence is a monomorphism**: the kernel inclusion is
one and the twist is flat. -/
theorem mono_twistedThickeningIdealMap (n q : ℕ) :
    Mono (twistedThickeningIdealMap I n q) :=
  mono_whiskerRight_comp_leftUnitor (thickeningIdealι I n)
    (mono_whiskerRight_blowupTwist I (thickeningIdealι I n)
      (ShortComplex.shortExact_mk_kernel_ι (thickeningProj I n)).mono_f q)

/-- **What is left of the exactness field `amb_shortExact` of `GeometricInput`**: the second
sequence `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0` of the proof of [Stacks, Tag 0GA7] is short exact
as soon as the canonical lift of `ambientTwistMap I q` to the kernel of the restriction to the
exceptional divisor is an **isomorphism**.

The lift exists for free, from the complex condition
`ambientTwistMap_comp_thickeningTwistProj_eq_zero`; the surjectivity of the second map is
`epi_thickeningTwistProj`; and exactness at the middle is then automatic. So the field is one
`IsIso` for each `q`, and nothing else.

That `IsIso` is [Stacks, Tag 02OS] part (3), `𝒪_X(1) = 𝒪_X(-Y)`, in the form the twisted
sequence needs it: the kernel in question receives the monomorphism
`twistedThickeningIdealMap I 1 q` from `ℐ_Y ⊗ 𝒪_X(q)`, so the `IsIso` says that
`𝒪_X(q+1) ⟶ 𝒪_X(q)` and `ℐ_Y ⊗ 𝒪_X(q) ⟶ 𝒪_X(q)` are the same subsheaf of `𝒪_X(q)`. -/
theorem shortExact_ambientTwistMap_of_isIso_kernelLift (q : ℕ)
    (hl : IsIso (kernel.lift (thickeningTwistProj I 1 q) (ambientTwistMap I q)
      (ambientTwistMap_comp_thickeningTwistProj_eq_zero I q))) :
    (ShortComplex.mk (ambientTwistMap I q) (thickeningTwistProj I 1 q)
      (ambientTwistMap_comp_thickeningTwistProj_eq_zero I q)).ShortExact :=
  shortExact_of_isIso_kernelLift (ambientTwistMap I q) (thickeningTwistProj I 1 q)
    (ambientTwistMap_comp_thickeningTwistProj_eq_zero I q) hl

end AmbShortExact

/-- **The canonical map `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))`**: the map `Iᑫ → H⁰(X, 𝒪_X(q))` followed by the
global sections of the canonical `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)`. -/
def thickeningSections (n q : ℕ) : (I ^ q : Ideal A) →+ blowupΓ I (thickeningTwist I n q) :=
  (blowupΓMap I (thickeningTwistProj I n q)).comp (ambientSections I q)

/-- **The right-hand square of the diagram in the proof of Tag 0GA7, clause (4).** The composite
`Iᑫ → H⁰(X, 𝒪_X(q)) → H⁰(X, 𝒪_Y(q))` is the canonical map `Iᑫ → H⁰(X, 𝒪_Y(q))`.

This is a triviality rather than an input, because the second map of the sequence
`0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0` is the canonical restriction `thickeningTwistProj I 1 q`
to the exceptional divisor, and `thickeningSections` is defined by composing with it. -/
theorem blowupΓMap_thickeningTwistProj_ambientSections (q : ℕ) (x : (I ^ q : Ideal A)) :
    blowupΓMap I (thickeningTwistProj I 1 q) (ambientSections I q x) =
      thickeningSections I 1 q x :=
  rfl

/-- **The right-hand square of the diagram in the proof of Tag 0GA7, clause (2).** The composite
`Iᑫ → H⁰(X, 𝒪_{Yₘ}(q)) → H⁰(X, 𝒪_{Yₙ}(q))` is the canonical map `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))`.

Like its counterpart for clause (4) this is a consequence of the second map of the sequence
being canonical, not an input: it is the compatibility
`thickeningTwistProj_comp_thickeningTwistRestrict` read on global sections. -/
theorem blowupΓMap_thickeningTwistRestrict_thickeningSections {n m : ℕ} (h : n ≤ m) (q : ℕ)
    (x : (I ^ q : Ideal A)) :
    blowupΓMap I (thickeningTwistRestrict I h q) (thickeningSections I m q x) =
      thickeningSections I n q x := by
  show blowupΓMap I (thickeningTwistRestrict I h q)
    (blowupΓMap I (thickeningTwistProj I m q) (ambientSections I q x)) = _
  rw [← blowupΓMap_comp, thickeningTwistProj_comp_thickeningTwistRestrict]
  rfl

/-- **The Situation of [Stacks, Tag 0GA6], read on the blowup `X` itself.**

The fields are the two short exact sequences of sheaves on `X` which the proof of Tag 0GA7 uses;
the two integers `d = d(S)` and `q₀ = q(S)`, pinned by the properties that define them; and the
vanishing of `Hⁱ` above `d`. Everything there except the last is what the section of Tag 0GA6
establishes before Tag 0GA7 is stated. **Neither of Serre's theorems on `X` is among the
fields**: the vanishing is `Stacks.LocalCohomology.UniformityIII.amb_serre`, and the computation
of the sections of `𝒪_X(q)` for large `q` — [Stacks, Tag 0AG6] part (3), which was the field
`amb_serre_sections` — is `Stacks.Blowup.exists_forall_bijective_ambientSections`.

The sequences are carried as *short exact sequences of sheaves* only. Everything they induce on
cohomology is proved: in positive degrees by `exact_blowupHMap`, in degree `0` by
`injective_blowupΓMap` and `exact_blowupΓMap`. And only the *first* map of each is data — the
second is in both cases the canonical restriction to the exceptional divisor, so the two
right-hand squares of the diagrams in the Stacks proof are theorems here rather than fields,
`blowupΓMap_thickeningTwistRestrict_thickeningSections` and
`blowupΓMap_thickeningTwistProj_ambientSections`.

No field is a clause of Tag 0GA7, for any `n` and any `q`: the `n = 1` fields `base_vanishing`,
`base_surjective` and `base_ker_le` *are* the definition of `q(S)` — Tag 0GA7 opens its
induction with "the base case `n = 1` is our definition of `q₀`, as `Y₁ = Y`". Indeed no field
mentions a thickening `Yₙ` with `n ≥ 2` except through the sequences themselves:
`base_vanishing_gt`, the vanishing above `d`, is also asked for on `Y` alone.

**This structure has no witness in the repository.** Everything proved from it is therefore
conditional; see the module docstring for what inhabiting it would take. -/
structure GeometricInput where
  /-- `d = d(S)`, the maximum of the dimensions of the fibres of `p : X → Spec(A)`. -/
  d : ℕ
  /-- `q₀ = q(S)`. -/
  q₀ : ℕ
  /-- The first map of `0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0`. It comes from the
  identification `𝒪_X(1) = 𝒪_X(-Y)` of [Stacks, Tag 02OS] part (3), so it is not canonical in
  the twists and is carried as data. -/
  divα : ∀ n q : ℕ, thickeningTwist I n (q + 1) ⟶ thickeningTwist I (n + 1) q
  /-- The first sequence is a complex. Its second map, `𝒪_{Y_{n+1}}(q) → 𝒪_Y(q)`, is not data:
  it is the canonical restriction `thickeningTwistRestrict` to the exceptional divisor. -/
  div_comp : ∀ n q : ℕ,
    divα n q ≫ thickeningTwistRestrict I (Nat.le_add_left 1 n) q = 0
  /-- **The first sequence is short exact.** Its long exact cohomology sequence is not assumed:
  it is derived from this by `Stacks.LocalCohomology.UniformityIII.exact_blowupHMap`. -/
  div_shortExact : ∀ n q : ℕ, 1 ≤ n →
    (ShortComplex.mk (divα n q) (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)
      (div_comp n q)).ShortExact
  /-- **The second sequence is short exact.** Again its long exact cohomology sequence is
  derived, not assumed. That it is a *complex* is not assumed either — that was the field
  `amb_comp`, and it is now the theorem
  `Stacks.LocalCohomology.UniformityIII.ambientTwistMap_comp_thickeningTwistProj_eq_zero`.

  Only one of the three assertions of short exactness is open. The surjectivity of the second
  map is `Stacks.LocalCohomology.UniformityIII.epi_thickeningTwistProj`, and by
  `Stacks.LocalCohomology.UniformityIII.shortExact_ambientTwistMap_of_isIso_kernelLift` the whole
  field follows from `IsIso (kernel.lift (thickeningTwistProj I 1 q) (ambientTwistMap I q) _)`,
  for each `q`: that the canonical lift of the first map to the kernel of the second is an
  isomorphism. That is [Stacks, Tag 02OS] part (3), the identification `𝒪_X(1) = 𝒪_X(-Y)`; see
  entries (2c) and (2d) of the obstruction register in the module docstring. -/
  amb_shortExact : ∀ q : ℕ,
    (ShortComplex.mk (ambientTwistMap I q) (thickeningTwistProj I 1 q)
      (ambientTwistMap_comp_thickeningTwistProj_eq_zero I q)).ShortExact
  /-- The left-hand square of the diagram in the proof of Tag 0GA7(2): the canonical maps out of
  the powers of `I` are compatible with `𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q)` and the inclusion
  `I^{q+1} ⊆ Iᑫ`. -/
  div_sq_left : ∀ (n q : ℕ) (x : (I ^ (q + 1) : Ideal A)),
    blowupΓMap I (divα n q) (thickeningSections I n (q + 1) x) =
      thickeningSections I (n + 1) q ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩
  /-- Half of the definition of `q(S)`: `Hⁱ(X, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ d` and `q ≥ q(S)`. -/
  base_vanishing : ∀ i q : ℕ, 1 ≤ i → i ≤ d → q₀ ≤ q →
    Subsingleton (blowupH I i (thickeningTwist I 1 q))
  /-- The other half of the definition of `q(S)`, surjectivity: `H⁰(X, 𝒪_Y(q)) = Iᑫ/I^{q+1}` for
  `q ≥ q(S)`. -/
  base_surjective : ∀ q : ℕ, q₀ ≤ q → Function.Surjective (thickeningSections I 1 q)
  /-- The other half of the definition of `q(S)`, the kernel — and only the half of *that* which
  does not follow from the rest: a class in `Iᑫ` killed by the canonical map lies in `I^{q+1}`.
  The reverse inclusion is **not** assumed, it is
  `Stacks.LocalCohomology.UniformityIII.thickeningSections_one_eq_zero_of_mem`, read off
  `ambientTwistMap_comp_thickeningTwistProj_eq_zero` and
  `blowupΓMap_ambientTwistMap_ambientSections`; the two together are
  `Stacks.LocalCohomology.UniformityIII.thickeningSections_one_eq_zero_iff`. -/
  base_ker_le : ∀ q : ℕ, q₀ ≤ q → ∀ x : (I ^ q : Ideal A),
    thickeningSections I 1 q x = 0 → (x : A) ∈ I ^ (q + 1)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`, since `d` bounds the fibre dimensions of
  `p`; here for `ℱ = 𝒪_Y(q)` only. The same vanishing for the higher thickenings `𝒪_{Yₙ}(q)`,
  `n ≥ 2`, is **not** assumed: it is the induction of the Stacks proof on the first short exact
  sequence, which carries vanishing above `d` up the thickenings exactly as it carries the
  vanishing in the range `1 ≤ i ≤ d`; see
  `Stacks.LocalCohomology.UniformityIII.subsingleton_thickeningH`. -/
  base_vanishing_gt : ∀ i q : ℕ, d < i → Subsingleton (blowupH I i (thickeningTwist I 1 q))

/-- The middle cohomology group of a short exact sequence vanishes if the outer ones do. -/
private theorem subsingleton_blowupH_of_shortExact
    {S : ShortComplex (SheafOfModules.{u} (blowupScheme I).ringCatSheaf)} (hS : S.ShortExact)
    (i : ℕ) (h₁ : Subsingleton (blowupH I i S.X₁)) (h₃ : Subsingleton (blowupH I i S.X₃)) :
    Subsingleton (blowupH I i S.X₂) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, rfl⟩ := (exact_blowupHMap I hS i y).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim x 0, map_zero]

/-- A property of `q + N` that passes from `r + 1` to `r` for all `r ≥ q` holds at `q`. -/
private theorem of_add_of_forall_succ_imp {P : ℕ → Prop} {q : ℕ}
    (step : ∀ r, q ≤ r → P (r + 1) → P r) (N : ℕ) : P (q + N) → P q := by
  induction N with
  | zero => exact id
  | succ N ih => exact fun h => ih (step (q + N) (Nat.le_add_right q N) h)

section Consequences

variable (G : GeometricInput I)

/-- **The easy half of the kernel computation at `n = 1`**, which is therefore not assumed: an
element of `I^{q+1}`, read as an element of `Iᑫ`, is killed by the canonical map
`Iᑫ → H⁰(X, 𝒪_Y(q))`.

The reason is that the section it produces already comes from `𝒪_X(q+1)`, the subsheaf of
`𝒪_X(q)` the second sequence of the Situation exhibits as the kernel of the restriction to the
exceptional divisor: the left-hand square `blowupΓMap_ambientTwistMap_ambientSections` factors
the section through `H⁰(X, 𝒪_X(q+1))`, and
`ambientTwistMap_comp_thickeningTwistProj_eq_zero` kills it there. No exactness is used, only
that the composite of the two maps of the sequence is zero — and that is now a theorem, so this
one uses no field of `GeometricInput` at all. -/
theorem thickeningSections_one_eq_zero_of_mem (q : ℕ) (x : (I ^ q : Ideal A))
    (hx : (x : A) ∈ I ^ (q + 1)) : thickeningSections I 1 q x = 0 := by
  have h : ambientSections I q x
      = blowupΓMap I (ambientTwistMap I q) (ambientSections I (q + 1) ⟨(x : A), hx⟩) :=
    (blowupΓMap_ambientTwistMap_ambientSections I q ⟨(x : A), hx⟩).symm
  show blowupΓMap I (thickeningTwistProj I 1 q) (ambientSections I q x) = 0
  rw [h, ← blowupΓMap_comp, ambientTwistMap_comp_thickeningTwistProj_eq_zero I q,
    blowupΓMap_zero]

/-- **The definition of `q(S)` at `n = 1`, kernel half**: for `q ≥ q(S)` the canonical map
`Iᑫ → H⁰(X, 𝒪_Y(q))` kills exactly `I^{q+1}`. Only the forward implication is a field of
`GeometricInput`; the other is `thickeningSections_one_eq_zero_of_mem`. -/
theorem thickeningSections_one_eq_zero_iff {q : ℕ} (hq : G.q₀ ≤ q) (x : (I ^ q : Ideal A)) :
    thickeningSections I 1 q x = 0 ↔ (x : A) ∈ I ^ (q + 1) :=
  ⟨G.base_ker_le q hq x, thickeningSections_one_eq_zero_of_mem I q x⟩

/-- **The vanishing of `Hⁱ(X, 𝒪_Y(q))` in every positive degree**, for `q ≥ q(S)`: in the range
`1 ≤ i ≤ d` it is the defining property of `q(S)`, and above `d` it is the vanishing the fibre
dimension `d` forces. This is the base case of the induction proving clause (1). -/
theorem subsingleton_baseH {i q : ℕ} (hi : 1 ≤ i) (hq : G.q₀ ≤ q) :
    Subsingleton (blowupH I i (thickeningTwist I 1 q)) := by
  by_cases hd : G.d < i
  · exact G.base_vanishing_gt i q hd
  · exact G.base_vanishing i q hi (by omega) hq

end Consequences

variable [IsNoetherianRing A] (G : GeometricInput I)

/-- **Stacks Project, Tag 0GA7, clause (1).** In the Situation of Tag 0GA6, for `n ≥ 1`,
`q ≥ q₀ = q(S)` and `i > 0` the cohomology `Hⁱ(X, 𝒪_{Yₙ}(q))` of the `q`-th twist of the
structure sheaf of the `n`-th thickening of the exceptional divisor of the blowup vanishes.

The case `n = 1` is the definition of `q(S)`; the general case is the induction of the Stacks
proof, on the long exact sequence of `0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0`. -/
theorem subsingleton_thickeningH {n i q : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hq : G.q₀ ≤ q) :
    Subsingleton (blowupH I i (thickeningTwist I n q)) := by
  have key : ∀ m : ℕ, 1 ≤ m → ∀ r : ℕ, G.q₀ ≤ r →
      Subsingleton (blowupH I i (thickeningTwist I m r)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun r hr => subsingleton_baseH I G hi hr
    | succ m hm ih =>
      intro r hr
      exact subsingleton_blowupH_of_shortExact I (G.div_shortExact m r hm) i (ih (r + 1) (by omega))
        (subsingleton_baseH I G hi hr)
  exact key n hn q hq

/-- **Stacks Project, Tag 0GA7, clause (2).** In the Situation of Tag 0GA6, for `n ≥ 1` and
`q ≥ q₀ = q(S)` the canonical map `Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))` is surjective with kernel exactly
`I^{q+n}`; that is, `H⁰(X, 𝒪_{Yₙ}(q)) = Iᑫ/I^{q+n}`.

The case `n = 1` is the definition of `q(S)`; the general case is the induction of the Stacks
proof, whose inductive step is the short five lemma applied to the commutative diagram there,
here `Stacks.LocalCohomology.UniformityIII.surjective_and_ker_of_step`. -/
theorem thickeningSections_surjective_and_ker {n q : ℕ} (hn : 1 ≤ n) (hq : G.q₀ ≤ q) :
    Function.Surjective (thickeningSections I n q) ∧
      ∀ x : (I ^ q : Ideal A), thickeningSections I n q x = 0 ↔ (x : A) ∈ I ^ (q + n) := by
  have key : ∀ m : ℕ, 1 ≤ m → ∀ r : ℕ, G.q₀ ≤ r →
      Function.Surjective (thickeningSections I m r) ∧
        ∀ x : (I ^ r : Ideal A), thickeningSections I m r x = 0 ↔ (x : A) ∈ I ^ (r + m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun r hr =>
        ⟨G.base_surjective r hr, thickeningSections_one_eq_zero_iff I G hr⟩
    | succ m hm ih =>
      intro r hr
      obtain ⟨hs, hk⟩ := ih (r + 1) (by omega)
      have hrw : r + 1 + m = r + (m + 1) := by omega
      rw [hrw] at hk
      obtain ⟨hs₂, hk₂⟩ :=
        surjective_and_ker_of_step (I := I) (q := r) (J := I ^ (r + (m + 1)))
          (Ideal.pow_le_pow_right (by omega))
          (blowupΓMap I (G.divα m r))
          (blowupΓMap I (thickeningTwistRestrict I (Nat.le_add_left 1 m) r))
          (thickeningSections I m (r + 1)) (thickeningSections I (m + 1) r)
          (thickeningSections I 1 r)
          (injective_blowupΓMap I (G.div_shortExact m r hm))
          (exact_blowupΓMap I (G.div_shortExact m r hm))
          (G.div_sq_left m r)
          (blowupΓMap_thickeningTwistRestrict_thickeningSections I (Nat.le_add_left 1 m) r)
          hs (G.base_surjective r hr) hk (thickeningSections_one_eq_zero_iff I G hr)
      exact ⟨hs₂, hk₂⟩
  exact key n hn q hq

/-- The transition map `Hⁱ(X, 𝒪_X(q+1)) → Hⁱ(X, 𝒪_X(q))` is surjective for `i > 0` and
`q ≥ q₀`, because the next term `Hⁱ(X, 𝒪_Y(q))` of the long exact sequence vanishes by
clause (1). -/
theorem surjective_blowupHMap_ambα {i q : ℕ} (hi : 1 ≤ i) (hq : G.q₀ ≤ q) :
    Function.Surjective (blowupHMap I i (ambientTwistMap I q)) := by
  have h : Subsingleton (blowupH I i (thickeningTwist I 1 q)) :=
    subsingleton_thickeningH I G le_rfl hi hq
  exact fun y =>
    (exact_blowupHMap I (G.amb_shortExact q) i y).1 (@Subsingleton.elim _ h _ _)

/-- **Serre vanishing on `X`**, [Stacks, Tag 0AG6] part (2) read on the blowup: for `i > 0` the
cohomology `Hⁱ(X, 𝒪_X(q))` vanishes once `q` is large.

This is a theorem and not a field of `GeometricInput`. It is
`Stacks.Blowup.exists_isZero_Hgroup_twistingSheaf_reesGrading`, which transports Serre vanishing
for coherent sheaves on projective space along the closed immersion of `X` into `𝐏^{m-1}` that a
generating family of `I` presents; Noetherianity of `A`, assumed here for faithfulness to the
Situation of Tag 0GA6 anyway, is what supplies that family. -/
theorem amb_serre (i : ℕ) (hi : 1 ≤ i) : ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
    Subsingleton (blowupH I i (blowupTwist I q)) := by
  obtain ⟨d₀, hd₀⟩ := Stacks.Blowup.exists_isZero_Hgroup_twistingSheaf_reesGrading I i hi
  exact ⟨d₀.toNat, fun q hq =>
    AddCommGrpCat.isZero_iff_subsingleton.1 (hd₀ (q : ℤ) (by omega))⟩

/-- **Stacks Project, Tag 0GA7, clause (3).** In the Situation of Tag 0GA6, for `q ≥ q₀ = q(S)`
and `i > 0` the cohomology `Hⁱ(X, 𝒪_X(q))` of the `q`-th twist of the structure sheaf of the
blowup vanishes.

The transition maps `Hⁱ(X, 𝒪_X(q+1)) → Hⁱ(X, 𝒪_X(q))` are surjective for `q ≥ q₀` by clause (1)
and the long exact sequence of `0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0`, and their source vanishes
once `q` is large by Serre vanishing on `X`. -/
theorem subsingleton_blowupH {i q : ℕ} (hi : 1 ≤ i) (hq : G.q₀ ≤ q) :
    Subsingleton (blowupH I i (blowupTwist I q)) := by
  obtain ⟨N, hN⟩ := amb_serre I i hi
  exact of_add_of_forall_succ_imp (P := fun r => Subsingleton (blowupH I i (blowupTwist I r)))
    (fun r hr h => subsingleton_blowupH_of_shortExact I (G.amb_shortExact r) i h
      (subsingleton_thickeningH I G le_rfl hi (hq.trans hr))) N (hN (q + N) (Nat.le_add_left N q))

/-- **Stacks Project, Tag 0GA7, clause (4).** In the Situation of Tag 0GA6, for `q ≥ q₀ = q(S)`
the canonical map `Iᑫ → H⁰(X, 𝒪_X(q))` is bijective; that is, `H⁰(X, 𝒪_X(q)) = Iᑫ`.

Descending induction from the range where Serre's theorem already identifies the sections: the
short five lemma applied to the map from `I^{q+1} ⊆ Iᑫ` into the long exact sequence of
`0 → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_Y(q) → 0` carries the identification from `q + 1` down to `q`, using
clause (2) for `n = 1` on the right.

The starting range is not assumed. It is [Stacks, Tag 0AG6] part (3) at the Rees grading,
`Stacks.Blowup.exists_forall_bijective_ambientSections`, which was the field
`amb_serre_sections` of `GeometricInput` until its two halves were proved. -/
theorem bijective_ambientSections {q : ℕ} (hq : G.q₀ ≤ q) :
    Function.Bijective (ambientSections I q) := by
  have step : ∀ r : ℕ, G.q₀ ≤ r → Function.Bijective (ambientSections I (r + 1)) →
      Function.Bijective (ambientSections I r) := by
    intro r hr hb
    have hk₁ : ∀ x : (I ^ (r + 1) : Ideal A),
        ambientSections I (r + 1) x = 0 ↔ (x : A) ∈ (⊥ : Ideal A) := by
      intro x
      rw [Submodule.mem_bot]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hb.1 (show ambientSections I (r + 1) x = ambientSections I (r + 1) 0 by
          rw [h, map_zero])
        exact congrArg Subtype.val this
      · rw [show x = 0 from Subtype.ext h, map_zero]
    obtain ⟨hs, hk⟩ :=
      surjective_and_ker_of_step (I := I) (q := r) (J := (⊥ : Ideal A)) bot_le
        (blowupΓMap I (ambientTwistMap I r)) (blowupΓMap I (thickeningTwistProj I 1 r))
        (ambientSections I (r + 1)) (ambientSections I r) (thickeningSections I 1 r)
        (injective_blowupΓMap I (G.amb_shortExact r)) (exact_blowupΓMap I (G.amb_shortExact r))
        (blowupΓMap_ambientTwistMap_ambientSections I r)
        (blowupΓMap_thickeningTwistProj_ambientSections I r)
        hb.2 (G.base_surjective r hr) hk₁
        (thickeningSections_one_eq_zero_iff I G hr)
    refine ⟨?_, hs⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (by simpa using (hk x).1 hx)
  obtain ⟨N, hN⟩ := Stacks.Blowup.exists_forall_bijective_ambientSections I
  exact of_add_of_forall_succ_imp (P := fun r => Function.Bijective (ambientSections I r))
    (fun r hr => step r (hq.trans hr)) N (hN (q + N) (Nat.le_add_left N q))

end Objects

end Stacks.LocalCohomology.UniformityIII

end
