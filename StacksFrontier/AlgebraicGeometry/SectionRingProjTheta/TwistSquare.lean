module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.TwistCompatibility

/-!
# Assertion (ii) of Stacks Tag 01QK: the twist square commutes

In the situation of Stacks Tag 01QH — `X` a scheme, `𝓛` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, 𝓛)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism of Stacks Tag 01PZ —
Stacks Tag 01QJ produces for each `𝓕` a comparison `θ_𝓕 : f^* M̃ ⟶ 𝓕`, where
`M = Γ_*(X, 𝓛, 𝓕)`. Stacks Tag 01QK is a Remark whose second assertion is that the square

```
      f^*M̃ ⊗_{𝒪_X} f^*𝒪_Y(n)  ────▶  f^*(M(n)~)
               │                            │
     θ_𝓕 ⊗ θ_{𝓛^{⊗n}}              θ_{𝓕 ⊗ 𝓛^{⊗n}}
               ▼                            ▼
         𝓕 ⊗ 𝓛^{⊗n}  ──── id ────▶   𝓕 ⊗ 𝓛^{⊗n}
```

commutes, the top arrow being the pullback of the multiplication map `M̃ ⊗ 𝒪_Y(n) → M(n)~` of
Constructions Equation 01MQ. The source says "Proof omitted."

**This file proves that square.** The sibling
`StacksFrontier/AlgebraicGeometry/SectionRingProjQuasicoherent/TwistCompatibility.lean` proves that
it is *not* a consequence of Tag 01QJ as stated: with Tag 0B5I's family `c` unconstrained, the
Remark's equation is quadratic in `θ` on the left and linear on the right, so negating `θ`
forces every instance to be `2`-torsion (`not_forall_twistSquare`). That file's conclusion is
that Tag 01QK needs `c` *characterised*, not merely bound. **The characterisation is supplied
here, and the square is derived from it**: `c` must be compatible with multiplication, i.e. it
must be a *monoidal* natural transformation, and the conversion of that compatibility on `Y`
into the square on `X` is the mate calculus — which is what the source omits.

The granted hypothesis is `Stacks.SectionRingProjTheta.pullbackComparison_tensorHom`'s `hmul`:

```
    mult ≫ c.app (𝓕 ⊗ 𝓖) = (c.app 𝓕 ⊗ₘ c.app 𝓖) ≫ μ (f_*) 𝓕 𝓖
```

It mentions only `c`, Equation 01MQ's multiplication map `mult`, and the lax monoidal structure
of `f_*`, which is **not** a further binder: it is the mate of the monoidal structure of the
left adjoint, pinned by Mathlib's `CategoryTheory.Adjunction.IsMonoidal`. So the only thing
granted is a property of Tag 0B5I's family, on the `Proj` side, stated without reference to
`θ`.

**The granted property is exactly what defeats the obstruction, and that is proved rather than
asserted.** `add_self_eq_zero_of_mulComm_neg` shows `hmul` cannot hold simultaneously for `c`
and for `-c` unless the common value is `2`-torsion. The perturbation that kills the square
when `c` is free is therefore inadmissible as soon as `hmul` is imposed, so the obstruction of
the sibling file and the theorem here are not in tension: they bracket the same statement from
the two sides.

## Main definitions

* `Stacks.SectionRingProjTheta.crossIso` and
  `Stacks.SectionRingProjTheta.pullbackTildeCrossIso`: the crossing isomorphism `f^* A ≅ A|_X`
  of `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, through which
  `pullbackComparison` is defined from `restrictComparison`; the second is the first with its
  source pinned to the folded spelling `f^* M̃`.
* `Stacks.SectionRingProjTheta.pullbackTwistTop`: **Tag 01QK's top arrow**,
  `f^*M̃ ⊗ f^*Ñ ⟶ f^*((M · N)~)`, built from the tensorator of restriction along `f`, Equation
  01MQ's multiplication map, and the crossing isomorphism. It is *constructed*, not bound, which
  is what distinguishes the square proved here from the arbitrary top arrow the sibling file's
  obstruction rules out.

## Main results

* `Stacks.SectionRingProjTheta.mateTensorHom`: **the mate identity**, with no hypothesis: for an
  adjunction `F ⊣ G` with `F` monoidal and `G` carrying the mate lax structure, the `⊗ₘ` of two
  transposed morphisms is the transpose of their `⊗ₘ` followed by `μ G`.
* `Stacks.SectionRingProjTheta.tensorHom_eq_of_mulComm` and
  `Stacks.SectionRingProjTheta.mulComm_of_tensorHom_eq`: **the square and the
  multiplication-compatibility of `c` are equivalent**, abstractly.
* `Stacks.SectionRingProjTheta.add_self_eq_zero_of_mulComm_neg`: multiplication-compatibility
  is destroyed by negating `c`; this is what rules out the sibling file's perturbation.
* `Stacks.SectionRingProjTheta.conjugated_square`: the square is stable under isomorphisms of
  its three upper corners.
* `Stacks.SectionRingProjTheta.restrictComparison_tensorHom`: the square at
  `Stacks.SectionRingProjQuasicoherent.restrictComparison`, the family that the Tag 01QJ
  declaration `pullbackComparison` is *defined* from. This is the engine.
* `Stacks.SectionRingProjTheta.pullbackComparison_tensorHom`: **assertion (ii) of Tag 01QK**, at
  the Tag 01QJ declaration
  `Stacks.SectionRingProjQuasicoherent.pullbackComparison`. This is the declaration that carries
  the `@[stacks 01QK]` attribute.
* `Stacks.SectionRingProjTheta.pullbackComparison_tensorHom_natTensorPow`: the same read at
  `𝓖 = 𝓛^{⊗ n}`, which is the Remark's own instance of the square.

## Implementation notes

**Why the proof goes through `restrictComparison`.** `restrictComparison L hL c |>.app 𝓕` is
by definition `(restrictFunctor f).map (c.app 𝓕) ≫ counit.app 𝓕`, which is exactly
`(restrictAdjunction f).homEquiv _ _ |>.symm (c.app 𝓕)`, so the abstract theorem applies to it
with no transport at all. `pullbackComparison` is `restrictComparison` precomposed with the
whiskering of `Scheme.Modules.restrictFunctorIsoPullback`, so the square there is obtained by
conjugating the top arrow with that one isomorphism, which is `conjugated_square`.

**Two deliberate `rfl` lemmas, and why they are not redundant.** `pullbackComparison_app` and
`pullbackTwistTop_eq` both hold by `rfl`, and the final theorem could in principle be a single
`exact`. It cannot in practice: that term makes the **kernel** delta-unfold
`Stacks.SectionRingProjQuasicoherent.pullbackTildeFunctor` underneath the projection `.obj`,
inside the implicit object arguments of `⊗ₘ`, at three corners simultaneously, and that
exceeds the kernel's budget (`(kernel) deterministic timeout`; the file builds in
~180s without the declaration and fails after ~353s with it). Each of the unfoldings is cheap in
isolation, so they are performed one at a time: `pullbackTildeCrossIso` pays for the object
spelling once, at an `Iso` type, and the two `rfl` lemmas are then rewritten into the goal
propositionally before the `exact`. No `set_option` is available in this tree to raise the
limit.

**The monoidal structure of restriction is a binder, and negating it is harmless.** Mathlib has
no `Functor.Monoidal` instance for `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, and
building one needs the comparison of `TensorStalkRingedSpace.tensorSheaf` with
`TensorSheafification.tensorSheaf` that this repository does not have (see "What is not done").
It is therefore carried as `[(Scheme.Modules.restrictFunctor f).Monoidal]`. The sibling file
warns that arbitrary isomorphism binders make the square false by the same negation argument;
that does not apply here, because `μ (f_*)` appearing in `hmul` is *derived* from this structure
through the mate, so negating the structure negates `hmul`'s right-hand side and the hypothesis
is no longer about the same `c`. Nothing is granted twice.

**`rw` is avoided on the monoidal coherences.** `mateTensorHom` is a `calc` of `congrArg`s and
`Category.assoc` steps, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/TwistedSectionsShift/Basic.lean`: `rw` matches only up to
instance transparency, and the monoidal structure reaches these goals by a different path from
the one `rw` elaborates the class fields with.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Equation 27.10.0.4, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)

## What is not done here

**Assertion (i) of Tag 01QK is not proved**, and the `@[stacks 01QK]` facet string below says
so. That assertion is that Tag 01QI's isomorphism `f^*𝒪_Y(n) → 𝓛^{⊗ n}` "is just
`θ_{𝓛^{⊗ n}}`", and Tag 01QI's *second* claim — the map itself — does not exist in this
repository: `StacksFrontier/AlgebraicGeometry/SectionRingProjGoodOpen/Basic.lean` carries
`@[stacks 01QI]` scoped by its clause string to the first claim alone. So assertion (i) has no
left-hand side to be about, and defining the map *as* `θ_{𝓛^{⊗ n}}` would make the assertion a
tautology.

**Equation 01MQ's multiplication map is a binder, not
`Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap`.** That declaration is stated for
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` and for the algebraic shift
`Stacks.GradedModule.shiftedGrading`, whereas the `⊗` here is
`Stacks.SheafInternalHom.schemeMonoidalCategory`, i.e. `TensorSheafification.tensorSheaf`. The
two tensor-product sheaves are not `rfl`-equal and the repository has only the half bridge
`Stacks.SheafOfModules.tensorObjIso`; and the shift is identified with
`Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` only abstractly, by
`Stacks.Monoidal.ModuleSystem.powShiftEquiv` of
`StacksFrontier/AlgebraicGeometry/TwistedSectionsShift/Basic.lean`, whose sheaf-level
instantiation is not carried out there. Binding `mult` is therefore the honest statement: the
theorem says that *whatever* morphism Equation 01MQ supplies, the square for it follows from
the compatibility of `c` with it. Unlike the sibling file's arbitrary top arrow `t`, this
`mult` is **not** the top arrow of the square: the top arrow is constructed from it by
`pullbackTwistTop`, and the hypothesis `hmul` ties `mult` to `c`.

**No `Functor.Monoidal` structure on restriction or pullback of sheaves of modules is
constructed.** The ringed-space level has four
(`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal` and companions), none transported
to `AlgebraicGeometry.Scheme.Modules`, and the transport is blocked on the tensor-sheaf
comparison named above. Supplying it would discharge the one instance binder here.

**Nothing is claimed about `θ` being an isomorphism.** Tag 01QJ's main assertion is not
proved — only clause (b), the functoriality — and the square proved here does not need it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

open Stacks.Ample
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (tildeFunctor pullbackTildeFunctor restrictComparison
  pullbackComparison)

universe v₁ v₂ u₁ u₂ u

namespace Stacks.SectionRingProjTheta

/-- Composing in the source of a transposed morphism: `F.map` of a composite, reassociated. -/
private theorem μ_map_comp_counit {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.Monoidal] {A B R : C} {P : D} (u : A ⊗ B ⟶ R) (v : R ⟶ G.obj P) :
    μ F A B ≫ F.map u ≫ F.map v ≫ adj.counit.app P
      = μ F A B ≫ F.map (u ≫ v) ≫ adj.counit.app P := by
  simp

/-! ### The mate calculus

A transposed family is compatible with `⊗ₘ` exactly when the family it transposes is compatible
with the lax monoidal structure of the right adjoint. This section is pure category theory and
mentions nothing about `Proj`.
-/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- **The mate identity.** For `cA : A ⟶ G P` and `cB : B ⟶ G Q`, write `θ` for the transpose
`F.map c ≫ counit`. Then `θ_A ⊗ₘ θ_B` is the transpose of `(cA ⊗ₘ cB) ≫ μ G`, after the
tensorator `μ F`.

No hypothesis is needed: this is the statement that the lax monoidal structure of a right
adjoint is the mate of the monoidal structure of the left adjoint, which in Mathlib is
`CategoryTheory.Adjunction.map_μ_comp_counit_app_tensor`, combined with the naturality of
`μ F` and the invertibility of `μ F` for a *monoidal* (not merely lax monoidal) `F`. -/
theorem mateTensorHom {A B : C} {P Q : D} (cA : A ⟶ G.obj P) (cB : B ⟶ G.obj Q) :
    (F.map cA ≫ adj.counit.app P) ⊗ₘ (F.map cB ≫ adj.counit.app Q)
      = μ F A B ≫ F.map ((cA ⊗ₘ cB) ≫ μ G P Q) ≫ adj.counit.app (P ⊗ Q) := by
  have hid : μ F (G.obj P) (G.obj Q) ≫ δ F (G.obj P) (G.obj Q) ≫
        (adj.counit.app P ⊗ₘ adj.counit.app Q) = adj.counit.app P ⊗ₘ adj.counit.app Q := by
    rw [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp]
  calc (F.map cA ≫ adj.counit.app P) ⊗ₘ (F.map cB ≫ adj.counit.app Q)
      = (F.map cA ⊗ₘ F.map cB) ≫ (adj.counit.app P ⊗ₘ adj.counit.app Q) :=
        (tensorHom_comp_tensorHom _ _ _ _).symm
    _ = (F.map cA ⊗ₘ F.map cB) ≫ (μ F (G.obj P) (G.obj Q) ≫
          δ F (G.obj P) (G.obj Q) ≫ (adj.counit.app P ⊗ₘ adj.counit.app Q)) :=
        congrArg ((F.map cA ⊗ₘ F.map cB) ≫ ·) hid.symm
    _ = (F.map cA ⊗ₘ F.map cB) ≫ (μ F (G.obj P) (G.obj Q) ≫
          (F.map (μ G P Q) ≫ adj.counit.app (P ⊗ Q))) := by
        rw [adj.map_μ_comp_counit_app_tensor]
    _ = ((F.map cA ⊗ₘ F.map cB) ≫ μ F (G.obj P) (G.obj Q)) ≫
          (F.map (μ G P Q) ≫ adj.counit.app (P ⊗ Q)) := (Category.assoc _ _ _).symm
    _ = (μ F A B ≫ F.map (cA ⊗ₘ cB)) ≫ (F.map (μ G P Q) ≫ adj.counit.app (P ⊗ Q)) :=
        congrArg (· ≫ (F.map (μ G P Q) ≫ adj.counit.app (P ⊗ Q)))
          (Functor.LaxMonoidal.μ_natural F cA cB)
    _ = μ F A B ≫ F.map ((cA ⊗ₘ cB) ≫ μ G P Q) ≫ adj.counit.app (P ⊗ Q) :=
        by rw [Category.assoc, μ_map_comp_counit adj]

/-- **The twist square from multiplication-compatibility.** If the family `c` is compatible with
a multiplication `mult : A ⊗ B ⟶ R` on the right-adjoint side, then the transposed family is
compatible with `⊗ₘ` on the left-adjoint side, the top arrow being `μ F` followed by `F mult`.

This is the abstract form of assertion (ii) of Stacks Tag 01QK. -/
theorem tensorHom_eq_of_mulComm {A B R : C} {P Q : D}
    (mult : A ⊗ B ⟶ R) (cA : A ⟶ G.obj P) (cB : B ⟶ G.obj Q) (cR : R ⟶ G.obj (P ⊗ Q))
    (hmul : mult ≫ cR = (cA ⊗ₘ cB) ≫ μ G P Q) :
    (F.map cA ≫ adj.counit.app P) ⊗ₘ (F.map cB ≫ adj.counit.app Q)
      = μ F A B ≫ F.map mult ≫ (F.map cR ≫ adj.counit.app (P ⊗ Q)) := by
  rw [mateTensorHom adj cA cB, ← hmul, μ_map_comp_counit adj]

/-- **The converse**: the square forces the multiplication-compatibility of `c`. Together with
`tensorHom_eq_of_mulComm` this says that the hypothesis granted for Tag 01QK is not a
convenient surrogate but the exact content of the square, transported across the adjunction.

The cancellation is by `μ F`, which is invertible because `F` is monoidal, followed by the
injectivity of the transposition. -/
theorem mulComm_of_tensorHom_eq {A B R : C} {P Q : D}
    (mult : A ⊗ B ⟶ R) (cA : A ⟶ G.obj P) (cB : B ⟶ G.obj Q) (cR : R ⟶ G.obj (P ⊗ Q))
    (hsq : (F.map cA ≫ adj.counit.app P) ⊗ₘ (F.map cB ≫ adj.counit.app Q)
      = μ F A B ≫ F.map mult ≫ (F.map cR ≫ adj.counit.app (P ⊗ Q))) :
    mult ≫ cR = (cA ⊗ₘ cB) ≫ μ G P Q := by
  have key : μ F A B ≫ F.map (mult ≫ cR) ≫ adj.counit.app (P ⊗ Q)
      = μ F A B ≫ F.map ((cA ⊗ₘ cB) ≫ μ G P Q) ≫ adj.counit.app (P ⊗ Q) := by
    rw [← μ_map_comp_counit adj, ← hsq]
    exact mateTensorHom adj cA cB
  have cancel : ∀ u v : A ⊗ B ⟶ G.obj (P ⊗ Q),
      μ F A B ≫ F.map u ≫ adj.counit.app (P ⊗ Q)
        = μ F A B ≫ F.map v ≫ adj.counit.app (P ⊗ Q) → u = v := by
    intro u v h
    have e : ∀ w : A ⊗ B ⟶ G.obj (P ⊗ Q),
        δ F A B ≫ μ F A B ≫ F.map w ≫ adj.counit.app (P ⊗ Q)
          = F.map w ≫ adj.counit.app (P ⊗ Q) := fun w => by
      rw [← Category.assoc, Functor.Monoidal.δ_μ, Category.id_comp]
    exact (adj.homEquiv _ _).symm.injective ((e u).symm.trans ((congrArg (δ F A B ≫ ·) h).trans
      (e v)))
  exact cancel _ _ key

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- **Multiplication-compatibility is destroyed by negating `c`.** If `hmul` holds both for
`(cA, cB, cR)` and for `(-cA, -cB, -cR)` then the common value is `2`-torsion: the left-hand
side `mult ≫ cR` is odd in `c` while the right-hand side `(cA ⊗ₘ cB) ≫ μ G` is even.

This is the complement of
`Stacks.SectionRingProjQuasicoherent.TwistCompatibility.not_forall_twistSquare`. That
declaration perturbs Tag 0B5I's binder by negation and concludes that no `θ`-free top arrow can
make the square hold uniformly in the binder. Here the same perturbation is shown to leave the
hypothesis `hmul` behind, so the square proved in this file is not uniform in the binder and the
two results agree. -/
theorem add_self_eq_zero_of_mulComm_neg {A B R : C} {P Q : D}
    (mult : A ⊗ B ⟶ R) (cA : A ⟶ G.obj P) (cB : B ⟶ G.obj Q) (cR : R ⟶ G.obj (P ⊗ Q))
    (hmul : mult ≫ cR = (cA ⊗ₘ cB) ≫ μ G P Q)
    (hneg : mult ≫ (-cR) = ((-cA) ⊗ₘ (-cB)) ≫ μ G P Q) :
    (mult ≫ cR) + (mult ≫ cR) = 0 := by
  rw [Stacks.SectionRingProjQuasicoherent.TwistCompatibility.neg_tensorHom_neg, ← hmul,
    Preadditive.comp_neg] at hneg
  exact add_eq_zero_iff_eq_neg.mpr hneg.symm

end Preadditive

end Abstract

section Conjugate

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- **Transporting the square along isomorphisms of its three upper corners.** If the square
holds for `θA, θB, θR` with top arrow `m`, then it holds for the conjugated morphisms
`wA.hom ≫ θA` and so on, with top arrow `(wA.hom ⊗ₘ wB.hom) ≫ m ≫ wR.inv`.

This is the bookkeeping that carries assertion (ii) of Stacks Tag 01QK from the restriction
spelling of `θ` to the pullback spelling, the two being related by one isomorphism
(`Scheme.Modules.restrictFunctorIsoPullback`) at each corner. It is proved here, at an abstract
monoidal category, because at the sheaf level `rw` cannot match `⊗ₘ` against a goal in which
`Stacks.SectionRingProjQuasicoherent.pullbackTildeFunctor` has to be unfolded to expose the
objects. -/
theorem conjugated_square {A A' B B' R R' P Q : C} (wA : A ≅ A') (wB : B ≅ B') (wR : R ≅ R')
    (m : A' ⊗ B' ⟶ R') (θA : A' ⟶ P) (θB : B' ⟶ Q) (θR : R' ⟶ P ⊗ Q)
    (h : θA ⊗ₘ θB = m ≫ θR) :
    (wA.hom ≫ θA) ⊗ₘ (wB.hom ≫ θB)
      = ((wA.hom ⊗ₘ wB.hom) ≫ m ≫ wR.inv) ≫ (wR.hom ≫ θR) := by
  rw [← tensorHom_comp_tensorHom, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Conjugate

/-! ### Assertion (ii) of Stacks Tag 01QK -/

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : IsAmple X L)

section Restrict

variable [IsOpenImmersion (projHomOfIsAmple L hL)]
  [(Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).Monoidal]
  [(Scheme.Modules.pushforward (projHomOfIsAmple L hL)).LaxMonoidal]
  [(Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).IsMonoidal]

/-- **The square at the restriction spelling of `θ`**, which is the engine of
`pullbackComparison_tensorHom` below.

`Stacks.SectionRingProjQuasicoherent.restrictComparison L hL c |>.app 𝓕` is by definition the
transpose of `c.app 𝓕` across `Scheme.Modules.restrictAdjunction`, so this is
`tensorHom_eq_of_mulComm` with no transport at all. The granted hypothesis `hmul` is the
compatibility of Tag 0B5I's family `c` with Equation 01MQ's multiplication map, stated on
`Proj Γ_*(X, L)` and mentioning no `θ`. -/
theorem restrictComparison_tensorHom
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F G : X.Modules)
    (mult : (tildeFunctor L).obj F ⊗ (tildeFunctor L).obj G ⟶ (tildeFunctor L).obj (F ⊗ G))
    (hmul : mult ≫ c.app (F ⊗ G) = (c.app F ⊗ₘ c.app G) ≫
      μ (Scheme.Modules.pushforward (projHomOfIsAmple L hL)) F G) :
    (restrictComparison L hL c).app F ⊗ₘ (restrictComparison L hL c).app G
      = μ (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL))
            ((tildeFunctor L).obj F) ((tildeFunctor L).obj G) ≫
          (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map mult ≫
            (restrictComparison L hL c).app (F ⊗ G) :=
  tensorHom_eq_of_mulComm (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL))
    mult (c.app F) (c.app G) (c.app (F ⊗ G)) hmul

/-- The crossing isomorphism `f^* A ≅ A|_X` of `Scheme.Modules.restrictFunctorIsoPullback`,
through which `Stacks.SectionRingProjQuasicoherent.pullbackComparison` is defined from
`restrictComparison`. -/
def crossIso (A : (AlgebraicGeometry.Proj (grading L)).Modules) :
    (Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj A ≅
      (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).obj A :=
  ((Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL)).app A).symm

/-- **`crossIso` with its source pinned to the folded spelling** `f^* M̃` rather than to
`f^*` applied to `M̃`.

The two types are definitionally equal — the only difference is whether
`Stacks.SectionRingProjQuasicoherent.pullbackTildeFunctor` is unfolded — but which one is
*written* decides whether the kernel can check the declarations below. Stating this one
isomorphism at the folded type pays for that unfolding once, here, where it is a single
comparison of `Iso` types; every consumer then matches the goal syntactically. Using `crossIso`
directly instead makes the kernel delta-unfold a `def` underneath the projection `.obj` inside
the implicit object arguments of `⊗ₘ`, at three corners at once, and that exceeds the
kernel's budget. -/
def pullbackTildeCrossIso (F : X.Modules) :
    (pullbackTildeFunctor L hL).obj F ≅
      (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).obj ((tildeFunctor L).obj F) :=
  crossIso L hL ((tildeFunctor L).obj F)

omit [(Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).Monoidal]
  [(Scheme.Modules.pushforward (projHomOfIsAmple L hL)).LaxMonoidal]
  [(Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).IsMonoidal] in
/-- **The two spellings of `θ` differ by exactly the crossing isomorphism**, on the nose. This
is the definition of `Stacks.SectionRingProjQuasicoherent.pullbackComparison` read at an object;
`IsOpenImmersion` is a `Prop` class, so the instance supplied by the binder here and the one
`pullbackComparison` derives internally from
`Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple` are interchangeable and the
identity is `rfl`. -/
theorem pullbackComparison_app
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL)) (F : X.Modules) :
    (pullbackComparison L hL c).app F
      = (pullbackTildeCrossIso L hL F).hom ≫ (restrictComparison L hL c).app F :=
  rfl

/-- **Stacks Tag 01QK's top arrow, constructed.** The pullback of Equation 01MQ's multiplication
map `mult`, read through the tensorator of restriction along `f` and the crossing isomorphism: a
morphism `f^*M̃ ⊗ f^*Ñ ⟶ f^*((M · N)~)`.

It is a *construction* from `mult`, not a binder, which is what makes
`pullbackComparison_tensorHom` stronger than
`Stacks.SectionRingProjQuasicoherent.TwistCompatibility.not_forall_twistSquare` permits for an
arbitrary top arrow. -/
def pullbackTwistTop (F G : X.Modules)
    (mult : (tildeFunctor L).obj F ⊗ (tildeFunctor L).obj G ⟶ (tildeFunctor L).obj (F ⊗ G)) :
    (pullbackTildeFunctor L hL).obj F ⊗ (pullbackTildeFunctor L hL).obj G ⟶
      (pullbackTildeFunctor L hL).obj (F ⊗ G) :=
  ((pullbackTildeCrossIso L hL F).hom ⊗ₘ (pullbackTildeCrossIso L hL G).hom) ≫
    (μ (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)) ((tildeFunctor L).obj F)
          ((tildeFunctor L).obj G) ≫
        (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map mult) ≫
      (pullbackTildeCrossIso L hL (F ⊗ G)).inv

omit [(Scheme.Modules.pushforward (projHomOfIsAmple L hL)).LaxMonoidal]
  [(Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).IsMonoidal] in
/-- The defining equation of `pullbackTwistTop`, as a propositional identity. It is needed
because the kernel must not be asked to unfold `pullbackTwistTop` at the same time as the three
components of `pullbackComparison`; splitting the unfoldings into separate small `rfl`s is what
brings `pullbackComparison_tensorHom` inside the kernel's budget. -/
theorem pullbackTwistTop_eq (F G : X.Modules)
    (mult : (tildeFunctor L).obj F ⊗ (tildeFunctor L).obj G ⟶ (tildeFunctor L).obj (F ⊗ G)) :
    pullbackTwistTop L hL F G mult
      = ((pullbackTildeCrossIso L hL F).hom ⊗ₘ (pullbackTildeCrossIso L hL G).hom) ≫
        (μ (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)) ((tildeFunctor L).obj F)
              ((tildeFunctor L).obj G) ≫
            (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map mult) ≫
          (pullbackTildeCrossIso L hL (F ⊗ G)).inv :=
  rfl

/-- **Assertion (ii) of Stacks Tag 01QK, at the Tag 01QJ comparison.**

With `θ = Stacks.SectionRingProjQuasicoherent.pullbackComparison L hL c`, the natural
transformation `f^* M̃ ⟶ 𝓕` that carries `@[stacks 01QJ]`, and with the top arrow
`Stacks.SectionRingProjTheta.pullbackTwistTop` *built* from Equation 01MQ's multiplication map
`mult`, Stacks Tag 01QK's square commutes:

```
    θ_𝓕 ⊗ₘ θ_𝓖 = pullbackTwistTop mult ≫ θ_{𝓕 ⊗ 𝓖}.
```

Both lower corners of the Remark's square are the single object `𝓕 ⊗ 𝓖` and its bottom arrow is
the identity, so this equation is the whole of assertion (ii).

The hypothesis `hmul` is the compatibility of Tag 0B5I's family `c` with `mult`, on
`Proj Γ_*(X, L)`, mentioning no `θ`. It is the characterisation of `c` that
`Stacks.SectionRingProjQuasicoherent.TwistCompatibility.not_forall_twistSquare` proves to be
necessary; `mulComm_of_tensorHom_eq` shows it is equivalent to the conclusion across the
adjunction, so nothing weaker would do, and `add_self_eq_zero_of_mulComm_neg` shows it is
destroyed by the negation of `c` that defeats an unconstrained binder. -/
@[stacks 01QK "assertion (ii): the Remark's square commutes, at the Tag 01QJ comparison
`pullbackComparison`, with the top arrow CONSTRUCTED as `pullbackTwistTop` — the tensorator of
restriction along `f` composed with `f^*` of Equation 01MQ's multiplication map — rather than
left arbitrary, which is what distinguishes this from the sibling file `TwistCompatibility`'s
`not_forall_twistSquare`. Three things are granted as named binders: (a) `hmul`, the
compatibility of Tag 0B5I's family `c` with that multiplication map on `Proj Γ_*(X, L)`, which
is the characterisation of `c` that `not_forall_twistSquare` proves to be necessary and
`add_self_eq_zero_of_mulComm_neg` proves is not stable under its perturbation; (b) the
multiplication map itself as the binder `mult`, Equation 01MQ's `moduleTwistMap` being stated
for the other of this repository's two tensor-product sheaves; (c) a monoidal structure on
restriction along `f` as an instance binder, which Mathlib does not provide for
`Scheme.Modules.restrictFunctor`. Assertion (i), that Tag 01QI's map `f^*𝒪_Y(n) → 𝓛^{⊗n}` is
`θ_{𝓛^{⊗n}}`, is NOT covered: that map does not exist in this repository"]
theorem pullbackComparison_tensorHom
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F G : X.Modules)
    (mult : (tildeFunctor L).obj F ⊗ (tildeFunctor L).obj G ⟶ (tildeFunctor L).obj (F ⊗ G))
    (hmul : mult ≫ c.app (F ⊗ G) = (c.app F ⊗ₘ c.app G) ≫
      μ (Scheme.Modules.pushforward (projHomOfIsAmple L hL)) F G) :
    (pullbackComparison L hL c).app F ⊗ₘ (pullbackComparison L hL c).app G
      = pullbackTwistTop L hL F G mult ≫ (pullbackComparison L hL c).app (F ⊗ G) := by
  rw [pullbackComparison_app L hL c F, pullbackComparison_app L hL c G,
    pullbackComparison_app L hL c (F ⊗ G), pullbackTwistTop_eq]
  exact conjugated_square (pullbackTildeCrossIso L hL F) (pullbackTildeCrossIso L hL G)
    (pullbackTildeCrossIso L hL (F ⊗ G))
    (μ (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)) ((tildeFunctor L).obj F)
        ((tildeFunctor L).obj G) ≫
      (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map mult)
    ((restrictComparison L hL c).app F) ((restrictComparison L hL c).app G)
    ((restrictComparison L hL c).app (F ⊗ G))
    ((restrictComparison_tensorHom L hL c F G mult hmul).trans (Category.assoc _ _ _).symm)

/-- **Stacks Tag 01QK's own instance of the square**: the second tensor factor is the `n`-th
tensor power `𝓛^{⊗ n}` of the ample invertible module, which is the module whose graded section
module the Remark identifies with `S(n)`. -/
theorem pullbackComparison_tensorHom_natTensorPow
    (c : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL))
    (F : X.Modules) (n : ℕ)
    (mult : (tildeFunctor L).obj F ⊗ (tildeFunctor L).obj (Stacks.TensorPowers.natTensorPow L n)
      ⟶ (tildeFunctor L).obj (F ⊗ Stacks.TensorPowers.natTensorPow L n))
    (hmul : mult ≫ c.app (F ⊗ Stacks.TensorPowers.natTensorPow L n) =
      (c.app F ⊗ₘ c.app (Stacks.TensorPowers.natTensorPow L n)) ≫
        μ (Scheme.Modules.pushforward (projHomOfIsAmple L hL)) F
          (Stacks.TensorPowers.natTensorPow L n)) :
    (pullbackComparison L hL c).app F ⊗ₘ
        (pullbackComparison L hL c).app (Stacks.TensorPowers.natTensorPow L n)
      = pullbackTwistTop L hL F (Stacks.TensorPowers.natTensorPow L n) mult ≫
          (pullbackComparison L hL c).app (F ⊗ Stacks.TensorPowers.natTensorPow L n) :=
  pullbackComparison_tensorHom L hL c F (Stacks.TensorPowers.natTensorPow L n) mult hmul

end Restrict

end Scheme

end Stacks.SectionRingProjTheta

end
