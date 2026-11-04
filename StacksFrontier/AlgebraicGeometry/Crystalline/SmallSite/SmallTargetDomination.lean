module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareCovering

/-!
# Dominating a thickening by the small site, over an object of the small site of the target

Let `f : X ⟶ X'` be a morphism of the global crystalline situations of [Stacks, Tag 07I5], write
`f_CRIS : CRIS(X/S) ⥤ CRIS(X'/S')` for change of divided power base, [Stacks, Tag 07IC], and let
`D` be an object of the *small* site `Cris(X'/S')`.

This module answers, for an object `A` of `CRIS(X/S)` equipped with a morphism
`ψ : f_CRIS(A) ⟶ D`, the question which the composition functoriality of `f_{cris, *}` turns on:

> can `A` be refined so that `ψ` factors through an object of the small site `Cris(X/S)`?

Both halves of the answer are proved here, in the only form available — *locally* on `A`:

* `dominationOverSieve_mem`: the refinements of `A` for which `ψ` does factor through an object
  of `Cris(X/S)` form a **covering sieve**; and
* `commonRefinementSieve_mem`: any **two** such factorizations agree after a further covering,
  the refining object mapping to both and the two morphisms to `D` becoming equal.

The second is not cofinality and does not follow from the cofilteredness
`Crystalline.GlobalCrystallineSituation.SmallSite.exists_cone_domination` of the dominations with
no target: a common refinement of two dominations need not be compatible with the two morphisms
down to `D`.  What makes it true is that the common refinement produced here is a *pushout*, and a
morphism out of a pushout is determined by its two legs; both candidate morphisms to `D` have the
same legs.  That is `domination_unique` below, and it is why this module works with
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.crystallinePushout` — the pushout of
[Stacks, Tag 07RT] as an object of the small site — rather than with the existence statement
`...CrystallineThickening.exists_crystalline_hom_of_affine`.

## Why the target has to be in the small site

The open `V` of `X` over which the pushout object lies is chosen inside `f^{-1}(U_D)`, and that is
possible because `U_D ⟶ X'` is an *open immersion*: `D` is an object of the small site.  For an
object `A'` of the big site `CRIS(X'/S')` in place of `D` there is no such open, the morphism
`V ⟶ U_{A'}` needed for the factorization does not exist, and the statements of this module are
false — the composition functoriality of `f_{cris, *}` really does need the restriction to the
small site which the third factor `π_{X', *}` of [Stacks, Tag 07IK] performs.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.IsDominatedOver` — the property that
  `ψ : f_CRIS(A) ⟶ D` factors through an object of `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.dominationOverSieve` — the sieve on `A` of the
  refinements over which `ψ` is so factored.
* `Crystalline.GlobalCrystallineSituation.SmallSite.commonRefinementSieve` — the sieve on `A` of
  the refinements over which two given factorizations are refined by a common one, compatibly with
  the two morphisms to `D`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.exists_domination_of_affine` — the pushout
  object dominates `A` over `D` when the structure map of `A` lifts affinely to an open of `X`
  inside `f^{-1}(U_D)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.domination_unique` — **the morphism to `D` out
  of a pushout object is unique** once its composite with the morphism from `A` is prescribed.
* `Crystalline.GlobalCrystallineSituation.SmallSite.exists_hom_of_range_le` — the pushout
  object maps to any object of `Cris(X/S)` dominating `A` whose open of `X` contains the chosen
  one, compatibly with the morphisms from `A`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.dominationOverSieve_mem` — **the covering
  step**.
* `Crystalline.GlobalCrystallineSituation.SmallSite.commonRefinementSieve_mem` — **the
  independence step**.

## What is and is not proved

Everything here is unconditional, for every morphism of global crystalline situations.  No tag
attribute is placed: nothing here is a clause of a tag of the Stacks project, the covering and
independence steps being inputs to the composition functoriality of `f_{cris, *}` in
`SmallSite/CrisDirectImageComposition.lean`.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

open CrystallineThickening

namespace SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- A sieve on `A` lies in the topology as soon as it contains the restriction of `A` to every
affine open `W` of its ambient scheme whose part of `U` maps into an affine open `V ≤ U` of `X`,
where `U` is an open of `X` containing the image of the structure map of `A`. -/
private theorem mem_topology_of_affine_pieces (A : Thickening S) (U : S.X.Opens)
    (hA : ∀ z : A.thickening.source, A.toX.base z ∈ U) (T : Sieve A)
    (hT : ∀ (W : A.thickening.target.scheme.Opens) (V : S.X.Opens), V ≤ U →
      Set.range ((A.restrictOpen W).toX).base ⊆ Set.range V.ι.base →
      IsAffine (V : Scheme.{u}) → IsAffine (A.restrictOpen W).thickening.source →
      T.arrows (A.restrictOpenHom W)) :
    T ∈ topology S A := by
  choose W V' hxW hV'V hWV using Thickening.exists_affine_neighbourhood_toX_of_mem A U hA
  set Wfam : ULift.{u + 1} A.thickening.target.scheme → A.thickening.target.scheme.Opens :=
    fun i ↦ (W i.down).1 with hWfam
  have hcov : Thickening.IsZariskiCovering (A.restrictOpenCover Wfam) :=
    A.isZariskiCovering_restrictOpenCover Wfam fun x ↦ ⟨⟨x⟩, hxW x⟩
  apply (topology S).superset_covering _
    (zariskiCovering_mem_topology S (A.restrictOpenCover Wfam) hcov)
  rw [Sieve.generate_le_iff]
  intro C g hg
  cases hg with
  | mk i =>
    have : IsAffine ((W i.down).1 : Scheme.{u}) := (W i.down).property
    have : IsAffine ((V' i.down).1 : Scheme.{u}) := (V' i.down).property
    have : IsAffine (A.restrictOpen (Wfam i)).thickening.target.scheme :=
      inferInstanceAs (IsAffine ((W i.down).1 : Scheme.{u}))
    exact hT (Wfam i) (V' i.down).1 (hV'V i.down)
      (by
        rintro _ ⟨z, rfl⟩
        exact ⟨⟨_, hWV i.down z.property⟩, rfl⟩) inferInstance
      (isAffine_of_isAffineHom (A.restrictOpen (Wfam i)).thickening.immersion)

include hf

/-- **The structure morphisms to the two divided power bases are compatible with `f`.**  Both
composites are the structure morphism of `X` to `S'`, read through the closed fibres; this is the
hypothesis `hf` of a morphism of global crystalline situations, pushed along the closed immersion
of the closed fibre. -/
theorem sourceToBase_comp_base :
    sourceToBase S ≫ fS.hom = fX ≫ sourceToBase S' := by
  rw [sourceToBase, sourceToBase, Category.assoc,
    ← DividedPowerScheme.closedFiberMap_comp_closedFiberι fS, ← Category.assoc, hf,
    Category.assoc]

/-! ### The components of a morphism out of a rebased object

Change of divided power base leaves the underlying divided power thickening alone, so a morphism
`f_CRIS(A) ⟶ C` is given by the same data as a morphism `A ⟶ C`: a map of thickened schemes and a
divided power map of ambient schemes.  The three definitions below name that data with its plain
type, so that the morphism of thickened schemes of `ψ` is a morphism
`U_A ⟶ U_C` and not a morphism out of the thickened scheme *of the rebased object*, which is the
same scheme but not the same expression.  Everything in this module is phrased through them. -/

section Rebased

variable {A : Thickening S} {C : Thickening S'}

/-- The map of thickened schemes of a morphism out of a rebased object. -/
def rebasedSourceHom (ψ : (changeBase S S' fS fX hf).obj A ⟶ C) :
    A.thickening.source ⟶ C.thickening.source :=
  ψ.sourceHom

/-- The divided power map of ambient schemes of a morphism out of a rebased object. -/
def rebasedTargetHom (ψ : (changeBase S S' fS fX hf).obj A ⟶ C) :
    A.thickening.target ⟶ C.thickening.target :=
  ψ.targetHom

/-- A morphism out of a rebased object is over `X'`, which for its plain components means that the
structure map of `A` to `X`, followed by `f`, is the one of `C`. -/
theorem rebasedSourceHom_comp_toX (ψ : (changeBase S S' fS fX hf).obj A ⟶ C) :
    rebasedSourceHom S S' fS fX hf ψ ≫ C.toX = A.toX ≫ fX :=
  ψ.toX_naturality

/-- A morphism out of a rebased object is over `S'`, which for its plain components means that the
structure morphism of `A` to `S`, followed by `f`, is the one of `C`. -/
theorem rebasedTargetHom_comp_toBase (ψ : (changeBase S S' fS fX hf).obj A ⟶ C) :
    rebasedTargetHom S S' fS fX hf ψ ≫ C.toBase = A.toBase ≫ fS :=
  ψ.base_naturality

/-- The square of thickenings of a morphism out of a rebased object commutes. -/
theorem rebased_immersion_naturality (ψ : (changeBase S S' fS fX hf).obj A ⟶ C) :
    A.thickening.immersion ≫ (rebasedTargetHom S S' fS fX hf ψ).hom =
      rebasedSourceHom S S' fS fX hf ψ ≫ C.thickening.immersion :=
  ψ.immersion_naturality

/-- A morphism out of a rebased object is determined by its two plain components. -/
theorem rebased_ext {ψ φ : (changeBase S S' fS fX hf).obj A ⟶ C}
    (h₁ : rebasedSourceHom S S' fS fX hf ψ = rebasedSourceHom S S' fS fX hf φ)
    (h₂ : rebasedTargetHom S S' fS fX hf ψ = rebasedTargetHom S S' fS fX hf φ) :
    ψ = φ :=
  Thickening.Hom.ext h₁ h₂

/-- **A morphism out of a rebased object from its two plain components.** -/
def rebasedMk (σ : A.thickening.source ⟶ C.thickening.source)
    (τ : A.thickening.target ⟶ C.thickening.target)
    (himm : A.thickening.immersion ≫ τ.hom = σ ≫ C.thickening.immersion)
    (hbase : τ ≫ C.toBase = A.toBase ≫ fS) (hX : σ ≫ C.toX = A.toX ≫ fX) :
    (changeBase S S' fS fX hf).obj A ⟶ C where
  sourceHom := σ
  targetHom := τ
  immersion_naturality := himm
  base_naturality := hbase
  toX_naturality := hX

/-- The map of thickened schemes of `rebasedMk` is the given map `σ`. -/
@[simp]
theorem rebasedSourceHom_rebasedMk (σ : A.thickening.source ⟶ C.thickening.source)
    (τ : A.thickening.target ⟶ C.thickening.target)
    (himm : A.thickening.immersion ≫ τ.hom = σ ≫ C.thickening.immersion)
    (hbase : τ ≫ C.toBase = A.toBase ≫ fS) (hX : σ ≫ C.toX = A.toX ≫ fX) :
    rebasedSourceHom S S' fS fX hf (rebasedMk S S' fS fX hf σ τ himm hbase hX) = σ :=
  rfl

/-- The map of ambient schemes of `rebasedMk` is the given map `τ`. -/
@[simp]
theorem rebasedTargetHom_rebasedMk (σ : A.thickening.source ⟶ C.thickening.source)
    (τ : A.thickening.target ⟶ C.thickening.target)
    (himm : A.thickening.immersion ≫ τ.hom = σ ≫ C.thickening.immersion)
    (hbase : τ ≫ C.toBase = A.toBase ≫ fS) (hX : σ ≫ C.toX = A.toX ≫ fX) :
    rebasedTargetHom S S' fS fX hf (rebasedMk S S' fS fX hf σ τ himm hbase hX) = τ :=
  rfl

/-- The map of thickened schemes of the composite of `f_CRIS(k)` with `ψ` is the composite of those
of `k` and `ψ`. -/
@[simp]
theorem rebasedSourceHom_comp {A₀ : Thickening S} (k : A₀ ⟶ A)
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ C) :
    rebasedSourceHom S S' fS fX hf ((changeBase S S' fS fX hf).map k ≫ ψ) =
      k.sourceHom ≫ rebasedSourceHom S S' fS fX hf ψ :=
  rfl

/-- The map of ambient schemes of the composite of `f_CRIS(k)` with `ψ` is the composite of those
of `k` and `ψ`. -/
@[simp]
theorem rebasedTargetHom_comp {A₀ : Thickening S} (k : A₀ ⟶ A)
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ C) :
    rebasedTargetHom S S' fS fX hf ((changeBase S S' fS fX hf).map k ≫ ψ) =
      k.targetHom ≫ rebasedTargetHom S S' fS fX hf ψ :=
  rfl

end Rebased

/-! ### Factorizations through the small site, over an object of the small site of the target -/

/-- **A factorization of `ψ : f_CRIS(A) ⟶ D` through an object of `Cris(X/S)`.**  It asks for an
object `B` of the small crystalline site of `X/S`, a morphism `A ⟶ B` of `CRIS(X/S)`, and a
morphism `f_CRIS(B) ⟶ D` of `CRIS(X'/S')` whose composite is `ψ`. -/
def IsDominatedOver (D : CrystallineThickening S') (A : Thickening S)
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D) : Prop :=
  ∃ (B : CrystallineThickening S) (m : A ⟶ (ι S).obj B)
    (h : (changeBase S S' fS fX hf).obj ((ι S).obj B) ⟶ (ι S').obj D),
    (changeBase S S' fS fX hf).map m ≫ h = ψ

/-- **The sieve of refinements of `A` over which `ψ` factors through the small site.**  It is a
sieve because a morphism to a refinement over which `ψ` factors gives, after composition, a
factorization over the source. -/
def dominationOverSieve (D : CrystallineThickening S') (A : Thickening S)
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D) : Sieve A where
  arrows _ g := IsDominatedOver S S' fS fX hf D _ ((changeBase S S' fS fX hf).map g ≫ ψ)
  downward_closed := fun {_ _ _} hg k ↦ by
    obtain ⟨B, m, h, hmh⟩ := hg
    refine ⟨B, k ≫ m, h, ?_⟩
    rw [Functor.map_comp, Category.assoc, hmh, Functor.map_comp, Category.assoc]

/-! ### The three properties of the pushout object -/

section Pushout

variable (D : CrystallineThickening S') (A : Thickening S) (V : S.X.Opens)
  (lift : A.thickening.source ⟶ (V : Scheme.{u})) [IsAffineHom lift]
  (hlift : lift ≫ V.ι = A.toX)

/-- **The pushout object dominates `A` over `D`.**  On thickened schemes the morphism down to `D`
is the lift of `V ⟶ X ⟶ X'` through the open immersion `U_D ⟶ X'`, which exists because `V` lies
inside `f^{-1}(U_D)`; on ambient schemes it is the morphism out of the pushout whose legs are the
ambient part of `ψ` and the immersion of `D`. -/
theorem exists_domination_of_affine
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D)
    (hV : Set.range (V.ι ≫ fX).base ⊆ Set.range ((ι S').obj D).toX.base) :
    ∃ h : (changeBase S S' fS fX hf).obj
        ((ι S).obj (crystallinePushout S A V lift hlift)) ⟶ (ι S').obj D,
      (changeBase S S' fS fX hf).map (crystallinePushoutHom S A V lift hlift) ≫ h = ψ := by
  have : IsOpenImmersion ((ι S').obj D).toX := D.property
  have hrange : Set.range (V.ι ≫ fX).base ⊆ Set.range ((ι S').obj D).toX.base := hV
  have hsfac : IsOpenImmersion.lift ((ι S').obj D).toX (V.ι ≫ fX) hrange ≫
      ((ι S').obj D).toX = V.ι ≫ fX :=
    IsOpenImmersion.lift_fac _ _ _
  have hlifts : lift ≫ IsOpenImmersion.lift ((ι S').obj D).toX (V.ι ≫ fX) hrange =
      rebasedSourceHom S S' fS fX hf ψ := by
    refine (cancel_mono ((ι S').obj D).toX).mp ?_
    rw [rebasedSourceHom_comp_toX, Category.assoc, hsfac, ← Category.assoc, hlift]
  have hw : A.thickening.immersion ≫ (rebasedTargetHom S S' fS fX hf ψ).hom =
      lift ≫ IsOpenImmersion.lift ((ι S').obj D).toX (V.ι ≫ fX) hrange ≫
        ((ι S').obj D).thickening.immersion := by
    rw [rebased_immersion_naturality, ← hlifts, Category.assoc]
  have hbase : pushoutDescThickening A.thickening lift ((ι S').obj D).thickening
        (rebasedTargetHom S S' fS fX hf ψ)
        (IsOpenImmersion.lift ((ι S').obj D).toX (V.ι ≫ fX) hrange) hw ≫
          ((ι S').obj D).toBase =
      (crystallinePushout S A V lift hlift).obj.toBase ≫ fS := by
    refine crystallinePushout_dividedPowerHom_ext S A V lift hlift ?_ ?_
    · rw [← Category.assoc, crystallinePushoutHom_targetHom_comp_pushoutDescThickening,
        rebasedTargetHom_comp_toBase, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ fS)
        (crystallinePushoutHom S A V lift hlift).base_naturality.symm
    · rw [DividedPowerScheme.Hom.comp_hom, DividedPowerScheme.Hom.comp_hom, ← Category.assoc,
        ← Category.assoc, crystallinePushout_immersion_comp_pushoutDescThickening,
        (crystallinePushout S A V lift hlift).obj.over_base, Category.assoc,
        ((ι S').obj D).over_base, ← Category.assoc, hsfac, Category.assoc,
        ← sourceToBase_comp_base S S' fS fX hf, crystallinePushout_toX]
      simp only [sourceToBase, Category.assoc]
  refine ⟨rebasedMk S S' fS fX hf
    (IsOpenImmersion.lift ((ι S').obj D).toX (V.ι ≫ fX) hrange)
    (pushoutDescThickening A.thickening lift ((ι S').obj D).thickening
      (rebasedTargetHom S S' fS fX hf ψ)
      (IsOpenImmersion.lift ((ι S').obj D).toX (V.ι ≫ fX) hrange) hw)
    (crystallinePushout_immersion_comp_pushoutDescThickening S A V lift hlift _ _ _ hw)
      hbase hsfac, ?_⟩
  refine rebased_ext S S' fS fX hf ?_ ?_
  · rw [rebasedSourceHom_comp, rebasedSourceHom_rebasedMk, crystallinePushoutHom_sourceHom,
      hlifts]
  · rw [rebasedTargetHom_comp, rebasedTargetHom_rebasedMk]
    exact crystallinePushoutHom_targetHom_comp_pushoutDescThickening S A V lift hlift _ _ _ hw

/-- **A morphism from a pushout object down to `D` is determined by its composite with the
morphism from `A`.**  On thickened schemes both are the lift of `V ⟶ X ⟶ X'` through the open
immersion `U_D ⟶ X'`, which is a monomorphism; on ambient schemes the two legs of the pushout
square are prescribed — one by the hypothesis, the other by compatibility with the immersions —
so `pushout.hom_ext` applies.

This is the step the cofilteredness of the dominations with no target does not give, and the
reason the common refinement of `commonRefinementSieve_mem` has to be a pushout. -/
theorem domination_unique
    (p q : (changeBase S S' fS fX hf).obj
      ((ι S).obj (crystallinePushout S A V lift hlift)) ⟶ (ι S').obj D)
    (hpq : (changeBase S S' fS fX hf).map (crystallinePushoutHom S A V lift hlift) ≫ p =
      (changeBase S S' fS fX hf).map (crystallinePushoutHom S A V lift hlift) ≫ q) :
    p = q := by
  have : IsOpenImmersion ((ι S').obj D).toX := D.property
  have hsource : rebasedSourceHom S S' fS fX hf p = rebasedSourceHom S S' fS fX hf q :=
    (cancel_mono ((ι S').obj D).toX).mp
      ((rebasedSourceHom_comp_toX S S' fS fX hf p).trans
        (rebasedSourceHom_comp_toX S S' fS fX hf q).symm)
  have hinl : (crystallinePushoutHom S A V lift hlift).targetHom ≫
        rebasedTargetHom S S' fS fX hf p =
      (crystallinePushoutHom S A V lift hlift).targetHom ≫ rebasedTargetHom S S' fS fX hf q :=
    congrArg (rebasedTargetHom S S' fS fX hf) hpq
  refine rebased_ext S S' fS fX hf hsource
    (crystallinePushout_dividedPowerHom_ext S A V lift hlift hinl ?_)
  rw [rebased_immersion_naturality, rebased_immersion_naturality, hsource]

/-- **The pushout object maps to any object of `Cris(X/S)` under `A` whose open of `X` contains
the chosen one.**  On thickened schemes the map is the lift of `V ↪ X` through the open immersion
`U_B ⟶ X`; on ambient schemes it is the morphism out of the pushout whose legs are the ambient
part of the given morphism and that lift followed by the immersion of `B`. -/
theorem exists_hom_of_range_le (B : CrystallineThickening S) (m : A ⟶ (ι S).obj B)
    (hVB : Set.range V.ι.base ⊆ Set.range ((ι S).obj B).toX.base) :
    ∃ a : crystallinePushout S A V lift hlift ⟶ B,
      crystallinePushoutHom S A V lift hlift ≫ (ι S).map a = m := by
  have : IsOpenImmersion ((ι S).obj B).toX := B.property
  have hrange : Set.range V.ι.base ⊆ Set.range ((ι S).obj B).toX.base := hVB
  have hsfac : IsOpenImmersion.lift ((ι S).obj B).toX V.ι hrange ≫ ((ι S).obj B).toX = V.ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hlifts : lift ≫ IsOpenImmersion.lift ((ι S).obj B).toX V.ι hrange = m.sourceHom := by
    refine (cancel_mono ((ι S).obj B).toX).mp ?_
    rw [m.toX_naturality, Category.assoc, hsfac, hlift]
  have hw : A.thickening.immersion ≫ m.targetHom.hom =
      lift ≫ IsOpenImmersion.lift ((ι S).obj B).toX V.ι hrange ≫
        ((ι S).obj B).thickening.immersion := by
    rw [m.immersion_naturality, ← hlifts, Category.assoc]
  have hbase : pushoutDescThickening A.thickening lift ((ι S).obj B).thickening m.targetHom
        (IsOpenImmersion.lift ((ι S).obj B).toX V.ι hrange) hw ≫ ((ι S).obj B).toBase =
      (crystallinePushout S A V lift hlift).obj.toBase := by
    refine crystallinePushout_dividedPowerHom_ext S A V lift hlift ?_ ?_
    · rw [← Category.assoc, crystallinePushoutHom_targetHom_comp_pushoutDescThickening,
        m.base_naturality]
      exact (crystallinePushoutHom S A V lift hlift).base_naturality.symm
    · rw [DividedPowerScheme.Hom.comp_hom, ← Category.assoc,
        crystallinePushout_immersion_comp_pushoutDescThickening,
        (crystallinePushout S A V lift hlift).obj.over_base, Category.assoc,
        ((ι S).obj B).over_base, ← Category.assoc, hsfac, crystallinePushout_toX]
  refine ⟨ObjectProperty.homMk
    { sourceHom := IsOpenImmersion.lift ((ι S).obj B).toX V.ι hrange
      targetHom := pushoutDescThickening A.thickening lift ((ι S).obj B).thickening m.targetHom
        (IsOpenImmersion.lift ((ι S).obj B).toX V.ι hrange) hw
      immersion_naturality :=
        crystallinePushout_immersion_comp_pushoutDescThickening S A V lift hlift _ _ _ hw
      base_naturality := hbase
      toX_naturality := hsfac }, ?_⟩
  refine Thickening.Hom.ext hlifts ?_
  exact crystallinePushoutHom_targetHom_comp_pushoutDescThickening S A V lift hlift _ _ _ hw

end Pushout

/-! ### The sieve of refinements admitting a common refinement of two dominations -/

/-- **The sieve of refinements of `A` over which two given dominations over `D` are refined by a
common one.**  A morphism `g : A'' ⟶ A` belongs to it when there is an object `B` of `Cris(X/S)`
under `A''` mapping to both `B₁` and `B₂` compatibly with the two given dominations, and such that
the two morphisms `f_CRIS(B) ⟶ D` obtained from `h₁` and from `h₂` agree.

It is a sieve because the refining object, the two morphisms to `B₁` and `B₂` and the equality of
the two morphisms to `D` do not depend on `g`. -/
def commonRefinementSieve (D : CrystallineThickening S') (A : Thickening S)
    (B₁ B₂ : CrystallineThickening S)
    (m₁ : A ⟶ (ι S).obj B₁)
    (h₁ : (changeBase S S' fS fX hf).obj ((ι S).obj B₁) ⟶ (ι S').obj D)
    (m₂ : A ⟶ (ι S).obj B₂)
    (h₂ : (changeBase S S' fS fX hf).obj ((ι S).obj B₂) ⟶ (ι S').obj D) : Sieve A where
  arrows _ g := ∃ (B : CrystallineThickening S) (m : _ ⟶ (ι S).obj B) (a₁ : B ⟶ B₁)
      (a₂ : B ⟶ B₂),
    m ≫ (ι S).map a₁ = g ≫ m₁ ∧ m ≫ (ι S).map a₂ = g ≫ m₂ ∧
      (changeBase S S' fS fX hf).map ((ι S).map a₁) ≫ h₁ =
        (changeBase S S' fS fX hf).map ((ι S).map a₂) ≫ h₂
  downward_closed := fun {_ _ _} hg k ↦ by
    obtain ⟨B, m, a₁, a₂, e₁, e₂, e₃⟩ := hg
    refine ⟨B, k ≫ m, a₁, a₂, ?_, ?_, e₃⟩
    · rw [Category.assoc, e₁, Category.assoc]
    · rw [Category.assoc, e₂, Category.assoc]

/-! ### The two covering statements -/

section Covering

variable (D : CrystallineThickening S') (A : Thickening S)

/-- **The open of `X` over which the dominating objects are chosen**: the preimage under `f` of
the open image in `X'` of the thickened scheme of `D`.  The structure map of `A` lands in it, as
soon as `A` has a morphism to `D` after change of base. -/
private theorem mem_preimage_opensRange
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D)
    [IsOpenImmersion ((ι S').obj D).toX] (z : A.thickening.source) :
    A.toX.base z ∈ fX ⁻¹ᵁ ((ι S').obj D).toX.opensRange :=
  ⟨(rebasedSourceHom S S' fS fX hf ψ).base z,
    congrArg (fun k : A.thickening.source ⟶ S'.X ↦ k.base z)
      (rebasedSourceHom_comp_toX S S' fS fX hf ψ)⟩

/-- **The covering step.**  Let `A` be an object of `CRIS(X/S)` with a morphism
`ψ : f_CRIS(A) ⟶ D` to an object of the small site of the target.  Then the refinements of `A`
over which `ψ` factors through an object of `Cris(X/S)` form a covering sieve.

Cover the ambient scheme of `A` by the affine opens `W` of
`Crystalline.GlobalCrystallineSituation.Thickening.exists_affine_neighbourhood_toX_of_mem`, taken
inside the open `f^{-1}(U_D)` of `X` the structure map of `A` lands in, so that the part of `U` in
`W` maps affinely into an affine open `V ⊆ f^{-1}(U_D)`.  The pushout of [Stacks, Tag 07RT] along
that affine map is an object of `Cris(X/S)` lying over `V`, and `exists_domination_of_affine`
factors `ψ` through it. -/
theorem dominationOverSieve_mem
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D) :
    dominationOverSieve S S' fS fX hf D A ψ ∈ topology S A := by
  have : IsOpenImmersion ((ι S').obj D).toX := D.property
  refine mem_topology_of_affine_pieces S A (fX ⁻¹ᵁ ((ι S').obj D).toX.opensRange)
    (mem_preimage_opensRange S S' fS fX hf D A ψ) _ fun W V hVU hrange _ _ ↦ ?_
  have hV : Set.range ((V.ι ≫ fX)).base ⊆ Set.range (((ι S').obj D).toX).base := by
    rintro _ ⟨z, rfl⟩
    exact hVU z.property
  obtain ⟨h, hmh⟩ := exists_domination_of_affine S S' fS fX hf D (A.restrictOpen W) V
    (IsOpenImmersion.lift V.ι (A.restrictOpen W).toX hrange) (IsOpenImmersion.lift_fac _ _ _)
    ((changeBase S S' fS fX hf).map (A.restrictOpenHom W) ≫ ψ) hV
  exact ⟨crystallinePushout S (A.restrictOpen W) V _ (IsOpenImmersion.lift_fac _ _ _),
    crystallinePushoutHom S (A.restrictOpen W) V _ (IsOpenImmersion.lift_fac _ _ _), h, hmh⟩

/-- **The independence step.**  Two factorizations of `ψ : f_CRIS(A) ⟶ D` through objects of
`Cris(X/S)` are refined by a common one after a covering of `A`, compatibly with the two
morphisms down to `D`.

The covering is the one of `dominationOverSieve_mem`, with the affine open `V` of `X` chosen
inside the open images of the thickened schemes of `B₁` and of `B₂` as well as inside
`f^{-1}(U_D)`; then `exists_hom_of_range_le` maps the pushout object to `B₁` and to `B₂`
compatibly with the two given morphisms, and `domination_unique` identifies the two resulting
morphisms down to `D`, both composites with the morphism from the piece of `A` being the
restriction of `ψ`. -/
theorem commonRefinementSieve_mem
    (ψ : (changeBase S S' fS fX hf).obj A ⟶ (ι S').obj D)
    (B₁ B₂ : CrystallineThickening S)
    (m₁ : A ⟶ (ι S).obj B₁)
    (h₁ : (changeBase S S' fS fX hf).obj ((ι S).obj B₁) ⟶ (ι S').obj D)
    (hmh₁ : (changeBase S S' fS fX hf).map m₁ ≫ h₁ = ψ)
    (m₂ : A ⟶ (ι S).obj B₂)
    (h₂ : (changeBase S S' fS fX hf).obj ((ι S).obj B₂) ⟶ (ι S').obj D)
    (hmh₂ : (changeBase S S' fS fX hf).map m₂ ≫ h₂ = ψ) :
    commonRefinementSieve S S' fS fX hf D A B₁ B₂ m₁ h₁ m₂ h₂ ∈ topology S A := by
  have : IsOpenImmersion ((ι S').obj D).toX := D.property
  have : IsOpenImmersion ((ι S).obj B₁).toX := B₁.property
  have : IsOpenImmersion ((ι S).obj B₂).toX := B₂.property
  have hmem : ∀ z : A.thickening.source, A.toX.base z ∈
      (fX ⁻¹ᵁ ((ι S').obj D).toX.opensRange) ⊓ ((ι S).obj B₁).toX.opensRange ⊓
        ((ι S).obj B₂).toX.opensRange := by
    intro z
    refine ⟨⟨mem_preimage_opensRange S S' fS fX hf D A ψ z, ?_⟩, ?_⟩
    · exact ⟨m₁.sourceHom.base z,
        congrArg (fun k : A.thickening.source ⟶ S.X ↦ k.base z) m₁.toX_naturality⟩
    · exact ⟨m₂.sourceHom.base z,
        congrArg (fun k : A.thickening.source ⟶ S.X ↦ k.base z) m₂.toX_naturality⟩
  refine mem_topology_of_affine_pieces S A _ hmem _ fun W V hVU hrange _ _ ↦ ?_
  have hV₁ : Set.range V.ι.base ⊆ Set.range (((ι S).obj B₁).toX).base := by
    rintro _ ⟨z, rfl⟩
    exact (hVU z.property).1.2
  have hV₂ : Set.range V.ι.base ⊆ Set.range (((ι S).obj B₂).toX).base := by
    rintro _ ⟨z, rfl⟩
    exact (hVU z.property).2
  obtain ⟨a₁, ha₁⟩ := exists_hom_of_range_le S S' fS fX hf (A.restrictOpen W) V
    (IsOpenImmersion.lift V.ι (A.restrictOpen W).toX hrange) (IsOpenImmersion.lift_fac _ _ _) B₁
    (A.restrictOpenHom W ≫ m₁) hV₁
  obtain ⟨a₂, ha₂⟩ := exists_hom_of_range_le S S' fS fX hf (A.restrictOpen W) V
    (IsOpenImmersion.lift V.ι (A.restrictOpen W).toX hrange) (IsOpenImmersion.lift_fac _ _ _) B₂
    (A.restrictOpenHom W ≫ m₂) hV₂
  refine ⟨crystallinePushout S (A.restrictOpen W) V _ (IsOpenImmersion.lift_fac _ _ _),
    crystallinePushoutHom S (A.restrictOpen W) V _ (IsOpenImmersion.lift_fac _ _ _),
    a₁, a₂, ha₁, ha₂, ?_⟩
  refine domination_unique S S' fS fX hf D (A.restrictOpen W) V _
    (IsOpenImmersion.lift_fac _ _ _) _ _ ?_
  rw [← Category.assoc, ← Functor.map_comp, ha₁, ← Category.assoc, ← Functor.map_comp, ha₂,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hmh₁, hmh₂]

end Covering

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
