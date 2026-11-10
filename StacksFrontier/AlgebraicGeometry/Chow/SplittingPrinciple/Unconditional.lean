module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIso
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundle
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelRank
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral

/-!
# The splitting principle in Chow homology

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ_i`, `i ∈ I` finite, be finite locally free `𝒪_X`-modules of
ranks `r_i`. Stacks 02UL asserts that there is a projective flat morphism `π : P ⟶ X` of relative
dimension `d` such that

1. for every morphism `f : Y ⟶ X` the flat pullback `π_Y^* : A_*(Y) ⟶ A_{*+d}(Y ×_X P)` along
   the base change `π_Y : Y ×_X P ⟶ Y` is injective, and
2. each `π^*ℰ_i` has a filtration whose successive quotients are invertible `𝒪_P`-modules.

The morphism is the iterated projective bundle. One layer of it is the projective bundle
`π : 𝐏(ℰ) ⟶ X` of a module of rank `m + 1`, together with the facts the iteration uses about it:
`π` is flat, proper and of relative dimension `m` (Stacks 02TX), flat pullback along it descends
to Chow groups (Stacks 02S1), the projective space bundle map is injective (Stacks 02TX), and the
tautological sequence `0 ⟶ 𝒦 ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` is short exact with `𝒦` locally free of rank
`m`. All of these are theorems about `Stacks.Chow.bundle`, and
`Stacks.Chow.BundleStep.ofProjectiveBundle` assembles them into the datum
`Stacks.Chow.BundleStep` that the iteration consumes.

Clause (1) for an arbitrary base change is proved by carrying through the iteration the property
`Stacks.Chow.UniversallyInjectiveFlatPullback`: flat pullback along every base change of the
morphism is injective. For one layer this holds because the base change of `𝐏(ℰ)` along
`f : Y ⟶ X` is `𝐏(f^*ℰ)` (Stacks 01O3, `Stacks.Chow.GenuineChern.bundleBaseChangeHolds`), along
whose projection flat pullback is injective by the top half of Stacks 02TW; and the property
passes to composites by pasting cartesian squares and Stacks 02RD.

## Main definitions

* `Stacks.Chow.BundleStep.ofProjectiveBundle` — the projective bundle of a finite locally free
  module of rank `m + 1`, as a layer of the splitting tower.
* `Stacks.Chow.UniversallyInjectiveFlatPullback` — flat pullback along every base change of a
  flat morphism of relative dimension `d` is injective on Chow groups.

## Main results

* `Stacks.Chow.injective_flatPullbackChow_comp` — flat pullback along a composite of two flat
  morphisms with injective pullbacks is injective.
* `Stacks.Chow.universallyInjectiveFlatPullback_bundleProj` — the projection of a projective
  bundle has universally injective flat pullback.
* `Stacks.Chow.UniversallyInjectiveFlatPullback.comp` — the property is stable under
  composition.
* `Stacks.Chow.exists_splittingMorphism_universal` — **Stacks 02UL**, both clauses, clause (1)
  in the source's form `π_Y : Y ×_X P ⟶ Y`.

## Implementation notes

The source asks for `π` *projective*. What is delivered is a flat *proper* morphism: each layer is
the projective bundle of a finite locally free module, which is proper by Stacks 0800, but the
base case of the induction is the identity of `X`, and no lemma here makes the identity, or a
composite of projective bundles, H-projective. Properness is what the applications of the
splitting principle in chapter 42 use.

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The projective bundle as a layer of the tower -/

/-- **The projective bundle `π : 𝐏(ℰ) ⟶ X` of a finite locally free module of rank `m + 1`, as a
layer of the splitting tower.** Every field is a theorem about `Stacks.Chow.bundle`: flatness,
local finite type and relative dimension `m` are Stacks 02TX
(`Stacks.Chow.flat_bundleProj`, `Stacks.Chow.relativeDimension_bundleProj`), properness is Stacks
0800, the descent of flat pullback is Stacks 02S1
(`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`), the cap operator is
`c₁(𝒪(1)) ∩ -`, the injectivity of the projective space bundle map is Stacks 02TX
(`Stacks.Chow.projectiveBundleRelationInjective_bundle`), and the tautological sequence is the
kernel sequence of the tautological surjection `π^*ℰ ⟶ 𝒪(1)`, whose kernel is finite locally
free of rank `(m + 1) - 1 = m`. -/
@[ega "IV 19.4.11" "(ii), special case"]
def BundleStep.ofProjectiveBundle (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)) :
    BundleStep C sX E m :=
  letI := hE
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (m + 1)
  letI := flat_bundleProj E m
  letI := locallyOfFiniteType_bundleProj E m
  letI : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let τ : (Scheme.Modules.pullback (bundleProj E)).obj E ⟶ bundleTwist E :=
    Stacks.ProjectiveBundleSplitting.tautologicalMap E (bundlePieces E)
  haveI hτ : Epi τ := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E (bundlePieces E)
  { P := bundle E
    sP := bundleProj E ≫ sX
    π := bundleProj E
    hsP := rfl
    relDim := relativeDimension_bundleProj E m
    hfac := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k
    twist := bundleTwistCap E C sX
    hinj := projectiveBundleRelationInjective_bundle E m C sX
    twistModule := bundleTwist E
    twistModule_isInvertible := isInvertible_bundleTwist E
    sub := kernel τ
    incl := kernel.ι τ
    quot := τ
    incl_comp_quot := kernel.condition τ
    shortExact := { exact := ShortComplex.exact_kernel τ }
    sub_rank := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi τ hτ
      (m + 1) 1 (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (m + 1))
      (Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _
        (isInvertible_bundleTwist E)) }

/-- The projection of the layer `Stacks.Chow.BundleStep.ofProjectiveBundle` is the projection of
the projective bundle. -/
@[simp]
theorem BundleStep.ofProjectiveBundle_π (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)) :
    (BundleStep.ofProjectiveBundle C sX E m hE).π =
      letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
        (m + 1)
      bundleProj E :=
  rfl

/-! ### Injectivity of flat pullback along composites and isomorphisms -/

section Injectivity

variable (C : ChowSituation.{u})

/-- **Flat pullback along a composite of flat morphisms with injective pullbacks is injective.**
If `q = f ≫ g` with `f` flat of relative dimension `r` and `g` flat of relative dimension `s`,
and `f^*` is injective in degree `k + s` and `g^*` in degree `k`, then `q^*` is injective in
degree `k`: by Stacks 02RD, `q^* = f^* ∘ g^*`. -/
theorem injective_flatPullbackChow_comp {A B Z : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (f : A ⟶ B) [LocallyOfFiniteType f] [Flat f] (g : B ⟶ Z)
    [LocallyOfFiniteType g] [Flat g] (q : A ⟶ Z) [LocallyOfFiniteType q] [Flat q]
    (hfg : f ≫ g = q) (hfbase : f ≫ sB = sA) (hgbase : g ≫ sZ = sB) (hq : q ≫ sZ = sA)
    (r s d : ℕ) (hd : r + s = d) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (hqd : AlgebraicGeometry.RelativeDimension q d)
    (k : ℤ)
    (hinjf : Function.Injective (flatPullbackChow C sA sB f hfbase r hf (k + (s : ℤ))
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)))
    (hinjg : Function.Injective (flatPullbackChow C sB sZ g hgbase s hg k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _))) :
    Function.Injective (flatPullbackChow C sA sZ q hq d hqd k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)) := by
  subst hd
  intro x y hxy
  have key : ∀ α : chowGroup C sZ k,
      flatPullbackChow C sA sB f hfbase r hf (k + (s : ℤ))
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
          (flatPullbackChow C sB sZ g hgbase s hg k
            (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) α) ≍
        flatPullbackChow C sA sZ q hq (r + s) hqd k
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) α := fun α ↦
    (flatPullbackChow_comp C sA sB sZ f g hfbase hgbase r s hf hg k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) α).trans
      (flatPullbackChow_heq_congr C sA sZ (f ≫ g) q _ hq hfg rfl _ hqd rfl _ _ α α HEq.rfl)
  exact hinjg (hinjf (eq_of_heq ((key x).trans ((heq_of_eq hxy).trans (key y).symm))))

/-- **Injectivity of flat pullback is invariant under an isomorphism over the target.** If
`q = e ≫ q'` with `e` an isomorphism and `q'^*` injective, then `q^*` is injective: `e^*` is
bijective (`Stacks.Chow.flatPullbackChow_bijective_of_isIso`) and Stacks 02RD composes the
two. -/
theorem injective_flatPullbackChow_of_isIso_comp {P P' T : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (sP' : P' ⟶ C.S) [LocallyOfFiniteType sP'] (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (q : P ⟶ T) [LocallyOfFiniteType q] [Flat q] (q' : P' ⟶ T)
    [LocallyOfFiniteType q'] [Flat q'] (e : P ⟶ P') [IsIso e] (he : e ≫ q' = q)
    (hq : q ≫ sT = sP) (hq' : q' ≫ sT = sP') (r : ℕ)
    (hqr : AlgebraicGeometry.RelativeDimension q r)
    (hq'r : AlgebraicGeometry.RelativeDimension q' r) (k : ℤ)
    (hinj : Function.Injective (flatPullbackChow C sP' sT q' hq' r hq'r k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _))) :
    Function.Injective (flatPullbackChow C sP sT q hq r hqr k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)) := by
  have heb : e ≫ sP' = sP := by rw [← hq', ← Category.assoc, he, hq]
  have he0 : AlgebraicGeometry.RelativeDimension e 0 := relativeDimension_of_isIso e
  exact injective_flatPullbackChow_comp C sP sP' sT e q' q he heb hq' hq 0 r r (zero_add r) he0
    hq'r hqr k (flatPullbackChow_bijective_of_isIso C sP sP' e heb he0 _ _).injective hinj

end Injectivity

/-! ### Universally injective flat pullback -/

/-- **Flat pullback along every base change of `π` is injective.** For a morphism `π : P ⟶ X`
and `d : ℕ`: for every cartesian square
```
Q ──g──▶ P
│        │
p        π
▼        ▼
Y ──f──▶ X
```
with `Y` and `Q` locally of finite type over the base and `p` flat, locally of finite type and of
relative dimension `d`, the flat pullback `p^* : A_k(Y) ⟶ A_{k+d}(Q)` is injective in every
degree. This is the form of clause (1) of Stacks 02UL that survives composition. The
hypotheses on `p` follow from the same ones on `π` by Stacks 02NK; they are binders so that the
property is stated for every structure morphism and every proof of them. -/
def UniversallyInjectiveFlatPullback (C : ChowSituation.{u}) {P X : Scheme.{u}} (π : P ⟶ X)
    (d : ℕ) : Prop :=
  ∀ ⦃Y Q : Scheme.{u}⦄ (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sQ : Q ⟶ C.S)
    [LocallyOfFiniteType sQ] (f : Y ⟶ X) (p : Q ⟶ Y) [LocallyOfFiniteType p] [Flat p]
    (g : Q ⟶ P), IsPullback g p π f → ∀ (hsQ : p ≫ sY = sQ)
    (hp : AlgebraicGeometry.RelativeDimension p d) (k : ℤ),
    Function.Injective (flatPullbackChow C sQ sY p hsQ d hp k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _))

namespace UniversallyInjectiveFlatPullback

variable {C : ChowSituation.{u}}

/-- The identity has universally injective flat pullback: in a cartesian square over `𝟙 X` the
left leg is an isomorphism. -/
theorem id (X : Scheme.{u}) : UniversallyInjectiveFlatPullback C (𝟙 X) 0 := by
  intro Y Q sY _ sQ _ f p _ _ g h hsQ hp k
  have hw : p ≫ f = g := by simpa using h.w.symm
  have : IsIso p := ⟨⟨h.lift f (𝟙 Y) (by simp),
    h.hom_ext (by rw [Category.assoc, h.lift_fst, Category.id_comp, hw])
      (by rw [Category.assoc, h.lift_snd, Category.comp_id, Category.id_comp]),
    h.lift_snd _ _ _⟩⟩
  exact (flatPullbackChow_bijective_of_isIso C sQ sY p hsQ hp k _).injective

/-- **Universally injective flat pullback is stable under composition.** If `π₁ : P ⟶ Q` and
`π₂ : Q ⟶ X` are locally of finite type of relative dimensions `n` and `m` and have universally
injective flat pullback, so does `π₁ ≫ π₂`, in relative dimension `n + m`. A cartesian square over
`π₁ ≫ π₂` is the vertical composite of one over `π₂` and one over `π₁`, and the flat pullback
along the composite of the two left legs is injective by
`Stacks.Chow.injective_flatPullbackChow_comp`. -/
theorem comp {P Q X : Scheme.{u}} (π₁ : P ⟶ Q) (π₂ : Q ⟶ X) [LocallyOfFiniteType π₁]
    [Flat π₁] [LocallyOfFiniteType π₂] [Flat π₂] {n m : ℕ}
    (hπ₁ : AlgebraicGeometry.RelativeDimension π₁ n)
    (hπ₂ : AlgebraicGeometry.RelativeDimension π₂ m)
    (h₁ : UniversallyInjectiveFlatPullback C π₁ n)
    (h₂ : UniversallyInjectiveFlatPullback C π₂ m) :
    UniversallyInjectiveFlatPullback C (π₁ ≫ π₂) (n + m) := by
  intro Y W sY _ sW _ f p _ _ g h hsW hp k
  -- the cartesian square over `π₂`
  have hb : IsPullback (pullback.snd f π₂) (pullback.fst f π₂) π₂ f :=
    (IsPullback.of_hasPullback f π₂).flip
  set l : W ⟶ pullback f π₂ := hb.lift (g ≫ π₁) p (by rw [Category.assoc, h.w])
  have hl₁ : l ≫ pullback.snd f π₂ = g ≫ π₁ := hb.lift_fst _ _ _
  have hl₂ : l ≫ pullback.fst f π₂ = p := hb.lift_snd _ _ _
  -- the cartesian square over `π₁`
  have ht : IsPullback g l π₁ (pullback.snd f π₂) :=
    IsPullback.of_bot (by rw [hl₂]; exact h) hl₁.symm hb
  have : LocallyOfFiniteType l := MorphismProperty.of_isPullback ht inferInstance
  have : Flat l := MorphismProperty.of_isPullback ht inferInstance
  have hl : AlgebraicGeometry.RelativeDimension l n :=
    AlgebraicGeometry.RelativeDimension.of_isPullback ht hπ₁
  have hp₁ : AlgebraicGeometry.RelativeDimension (pullback.fst f π₂) m :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hb hπ₂
  have hsW' : l ≫ pullback.fst f π₂ ≫ sY = sW := by rw [← Category.assoc, hl₂, hsW]
  exact injective_flatPullbackChow_comp C sW (pullback.fst f π₂ ≫ sY) sY l
    (pullback.fst f π₂) p hl₂ hsW' rfl hsW n m (n + m) rfl hl hp₁ hp k
    (h₁ (pullback.fst f π₂ ≫ sY) sW (pullback.snd f π₂) l g ht hsW' hl (k + (m : ℤ)))
    (h₂ sY (pullback.fst f π₂ ≫ sY) f (pullback.fst f π₂) (pullback.snd f π₂) hb rfl hp₁ k)

end UniversallyInjectiveFlatPullback

/-- **The projection of a projective bundle has universally injective flat pullback.** For `ℰ`
finite locally free of rank `m + 1` on `X` and a cartesian square with `p : Q ⟶ Y` the base
change of `π : 𝐏(ℰ) ⟶ X` along `f : Y ⟶ X`, the scheme `Q` is `𝐏(f^*ℰ)` over `Y` (Stacks 01O3,
`Stacks.Chow.GenuineChern.bundleBaseChangeHolds`), and flat pullback along the projection of
`𝐏(f^*ℰ)` is injective by the top half of Stacks 02TW
(`Stacks.Chow.GenuineChern.pullback_injective`). -/
theorem universallyInjectiveFlatPullback_bundleProj (C : ChowSituation.{u}) {X : Scheme.{u}}
    (E : X.Modules) (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)] :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (m + 1)
    UniversallyInjectiveFlatPullback C (bundleProj E) m := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (m + 1)
  intro Y Q sY _ sQ _ f p _ _ g h hsQ hp k
  set E' := (Scheme.Modules.pullback f).obj E
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (m + 1) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f E (m + 1)
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E'
    (m + 1)
  have := flat_bundleProj E' m
  have := locallyOfFiniteType_bundleProj E' m
  obtain ⟨e, he, -⟩ := GenuineChern.bundleBaseChangeHolds f E E' (Iso.refl _)
  have hinj := GenuineChern.pullback_injective sY E' (GenuineChern.topHalf C) m k
  refine injective_flatPullbackChow_of_isIso_comp C sQ (bundleProj E' ≫ sY) sY p
    (bundleProj E') (h.flip.isoPullback.hom ≫ e.inv) ?_ hsQ rfl m hp
    (relativeDimension_bundleProj E' m) k hinj
  rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, IsPullback.isoPullback_hom_fst]

/-! ### The splitting principle -/

/-- The splitting principle with clause (1) for every base change, in the form the strong
induction on `∑ binom(r_i, 2)` proves: the total relative dimension is the induction
variable. -/
private theorem exists_splittingMorphism_universal_aux (C : ChowSituation.{u}) :
    ∀ (n : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type)
      [Fintype I] (E : I → X.Modules) (r : I → ℕ),
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) →
      ∑ i, (r i).choose 2 = n →
      ∃ T : SplittingMorphism C sX n, UniversallyInjectiveFlatPullback C T.π n ∧
        ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj (E i)) (r i) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X sX _ I _ E r hE hn
    by_cases hr : ∀ i, r i ≤ 1
    · -- every rank is at most one: the identity of `X` already splits the collection
      have hn0 : n = 0 := by
        rw [← hn, Finset.sum_eq_zero]
        intro i _
        exact Nat.choose_eq_zero_of_lt (by have := hr i; omega)
      subst hn0
      refine ⟨SplittingMorphism.id C sX, UniversallyInjectiveFlatPullback.id X, fun i ↦ ?_⟩
      exact Stacks.WeilCohomology.hasInvertibleFiltration_of_rank_le_one _ (r i)
        (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (𝟙 X) (E i) (r i) (hE i))
        (hr i)
    -- some rank exceeds one: split one invertible quotient off that module
    obtain ⟨i, hi⟩ := not_forall.mp hr
    have hi : 1 < r i := by omega
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (r i - 1 + 1) := by
      rw [Nat.sub_add_cancel (show 1 ≤ r i by omega)]
      exact hE i
    set D := BundleStep.ofProjectiveBundle C sX (E i) (r i - 1) hEi with hD
    have hDu : UniversallyInjectiveFlatPullback C D.π (r i - 1) :=
      @universallyInjectiveFlatPullback_bundleProj C X (E i) (r i - 1) hEi
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub j)
        (Function.update r i (r i - 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E j) (r j) (hE j)
    have hchoose : (r i - 1).choose 2 + (r i - 1) = (r i).choose 2 := by
      obtain ⟨m, hm⟩ : ∃ m, r i = m + 1 := ⟨r i - 1, by omega⟩
      have key : (m + 1).choose 2 = m.choose 2 + m := by
        change Nat.choose (m + 1) (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        change m + Nat.choose m 2 = Nat.choose m 2 + m
        omega
      rw [hm, Nat.add_sub_cancel, key]
    have hsplit : ∀ f : I → ℕ, ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := fun f ↦
      (Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)).symm
    have hA : (∑ j, (Function.update r i (r i - 1) j).choose 2) =
        (r i - 1).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 := by
      rw [hsplit, Function.update_self]
      exact congrArg _ (Finset.sum_congr rfl fun j hj ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hB := hsplit fun j ↦ (r j).choose 2
    have hsum : (∑ j, (Function.update r i (r i - 1) j).choose 2) + (r i - 1) = n := by
      rw [hA, ← hn, hB]; omega
    have hlt : (∑ j, (Function.update r i (r i - 1) j).choose 2) < n := by
      rw [hA, ← hn, hB]
      have : 1 ≤ r i - 1 := by omega
      omega
    obtain ⟨T, hTu, hT⟩ := ih _ hlt D.sP I
      (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub)
      (Function.update r i (r i - 1)) hE' rfl
    subst hsum
    refine ⟨SplittingMorphism.compStep D T,
      UniversallyInjectiveFlatPullback.comp T.π D.π T.relDim D.relDim hTu hDu, fun j ↦ ?_⟩
    simp only [SplittingMorphism.compStep_P, SplittingMorphism.compStep_π]
    have comp₁ : (Scheme.Modules.pullback T.π).obj
          ((Scheme.Modules.pullback D.π).obj (E j)) ≅
        (Scheme.Modules.pullback (T.π ≫ D.π)).obj (E j) :=
      (Scheme.Modules.pullbackComp T.π D.π).app (E j)
    by_cases hj : j = i
    · rw [hj] at comp₁ ⊢
      have hDx : ((ShortComplex.mk D.incl D.quot D.incl_comp_quot).map
          (Scheme.Modules.pullback T.π)).ShortExact :=
        Stacks.WeilCohomology.shortExact_map_pullback T.π _ D.shortExact
      have hleft : Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj D.sub) (r i - 1) := by
        simpa only [Function.update_self] using hT i
      have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback T.π).obj
            ((Scheme.Modules.pullback D.π).obj (E i))) (r i - 1 + 1) :=
        @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ T.π _ _
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E i) _ hEi)
      refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Nat.sub_add_cancel (show 1 ≤ r i by omega)] using
        Stacks.WeilCohomology.HasInvertibleFiltration.step _ _ _ hDx
          (Stacks.WeilCohomology.isInvertible_pullback_obj T.π D.twistModule
            D.twistModule_isInvertible)
          hrank.isFiniteLocallyFree hleft
    · refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Function.update_of_ne hj] using hT j

/-- **Stacks 02UL, the splitting principle.** Let `(S, δ)` be the situation of Stacks 02QL, let
`X` be locally of finite type over `S` and let `ℰ_i`, `i ∈ I` finite, be finite locally free
`𝒪_X`-modules of ranks `r_i`. There is a flat proper morphism `π : P ⟶ X` of relative dimension
`d = ∑_i binom(r_i, 2)`, along which flat pullback on Chow groups is injective in every degree,
such that

1. for every morphism `f : Y ⟶ X` with `Y` locally of finite type over `S` the flat pullback
   `π_Y^* : A_k(Y) ⟶ A_{k+d}(Y ×_X P)` along the base change `π_Y : Y ×_X P ⟶ Y` is injective in
   every degree, and
2. each `π^*ℰ_i` has a filtration of length `r_i` whose successive quotients are invertible
   `𝒪_P`-modules.

The morphism is the iterated projective bundle
(`Stacks.Chow.BundleStep.ofProjectiveBundle`); clause (1) is carried through the iteration as
`Stacks.Chow.UniversallyInjectiveFlatPullback`. -/
@[stacks 02UL "both clauses, clause (1) in the source's form: for every f : Y -> X, with Y \
locally of finite type over S by an arbitrary structure morphism, flat pullback along the base \
change Y x_X P -> Y is injective in every degree. Relative dimension d = sum of binom(r_i, 2). \
The source says projective; the morphism delivered is flat and proper (each layer is a \
projective bundle, proper by Stacks 0800), but H-projectivity of the tower is not proved"]
theorem exists_splittingMorphism_universal (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I] (E : I → X.Modules)
    (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      (∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X) (k : ℤ),
        Function.Injective (flatPullbackChow C (pullback.fst f T.π ≫ sY) sY (pullback.fst f T.π)
          rfl (∑ i, (r i).choose 2)
          (AlgebraicGeometry.RelativeDimension.of_isPullback
            (IsPullback.of_hasPullback f T.π).flip T.relDim) k
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _))) ∧
      ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj (E i)) (r i) := by
  obtain ⟨T, hTu, hT⟩ := exists_splittingMorphism_universal_aux C _ sX I E r hE rfl
  exact ⟨T, fun sY _ f k ↦ hTu sY _ f (pullback.fst f T.π) (pullback.snd f T.π)
    (IsPullback.of_hasPullback f T.π).flip rfl _ k, hT⟩

end Stacks.Chow

end
