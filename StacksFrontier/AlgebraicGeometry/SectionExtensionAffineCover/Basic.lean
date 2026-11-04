module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Sum
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a function off an affine nonvanishing locus, and the basis of an ample sheaf

Let `Y` be a scheme and `M` an invertible `𝒪_Y`-module. Suppose finitely many global sections
`σ i` of one power `M^{⊗ N}` have affine nonvanishing loci `T i` covering `Y`. This file proves
that a function on `T i₀` becomes, after multiplication by a high enough power of `σ i₀`, the
restriction of a global section of a power of `M`. That is the surjectivity half of
[Stacks, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW) for `F = 𝒪_X`, in the form an
ample sheaf supplies it -- see the implementation notes for why the tag is withheld.

The consequence is the one the source draws: **for an ample invertible sheaf the nonvanishing
loci of the global sections of the positive tensor powers form a basis for the topology, and
the affine ones already do** -- items (3) and (4) of
[Stacks, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3) (the items labelled Tag 01Q6 and
Tag 01Q7). The Stacks proof of those implications runs through the open immersion of `Y` into
`Proj Γ_*(Y, L)` (Tag 01Q1 and the Proj constructions of Section 01M3); the proof here needs no
Proj, no graded section ring, and no prime avoidance.

That basis statement is the **one-point case of
[Stacks, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)**, which is the residue recorded
for 09NV in this repository. What 09NV asks for beyond it is the passage from one point
to a finite set, for which the engine is the existing
`AlgebraicGeometry.Scheme.Modules.isAffineOpen_nonvanishingOpen_add`
(`AffineNonvanishing/Sum.lean`) together with
`Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_add`,
`nonvanishingLocus_sectionsOfTop_add_le` and `Topology.exists_maximal_specializes`
(`QuasiAffineNonvanishing/Basic.lean`) -- exactly the combination that file runs for a
quasi-affine scheme with global *functions*. That passage is **not** carried out here.

## Main results

* `Stacks.SheafOfModules.Invertible.exists_sections_eval_eq_smul_of_affineCover`: the
  section-extension lemma.
* `Stacks.SheafOfModules.Invertible.exists_affineCover_of_isAmple`: an ample invertible sheaf
  has, for a single positive power, a finite family of global sections whose nonvanishing loci
  are affine and cover the scheme.
* `Stacks.SheafOfModules.Invertible.exists_sections_mem_nonvanishingOpen_le_of_isAmple`:
  **items (3) and (4) of Tag 01Q3** for an ample invertible sheaf, i.e. the one-point case of
  Tag 09NV.

## Implementation notes

The argument is the one in the Stacks proof of Tag 01PW, with the trivializing cover taken to
be the `T i` themselves. That choice is what makes the proof short: because `σ i` trivializes
`M^{⊗ N}` over `T i` (Tag 01CY) and is *global*, the powers `σ i ^ k` trivialize `M^{⊗ N k}`
over the same open, so every section of every power that occurs is a function times the
restriction of a global section, and all the bookkeeping happens in `Γ(Y, V)`. The pairwise
intersections `T i ⊓ T j` are affine for free -- they are basic opens of `T i`, by
`AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_smul_eq` -- so no
quasi-separatedness hypothesis is needed anywhere and no induction over a compact open is run.

Only two inputs from Mathlib are used, both for the affine open `T i`:
`AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` extends `c` off the basic open
`T i₀ ⊓ T i`, and
`AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen` makes the
local extensions agree on the overlaps after one further multiplication. The gluing is
Mathlib's `TopCat.Sheaf.existsUnique_gluing'` applied to the underlying sheaf of abelian
groups, and the final comparison over `T i₀` is `TopCat.Sheaf.eq_of_locally_eq'`.

**The `@[stacks 01PW]` attribute is withheld** -- see the docstring of
`exists_sections_eval_eq_smul_of_affineCover`. Neither half of Tag 01PW is proved in this file;
both are proved in
`StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean`
(`Stacks.SheafOfModules.sectionLocalizationMap_injective` and
`Stacks.SheafOfModules.sectionLocalizationMap_bijective`), which carries the two attributes.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [EGA I, second edition, Section 6.8]
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u

namespace Stacks.SheafOfModules.Invertible

variable {Y : Scheme.{u}} (M : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property M]

local notation "Mpow[" n "]" => tensorPowerModule' M ((n : ℕ) : ℤ)

local notation "NV[" n ", " s "]" =>
  Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace)
    (tensorPowerModule' M ((n : ℕ) : ℤ)) s

local notation "res[" h ", " x "]" => Y.presheaf.map (Quiver.Hom.op (homOfLE h)) x

/-- The basic open of a function `h` on `T ≤ NV[n, w]` with `h • w|_T = a|_T` is `NV[n, a] ⊓ T`. -/
private theorem basicOpen_eq_inf_nonvanishingOpen_of_eval_smul_eq {n : ℕ}
    (T : Opens Y.toRingedSpace.carrier) (a w : Mpow[n].sections) (hT : T ≤ NV[n, w])
    (h : Y.presheaf.obj (op T)) (hh : h • w.eval (op T) = a.eval (op T)) :
    Y.basicOpen h = NV[n, a] ⊓ T := by
  have key := AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_smul_eq
    (M := Mpow[n]) T (a.eval (op ⊤)) (w.eval (op ⊤))
    (by rw [sectionsOfTop_eval_top_self]; exact hT) h
    (by rw [sectionsOfTop_eval_top_self, sectionsOfTop_eval_top_self]; exact hh)
  rwa [sectionsOfTop_eval_top_self] at key

/-- **Tag 01PW, section-extension form.** -/
theorem exists_sections_eval_eq_smul_of_affineCover
    {ι : Type u} [Finite ι] (N : ℕ) (hN : 1 ≤ N)
    (σ : ι → Mpow[N].sections)
    (T : ι → Opens Y.toRingedSpace.carrier)
    (hT : ∀ i, T i = NV[N, σ i])
    (haff : ∀ i, IsAffineOpen (T i))
    (hcov : (⨆ i, T i) = ⊤)
    (i₀ : ι) (c : Y.presheaf.obj (op (T i₀))) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ a w : Mpow[m].sections,
      T i₀ ≤ NV[m, w] ∧
      a.eval (op (T i₀)) = c • w.eval (op (T i₀)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- the coefficient of `σ j` with respect to the trivialization `σ i` over `T i`
  have hcoef : ∀ i j : ι, ∃ g : Y.presheaf.obj (op (T i)),
      g • (σ i).eval (op (T i)) = (σ j).eval (op (T i)) := fun i j =>
    (Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen (X := Y.toRingedSpace)
      Mpow[N] (σ i) (T i) (le_of_eq (hT i))).surjective _
  choose g hg using hcoef
  -- the basic open of that coefficient is the intersection of the two nonvanishing opens
  have hbo : ∀ i j : ι, Y.basicOpen (g i j) = T j ⊓ T i := by
    intro i j
    rw [basicOpen_eq_inf_nonvanishingOpen_of_eval_smul_eq M (T i) (σ j) (σ i) (le_of_eq (hT i))
      (g i j) (hg i j), ← hT j]
  -- restriction of the coefficient equation to a smaller open
  have hgres : ∀ (i j : ι) (V : Opens Y.toRingedSpace.carrier) (hV : V ≤ T i),
      res[hV, g i j] • (σ i).eval (op V) = (σ j).eval (op V) := by
    intro i j V hV
    have h1 : Mpow[N].val.map (homOfLE hV).op ((σ j).eval (op (T i))) = (σ j).eval (op V) :=
      PresheafOfModules.sections_property (σ j) (homOfLE hV).op
    have h2 : Mpow[N].val.map (homOfLE hV).op ((σ i).eval (op (T i))) = (σ i).eval (op V) :=
      PresheafOfModules.sections_property (σ i) (homOfLE hV).op
    rw [← h1, ← hg i j, PresheafOfModules.map_smul, h2]
    rfl
  -- powers of the coefficient equation
  have hpow : ∀ (i j : ι) (V : Opens Y.toRingedSpace.carrier) (hV : V ≤ T i) (k : ℕ),
      (sectionPow' M (σ j) k).eval (op V)
        = res[hV, g i j] ^ k • (sectionPow' M (σ i) k).eval (op V) := fun i j V hV k =>
    sectionPow'_eval_eq_of_smul_eq M (σ j) (σ i) V _ (hgres i j V hV) k
  -- the coefficients compose
  have hgmul : ∀ (i j : ι) (V : Opens Y.toRingedSpace.carrier) (hVi : V ≤ T i) (hVj : V ≤ T j),
      res[hVi, g i j] * res[hVj, g j i₀] = res[hVi, g i i₀] := by
    intro i j V hVi hVj
    refine (Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen
      (X := Y.toRingedSpace) Mpow[N] (σ i) V (le_trans hVi (le_of_eq (hT i)))).injective ?_
    show (res[hVi, g i j] * res[hVj, g j i₀]) • (σ i).eval (op V) = _
    rw [mul_comm, mul_smul, hgres i j V hVi, hgres j i₀ V hVj, hgres i i₀ V hVi]
  -- `c` restricted to the overlap, and the affine extension of it over `T i`
  have hle : ∀ i : ι, Y.basicOpen (g i i₀) ≤ T i₀ := fun i => by
    rw [hbo i i₀]; exact inf_le_left
  have hext : ∀ i : ι, ∃ (n : ℕ) (yy : Y.presheaf.obj (op (T i))),
      yy |_ Y.basicOpen (g i i₀)
        = (g i i₀ |_ Y.basicOpen (g i i₀)) ^ n * res[hle i, c] := fun i =>
    AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen Y (T i) (haff i) (g i i₀)
      res[hle i, c]
  choose n yy hyy using hext
  -- a uniform exponent for the extensions
  obtain ⟨E, hE⟩ := Finite.exists_le fun i => n i + 1
  have hE1 : 1 ≤ E := le_trans (Nat.le_add_left 1 _) (hE i₀)
  have hEn : ∀ i, n i ≤ E := fun i => le_trans (Nat.le_succ _) (hE i)
  have hz : ∀ i : ι, ∃ zz : Y.presheaf.obj (op (T i)),
      zz |_ Y.basicOpen (g i i₀)
        = (g i i₀ |_ Y.basicOpen (g i i₀)) ^ E * res[hle i, c] := by
    intro i
    refine ⟨(g i i₀) ^ (E - n i) * yy i, ?_⟩
    simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at hyy ⊢
    rw [map_mul, map_pow, hyy i, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hEn i)]
  choose zz hzz using hz
  simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at hzz
  -- the overlaps are affine and sit inside both members
  have hAi : ∀ i j : ι, Y.basicOpen (g i j) ≤ T i := fun i j => Y.basicOpen_le (g i j)
  have hAaff : ∀ i j : ι, IsAffineOpen (Y.basicOpen (g i j)) := fun i j =>
    (haff i).basicOpen (g i j)
  have hinf : ∀ i j : ι, T i ⊓ T j = Y.basicOpen (g i j) := fun i j => by
    rw [hbo i j, inf_comm]
  have hIaff : ∀ i j : ι, IsAffineOpen (T i ⊓ T j) := fun i j => by
    rw [hinf i j]; exact hAaff i j
  have hIi : ∀ i j : ι, T i ⊓ T j ≤ T i := fun _ _ => inf_le_left
  have hIj : ∀ i j : ι, T i ⊓ T j ≤ T j := fun _ _ => inf_le_right
  -- on the overlap the two extensions agree after multiplying by a power of `g i i₀`
  have hdvan : ∀ i j : ι, ∃ kk : ℕ,
      res[hIi i j, g i i₀] ^ kk *
        (res[hIi i j, zz i] - res[hIj i j, zz j] * res[hIi i j, g i j] ^ E) = 0 := by
    intro i j
    refine AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y
      (hIaff i j) _ res[hIi i j, g i i₀] ?_
    have hBA : Y.basicOpen res[hIi i j, g i i₀] ≤ T i ⊓ T j := Y.basicOpen_le _
    have hBbo : Y.basicOpen res[hIi i j, g i i₀] ≤ Y.basicOpen (g i i₀) := by
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    have hBTi : Y.basicOpen res[hIi i j, g i i₀] ≤ T i := le_trans hBA (hIi i j)
    have hBTj : Y.basicOpen res[hIi i j, g i i₀] ≤ T j := le_trans hBA (hIj i j)
    have hBT0 : Y.basicOpen res[hIi i j, g i i₀] ≤ T i₀ := le_trans hBbo (hle i)
    have hBboj : Y.basicOpen res[hIi i j, g i i₀] ≤ Y.basicOpen (g j i₀) := by
      rw [hbo j i₀]; exact le_inf hBT0 hBTj
    have e1 := congrArg (fun x => Y.presheaf.map (homOfLE hBbo).op x) (hzz i)
    have e2 := congrArg (fun x => Y.presheaf.map (homOfLE hBboj).op x) (hzz j)
    have e3 := hgmul i j (Y.basicOpen res[hIi i j, g i i₀]) hBTi hBTj
    simp only [TopCat.Presheaf.restrictOpenCommRingCat_apply, map_mul, map_pow, map_sub,
      ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] at e1 e2 e3 ⊢
    rw [e1, e2, ← e3]
    ring
  choose kk hkk using hdvan
  obtain ⟨E', hE'⟩ := Finite.exists_le fun p : ι × ι => kk p.1 p.2 + 1
  have hE'1 : 1 ≤ E' := le_trans (Nat.le_add_left 1 _) (hE' (i₀, i₀))
  have hE'k : ∀ i j, kk i j ≤ E' := fun i j => le_trans (Nat.le_succ _) (hE' (i, j))
  have hkE : ∀ i j : ι,
      res[hIi i j, g i i₀] ^ E' *
        (res[hIi i j, zz i] - res[hIj i j, zz j] * res[hIi i j, g i j] ^ E) = 0 := by
    intro i j
    have h : res[hIi i j, g i i₀] ^ E'
        = res[hIi i j, g i i₀] ^ (E' - kk i j) * res[hIi i j, g i i₀] ^ kk i j := by
      rw [← pow_add, Nat.sub_add_cancel (hE'k i j)]
    rw [h, mul_assoc, hkk i j, mul_zero]
  -- the global sections `W i` and the local sections `u i`
  refine ⟨N * E' + N * E, ?_, ?_⟩
  · exact le_trans (by simpa using Nat.mul_le_mul hN hE'1) (Nat.le_add_right _ _)
  -- the global sections `W i` and the local sections `u i`, named
  obtain ⟨Wg, hWg⟩ : ∃ Wg : ∀ i : ι, Mpow[(N * E' + N * E)].sections,
      ∀ i, Wg i = sectionMul' M (sectionPow' M (σ i₀) E') (sectionPow' M (σ i) E) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Ug, hUg⟩ : ∃ Ug : ∀ i : ι, Mpow[(N * E' + N * E)].val.obj (op (T i)),
      ∀ i, Ug i = zz i • (Wg i).eval (op (T i)) := ⟨_, fun _ => rfl⟩
  have hures : ∀ (i : ι) (V : Opens Y.toRingedSpace.carrier) (hV : V ≤ T i),
      Mpow[(N * E' + N * E)].val.map (homOfLE hV).op (Ug i)
        = res[hV, zz i] • (Wg i).eval (op V) := by
    intro i V hV
    rw [hUg, PresheafOfModules.map_smul, PresheafOfModules.sections_property]
    rfl
  have hWres : ∀ (i j : ι) (V : Opens Y.toRingedSpace.carrier) (hV : V ≤ T i),
      (Wg j).eval (op V) = res[hV, g i j] ^ E • (Wg i).eval (op V) := by
    intro i j V hV
    rw [hWg j, hWg i, sectionMul'_eval, sectionMul'_eval, hpow i j V hV E,
      sectionMulOver_smul_right]
  have hWfac : ∀ (i : ι) (V : Opens Y.toRingedSpace.carrier) (hV : V ≤ T i),
      (Wg i).eval (op V) = res[hV, g i i₀] ^ E'
        • sectionMulOver M (N * E') (N * E) (op V) ((sectionPow' M (σ i) E').eval (op V))
            ((sectionPow' M (σ i) E).eval (op V)) := by
    intro i V hV
    rw [hWg i, sectionMul'_eval, hpow i i₀ V hV E', sectionMulOver_smul_left]
  have hcompat : TopCat.Presheaf.IsCompatible Mpow[(N * E' + N * E)].val.presheaf T Ug := by
    intro i j
    show Mpow[(N * E' + N * E)].val.map (homOfLE (hIi i j)).op (Ug i)
      = Mpow[(N * E' + N * E)].val.map (homOfLE (hIj i j)).op (Ug j)
    rw [hures i _ (hIi i j), hures j _ (hIj i j), hWres i j _ (hIi i j),
      hWfac i _ (hIi i j)]
    simp only [smul_smul]
    congr 1
    linear_combination hkE i j
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} Y.toRingedSpace.carrier :=
    ⟨Mpow[(N * E' + N * E)].val.presheaf, SheafOfModules.isSheaf Mpow[(N * E' + N * E)]⟩
  obtain ⟨Atop, hAtop, -⟩ := Fsh.existsUnique_gluing'
    T ⊤ (fun _ => homOfLE le_top) (le_of_eq hcov.symm) Ug hcompat
  refine ⟨Stacks.SheafOfModules.sectionsOfTop Mpow[(N * E' + N * E)] Atop, Wg i₀, ?_, ?_⟩
  · have hloc : Stacks.SheafOfModules.nonvanishingLocus Mpow[(N * E' + N * E)] (Wg i₀)
        = Stacks.SheafOfModules.nonvanishingLocus Mpow[N] (σ i₀) := by
      rw [hWg i₀, nonvanishingLocus_sectionMul',
        nonvanishingLocus_sectionPow' M (σ i₀) E' hE'1,
        nonvanishingLocus_sectionPow' M (σ i₀) E hE1, Set.inter_self]
    intro x hx
    show x ∈ Stacks.SheafOfModules.nonvanishingLocus Mpow[(N * E' + N * E)] _
    rw [hloc]
    exact (hT i₀ ▸ hx : x ∈ NV[N, σ i₀])
  · have hcover : T i₀ ≤ ⨆ i, Y.basicOpen (g i i₀) := by
      refine le_of_eq (Eq.symm ?_)
      calc (⨆ i, Y.basicOpen (g i i₀)) = ⨆ i, (T i₀ ⊓ T i) := iSup_congr fun i => hbo i i₀
        _ = T i₀ ⊓ ⨆ i, T i := by rw [inf_iSup_eq]
        _ = T i₀ := by rw [hcov, inf_top_eq]
    have key : ∀ i : ι,
        Mpow[(N * E' + N * E)].val.map (homOfLE (hle i)).op
            ((Stacks.SheafOfModules.sectionsOfTop Mpow[(N * E' + N * E)] Atop).eval (op (T i₀)))
          = Mpow[(N * E' + N * E)].val.map (homOfLE (hle i)).op (c • (Wg i₀).eval (op (T i₀))) := by
      intro i
      have hL : Mpow[(N * E' + N * E)].val.map (homOfLE (hle i)).op
            ((Stacks.SheafOfModules.sectionsOfTop Mpow[(N * E' + N * E)] Atop).eval (op (T i₀)))
          = res[hAi i i₀, zz i] • (Wg i).eval (op (Y.basicOpen (g i i₀))) := by
        refine Eq.trans (PresheafOfModules.sections_property
          (Stacks.SheafOfModules.sectionsOfTop Mpow[(N * E' + N * E)] Atop) (homOfLE (hle i)).op) ?_
        refine Eq.trans (PresheafOfModules.sections_property
          (Stacks.SheafOfModules.sectionsOfTop Mpow[(N * E' + N * E)] Atop)
            (homOfLE (hAi i i₀)).op).symm ?_
        refine Eq.trans (congrArg
          (fun z : Mpow[(N * E' + N * E)].val.obj (op (T i)) =>
            Mpow[(N * E' + N * E)].val.map (homOfLE (hAi i i₀)).op z) (hAtop i)) ?_
        exact hures i _ (hAi i i₀)
      have hR : Mpow[(N * E' + N * E)].val.map (homOfLE (hle i)).op (c • (Wg i₀).eval (op (T i₀)))
          = res[hle i, c]
            • (res[hAi i i₀, g i i₀] ^ E • (Wg i).eval (op (Y.basicOpen (g i i₀)))) := by
        refine Eq.trans (PresheafOfModules.map_smul (M := Mpow[(N * E' + N * E)].val)
          (homOfLE (hle i)).op c ((Wg i₀).eval (op (T i₀)))) ?_
        refine Eq.trans (congrArg
          (fun z : Mpow[(N * E' + N * E)].val.obj (op (Y.basicOpen (g i i₀))) => res[hle i, c] • z)
          (Eq.trans (PresheafOfModules.sections_property (Wg i₀) (homOfLE (hle i)).op)
            (hWres i i₀ (Y.basicOpen (g i i₀)) (hAi i i₀)))) ?_
        rfl
      rw [hL, hR, smul_smul, hzz i]
      exact congrArg (fun r : Y.presheaf.obj (op (Y.basicOpen (g i i₀))) =>
        r • (Wg i).eval (op (Y.basicOpen (g i i₀)))) (mul_comm _ _)
    exact Fsh.eq_of_locally_eq' (fun i => Y.basicOpen (g i i₀)) (T i₀)
      (fun i => homOfLE (hle i)) hcover _ _ (fun i => key i)

/-! ### The nonvanishing opens of an ample sheaf form a basis -/

/-- Transporting a global section of `M ^ m` along an equality `m = k` does not change its
nonvanishing locus. -/
theorem nonvanishingLocus_sectionsCongr {m k : ℕ} (h : m = k) (ss : Mpow[m].sections) :
    Stacks.SheafOfModules.nonvanishingLocus Mpow[k]
        (sectionsCongr Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property M
          h ss)
      = Stacks.SheafOfModules.nonvanishingLocus Mpow[m] ss :=
  Stacks.SheafOfModules.nonvanishingLocus_sectionsMap
    (e := eqToIso (congrArg (fun j : ℕ => Mpow[j]) h)) (s := ss)

/-- **An ample invertible sheaf admits, for a single positive power, a finite family of global
sections whose nonvanishing loci are affine and cover the scheme.** -/
theorem exists_affineCover_of_isAmple
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple Y M) :
    ∃ (t : Finset Y) (N : ℕ) (_ : 1 ≤ N) (σ : {x : Y // x ∈ t} → Mpow[N].sections),
      (∀ i, IsAffineOpen (NV[N, σ i])) ∧ (⨆ i, NV[N, σ i]) = ⊤ := by
  classical
  choose nn hnn ss hmem haff using hL.2
  have hcs : CompactSpace Y := hL.1
  obtain ⟨t, ht⟩ := hcs.isCompact_univ.elim_finite_subcover
    (fun x : Y => ((NV[nn x, ss x] : Opens Y.toRingedSpace.carrier) : Set Y))
    (fun x => (NV[nn x, ss x]).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hmem x⟩
  have hNpos : 0 < ∏ x ∈ t, nn x := Finset.prod_pos fun x _ => hnn x
  have hdvd : ∀ (i : {x : Y // x ∈ t}), nn i.1 ∣ ∏ x ∈ t, nn x := fun i =>
    Finset.dvd_prod_of_mem _ i.2
  have hq : ∀ (i : {x : Y // x ∈ t}), 1 ≤ (∏ x ∈ t, nn x) / nn i.1 := fun i =>
    (Nat.one_le_div_iff (hnn i.1)).2 (Nat.le_of_dvd hNpos (hdvd i))
  have hloc : ∀ i : {x : Y // x ∈ t},
      NV[∏ x ∈ t, nn x, sectionsCongr Y.toRingedSpace.presheaf
          (structureSheafRing Y.toRingedSpace).property M (Nat.mul_div_cancel' (hdvd i))
          (sectionPow' M (ss i.1) ((∏ x ∈ t, nn x) / nn i.1))]
        = NV[nn i.1, ss i.1] := fun i =>
    Opens.ext ((nonvanishingLocus_sectionsCongr M _ _).trans
      (nonvanishingLocus_sectionPow' M (ss i.1) _ (hq i)))
  refine ⟨t, ∏ x ∈ t, nn x, hNpos, fun i =>
    sectionsCongr Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property M
      (Nat.mul_div_cancel' (hdvd i)) (sectionPow' M (ss i.1) ((∏ x ∈ t, nn x) / nn i.1)), ?_, ?_⟩
  · intro i
    rw [hloc]
    exact haff i.1
  · refine Opens.ext (Set.eq_univ_of_univ_subset ?_)
    refine le_trans ht ?_
    rw [Opens.coe_iSup]
    refine Set.iUnion₂_subset fun x hx => ?_
    refine le_trans (le_of_eq ?_) (Set.subset_iUnion _ (⟨x, hx⟩ : {x : Y // x ∈ t}))
    exact congrArg _ (hloc ⟨x, hx⟩).symm

/-- **Tag 01Q6 (item (3) of Tag 01Q3): the nonvanishing opens of the global sections of the
positive tensor powers of an ample invertible sheaf form a basis for the topology** -- and the
members of that basis can be taken affine, which is item (4) of Tag 01Q3 (tag 01Q7) and is the
one-point case of [Stacks, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV).

Affineness is free here: the section produced has nonvanishing open a *basic* open of the
affine `X_{σ i₀}`, by `AlgebraicGeometry.IsAffineOpen.basicOpen`. -/
@[stacks 01Q3 "(1) implies (3) and (4)",
  ega "II 4.5.2" "(a') => (a)",
  sga "6 II 2.2.3" "(i), single L"]
theorem exists_sections_mem_nonvanishingOpen_le_of_isAmple
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple Y M)
    (W : Y.Opens) (x : Y) (hx : x ∈ W) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (gg : Mpow[m].sections),
      x ∈ NV[m, gg] ∧ NV[m, gg] ≤ W ∧ IsAffineOpen NV[m, gg] := by
  obtain ⟨t, N, hN, σ, haff, hcov⟩ := exists_affineCover_of_isAmple M hL
  have hxtop : x ∈ (⨆ i, NV[N, σ i]) := by rw [hcov]; trivial
  obtain ⟨i₀, hxi₀⟩ := Opens.mem_iSup.mp hxtop
  obtain ⟨h, hhW, hxh⟩ := (haff i₀).exists_basicOpen_le (⟨x, hx⟩ : W) hxi₀
  obtain ⟨m, hm, a, w, hwle, haw⟩ := exists_sections_eval_eq_smul_of_affineCover M N hN σ
    (fun i => NV[N, σ i]) (fun _ => rfl) haff hcov i₀ h
  have hbo : Y.basicOpen h = NV[m, a] ⊓ NV[N, σ i₀] := by
    exact basicOpen_eq_inf_nonvanishingOpen_of_eval_smul_eq M _ a w hwle h haw.symm
  have hloc : NV[m + N, sectionMul' M a (σ i₀)] = Y.basicOpen h := by
    refine Opens.ext ?_
    rw [hbo]
    exact nonvanishingLocus_sectionMul' M a (σ i₀)
  exact ⟨m + N, le_trans hm (Nat.le_add_right _ _), sectionMul' M a (σ i₀),
    by rw [hloc]; exact hxh, by rw [hloc]; exact hhW,
    by rw [hloc]; exact (haff i₀).basicOpen h⟩
end Stacks.SheafOfModules.Invertible

end
