module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkFraction
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.LocalFamilyAssembly
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicFromGenericStalk
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierCancellation
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.PullbackGenericValue

/-!
# One member of the family of Tag 0BD7, at one point of `X`

The penultimate paragraph of [Stacks, Tag 0BD7] works at a point `x` of `X`. It has an affine
chart `U ∋ x` on which `ℒ` has a generator, the generator `m` of the stalk of `ℒ` at the generic
point that the first paragraph builds, and the relation `r s = g u` between two nonzero germs
`g`, `r` of `𝒪_Y` at `φ(x)`, a unit `u` of `𝒪_{X, x}` and the chart ratio; and from them it
produces a meromorphic function `q = r / g` on a neighbourhood of `φ(x)` with `φ^*(q) s` regular
and generating `ℒ` at `x`. This file is that production, with the relation as a hypothesis.

Everything happens at the generic point. On an integral scheme every nonempty open contains the
generic point, so `AlgebraicGeometry.meromorphicSectionOfGenericStalk_eval_eq_`
`toMeromorphicSectionSheafAsModule_iff` turns the equation `φ^*(q) s = t` on a neighbourhood of
`x` into the single-stalk identity `q · m = germ_ξ t`; the left-hand side is computed by the
scalar law `AlgebraicGeometry.meromorphicSectionSheafIsoConstant_smul` together with
`AlgebraicGeometry.totalQuotientSheafIsoConstant_restrict_ringSheafPullbackOfFlat`, which names
the generic value of `φ^*(q)`, and the right-hand side by the choice of `t`.

That choice is forced: `t` is the generator of the chart multiplied by a section representing
the unit `u`. Its germ at `x` is a unit multiple of the generator's, so it generates there
(`Stacks.SheafOfModules.mem_generatingLocus_of_grpGerm_eq_smul`), and its germ at the generic
point is the image of `u` in `K(X)` times the generator's, which is exactly `q · m` once the
relation `r s = g u` is divided by `g`.

## Main results

* `Stacks.InvertiblePullback.exists_mem_generatingLocus_restrictₛₗ_pullbackMeromorphicMul_eq`:
  the data a member of `Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` owes at the point
  `x` — an open `A` of the base, an open `V ∋ x` of `φ^{-1}(A)`, a meromorphic function `q` on
  `A` and a regular section `t` of `ℒ` on `V` generating at `x` with `φ^*(q) s = t` there.

## Implementation notes

The tag is **withheld**: the statement carries an affine chart of `X`, a point of `X` and the
relation `r s = g u`, none of which [Stacks, Tag 0BD7] states. What is still owed to use it is
that relation together with `hm`, and both come from
`AlgebraicGeometry.exists_isUnit_mul_eq_germ_generatorRatio` and
`AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator` — at a point of the generic fibre
over the generic point of `X`, so that connecting them to the statements here is a transport
along `AlgebraicGeometry.exists_fiberι_base_eq_genericPoint`.

Scalar multiplications are written `HSMul.hSMul` with the scalar type named. `ℒ` has to be bound
as `X.Modules`, because `SheafOfModules.IsQuasicoherent` — which
`AlgebraicGeometry.meromorphicSectionOfGenericStalk` needs — does not synthesize at the
`structureSheafRing` spelling; and at that binding the instance for `c • t` is not found from
`c : Γ(X, V)` alone, the module structure on `ℒ(V)` being over the ring sheaf of `X.Modules`.
For the same reason the stalk module structure is introduced by `let` before
`Stacks.SheafOfModules.mem_generatingLocus_of_grpGerm_eq_smul` is applied.

The two germ identities fed to `rw` are stated with `SheafOfModules.presheaf` and proved by the
`PresheafOfModules` lemmas as terms: the lemmas produce `L.val.presheaf`, the goal carries
`L.presheaf`, and the two are definitionally but not syntactically equal, so a direct `rw`
reports that it cannot find its own pattern.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.InvertiblePullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
  (L : X.Modules) [L.IsQuasicoherent]

/-- The germ at `x ∈ V` of the restriction to `V ≤ U₀` of a section `u'` is the germ of `u'`. -/
private theorem germ_map_homOfLE_eq {X : Scheme.{u}} {x : X} {U₀ V : X.Opens} (hVU₀ : V ≤ U₀)
    (hxV : x ∈ V) (u' : X.presheaf.obj (op U₀)) {u : X.presheaf.stalk x}
    (hu' : X.presheaf.germ U₀ x (hVU₀ hxV) u' = u) :
    X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU₀).op u') = u :=
  (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU₀) x hxV u').trans hu'

omit [AlgebraicGeometry.IsIntegral X] [L.IsQuasicoherent] in
/-- A unit multiple of a generator at `x`, restricted to a smaller open, still generates at `x`. -/
theorem mem_generatingLocus_smul_restrict_of_germ_eq {x : X} {U U₀ V : X.Opens} (hVU : V ≤ U)
    (hVU₀ : V ≤ U₀) (hxV : x ∈ V) (hxU : x ∈ U) (genU : L.val.obj (op U))
    (hgenU : x ∈ generatingLocus L genU) {u : X.presheaf.stalk x} (hu : IsUnit u)
    (u' : X.presheaf.obj (op U₀)) (hu' : X.presheaf.germ U₀ x (hVU₀ hxV) u' = u) :
    x ∈ generatingLocus L
      (HSMul.hSMul (α := ↑((Stacks.Sheaves.Differentials.ringSheaf
          (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op V)))
        (X.presheaf.map (homOfLE hVU₀).op u') (L.val.restrictₛₗ (homOfLE hVU).op genU)) := by
  let := stalkModule X.toRingedSpace L.val x
  refine mem_generatingLocus_of_grpGerm_eq_smul L hxV hxU hu ?_ hgenU
  refine (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X.toRingedSpace
    L.val x _ hxV _ _).trans (congrArg₂ (· • ·) ?_ ?_)
  · exact germ_map_homOfLE_eq hVU₀ hxV u' hu'
  · exact TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE hVU) x hxV genU

omit [L.IsQuasicoherent] in
/-- The generic germ of `u' • genU` restricted to `V` is the image of `germ_x u'` in `K(X)` times
the generic germ of `genU`. -/
theorem germ_genericPoint_smul_restrict_eq {x : X} {U U₀ V : X.Opens} (hVU : V ≤ U)
    (hVU₀ : V ≤ U₀) (hxV : x ∈ V) (hξU : genericPoint X ∈ U) (hξV : genericPoint X ∈ V)
    (genU : L.val.obj (op U)) (u' : X.presheaf.obj (op U₀)) {u : X.presheaf.stalk x}
    (hu' : X.presheaf.germ U₀ x (hVU₀ hxV) u' = u) :
    L.presheaf.germ V (genericPoint X) hξV
        (HSMul.hSMul (α := ↑((Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op V)))
          (X.presheaf.map (homOfLE hVU₀).op u') (L.val.restrictₛₗ (homOfLE hVU).op genU))
      = algebraMap (X.presheaf.stalk x) X.functionField u •
          L.presheaf.germ U (genericPoint X) hξU genU := by
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hgermu : X.presheaf.germ V (genericPoint X) hξV (X.presheaf.map (homOfLE hVU₀).op u')
      = algebraMap (X.presheaf.stalk x) X.functionField u :=
    ((Scheme.algebraMap_germ_eq_germToFunctionField X hxV
      (X.presheaf.map (homOfLE hVU₀).op u')).symm).trans
        (congrArg _ (germ_map_homOfLE_eq hVU₀ hxV u' hu'))
  have h1 : L.presheaf.germ V (genericPoint X) hξV
        (HSMul.hSMul (α := ↑((Stacks.Sheaves.Differentials.ringSheaf
            (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op V)))
          (X.presheaf.map (homOfLE hVU₀).op u') (L.val.restrictₛₗ (homOfLE hVU).op genU))
      = X.presheaf.germ V (genericPoint X) hξV (X.presheaf.map (homOfLE hVU₀).op u')
          • L.presheaf.germ V (genericPoint X) hξV (L.val.restrictₛₗ (homOfLE hVU).op genU) :=
    PresheafOfModules.germ_smul L.val (genericPoint X) _ hξV _ _
  have h2 : L.presheaf.germ V (genericPoint X) hξV (L.val.restrictₛₗ (homOfLE hVU).op genU)
      = L.presheaf.germ U (genericPoint X) hξU genU :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE hVU) (genericPoint X) hξV genU
  rw [h1, hgermu, h2]

/-- **The two conjuncts a member of `Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` owes at
one point.** From a chart generator `genU` of `ℒ` at `x`, the generic generator `m` as the
multiple `c` of its germ there, and the relation `r c = g u` of the penultimate paragraph of
[Stacks, Tag 0BD7], out come `A ∋ φ(x)`, an open `V ∋ x` of `φ^{-1}(A)`, a meromorphic function
`q` on `A` and a regular section `t` of `ℒ` on `V` generating at `x` with `φ^*(q) s = t`. -/
theorem exists_mem_generatingLocus_restrictₛₗ_pullbackMeromorphicMul_eq
    {x : X} {U : X.Opens} (hxU : x ∈ U) (hξU : genericPoint X ∈ U)
    (genU : L.val.obj (op U)) (hgenU : x ∈ generatingLocus L genU)
    (m : L.presheaf.stalk (genericPoint X)) (c : X.functionField)
    (hm : m = c • L.presheaf.germ U (genericPoint X) hξU genU)
    {g r : Y.presheaf.stalk (f x)} {u : X.presheaf.stalk x}
    (hg : g ≠ 0) (hu : IsUnit u)
    (hgru : algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r) * c
      = algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom g) *
        algebraMap (X.presheaf.stalk x) X.functionField u) :
    ∃ (A : Y.Opens) (V : X.Opens) (hVA : (V : Opens X.toRingedSpace.carrier) ≤
        ((f ⁻¹ᵁ A : X.Opens) : Opens X.toRingedSpace.carrier))
      (q : (totalQuotientSheafAsModule Y).val.obj (op A)) (t : L.val.obj (op V)),
      x ∈ V ∧ x ∈ generatingLocus L t ∧
        (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hVA).op
            ((pullbackMeromorphicMul f L (meromorphicSectionOfGenericStalk X L m)).val.app
              (op A) q)
          = (toMeromorphicSectionSheafAsModule X L).val.app (op V) t := by
  classical
  obtain ⟨A, hfxA, hAaff, g', r', q, hg'germ, hr'germ, hg'nzd, hq⟩ :=
    exists_isAffineOpen_nhds_mul_toTotalQuotientSheaf_eq Y g r hg
  obtain ⟨U₀, hxU₀, u', hu'⟩ := X.presheaf.exists_germ_eq u
  obtain ⟨V, hVU, hVU₀, hVA, hxV⟩ : ∃ V : X.Opens,
      V ≤ U ∧ V ≤ U₀ ∧ V ≤ (f ⁻¹ᵁ A : X.Opens) ∧ x ∈ V :=
    ⟨U ⊓ U₀ ⊓ f ⁻¹ᵁ A, inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right,
      inf_le_right, ⟨⟨hxU, hxU₀⟩, hfxA⟩⟩
  have hξV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨x, ⟨Set.mem_univ _, hxV⟩⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hval : ∀ (a : Γ(Y, A)) (b : Y.presheaf.stalk (f x)),
      Y.presheaf.germ A (f x) hfxA a = b →
      X.presheaf.germ V (genericPoint X) hξV ((f.appLE A V hVA).hom a)
        = algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom b) :=
    fun a b h => (germ_genericPoint_appLE f hVA hxV hξV a).trans (by rw [h])
  have hgval := hval g' g hg'germ
  have hrval := hval r' r hr'germ
  have hgne : X.presheaf.germ V (genericPoint X) hξV ((f.appLE A V hVA).hom g') ≠ 0 :=
    germ_genericPoint_appLE_ne_zero f hVA hxV hξV (by rwa [hg'germ])
  have hĝ : algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom g) ≠ 0 :=
    hgval ▸ hgne
  have hρ : algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r)
        * (algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom g))⁻¹
        * X.presheaf.germ V (genericPoint X) hξV ((f.appLE A V hVA).hom g')
      = X.presheaf.germ V (genericPoint X) hξV ((f.appLE A V hVA).hom r') := by
    rw [hgval, hrval, inv_mul_cancel_right₀ hĝ]
  have hρc : algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r)
        * (algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom g))⁻¹ * c
      = algebraMap (X.presheaf.stalk x) X.functionField u := by
    rw [mul_right_comm, hgru, mul_right_comm, mul_inv_cancel₀ hĝ, one_mul]
  refine ⟨A, V, hVA, q,
    HSMul.hSMul (α := ↑((Stacks.Sheaves.Differentials.ringSheaf
        (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op V)))
      (X.presheaf.map (homOfLE hVU₀).op u') (L.val.restrictₛₗ (homOfLE hVU).op genU),
    hxV, ?_, ?_⟩
  · exact mem_generatingLocus_smul_restrict_of_germ_eq L hVU hVU₀ hxV hxU genU hgenU hu u' hu'
  · have hgermt : (algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r)
            * (algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom g))⁻¹) • m
        = L.presheaf.germ V (genericPoint X) hξV
            (HSMul.hSMul (α := ↑((Stacks.Sheaves.Differentials.ringSheaf
                (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op V)))
              (X.presheaf.map (homOfLE hVU₀).op u')
              (L.val.restrictₛₗ (homOfLE hVU).op genU)) := by
      rw [germ_genericPoint_smul_restrict_eq L hVU hVU₀ hxV hξU hξV genU u' hu', hm, smul_smul,
        hρc]
    refine (restrict_pullbackMeromorphicMul_val_app f L
      (meromorphicSectionOfGenericStalk X L m) A hVA q).trans ?_
    refine (eq_toMeromorphicSectionSheafAsModule_iff_eq_germ X L hξV _ _
      (meromorphicSectionSheafIsoConstant_smul X L _ _ ?_
        (meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk_eval X L V m))).mpr
      hgermt
    exact totalQuotientSheafIsoConstant_restrict_ringSheafPullbackOfFlat f hVA hξV q g' r' hq _
      hgne hρ

end Stacks.InvertiblePullback

end
