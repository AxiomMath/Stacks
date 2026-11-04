module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Sum
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityFibre

/-!
# Where two of the three points agree, every collinearity equation vanishes

A triple of points of `𝐏(V)` two of which coincide is collinear, whatever the third point is:
the determinant of a matrix with two equal rows vanishes. This file proves that, in the form the
dimension theory of the incidence variety needs, for an arbitrary morphism into the triple
product whose first two components agree:

if `g : S ⟶ 𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` satisfies `g ≫ pr₁ = g ≫ pr₂`, then the image of `g` lies in
the collinearity locus.

Taking `S` to be the fibre of `pr₁ ×_k pr₂` over a pair `(y, y)` this says that the fibre of the
collinearity subscheme over a diagonal pair is the whole of `𝐏(V)`, which is why the base of the
incidence variety of Tag 0B1R has to be the *distinct* pairs: over the diagonal the fibre is not
a line.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_detSection_iff_mem_basicOpen`:
  **the dictionary between collinearity and the chart determinant**, used in both directions.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.det_residue_chartMatrix_eq_zero`: **collinearity at a
  point makes the determinant of the matrix of residues of the chart coordinates vanish.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.notMem_nonvanishingLocus_detSection_of_comp_eq`:
  every determinant section vanishes along such a `g`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_subset_collinearLocus_of_comp_eq`: **the image
  of such a `g` lies in the collinearity locus.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.diagThree`: the morphism `(y, z) ↦ (y, y, z)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_diagThree_subset_collinearLocus`: **the triples
  `(y, y, z)` are all collinear**, so over a pair whose two points coincide the fibre of the
  collinearity subscheme contains a whole copy of `𝐏(V)` and is not a line.

## Implementation notes

The proof is the chart computation of
`AlgebraicGeometry.ProjectiveSpaceOfModule.divBySection_detSection` pulled back along `g`. Choose
a chart around `g s` whose first two frame vectors are *the same* vector `a`: that is possible
because the first two projections of `g s` are the same point of `𝐏(V)`, so one `a` avoids both
homogeneous primes. On that chart the determinant section becomes the determinant of the matrix
whose `i`-th row is the pullback along `prᵢ` of the ratios `ι wⱼ / ι uᵢ`. Restricting that matrix
along `g` turns the first two rows into pullbacks along `g ≫ pr₁` and `g ≫ pr₂` of the *same*
ratios `ι wⱼ / ι a`, and those two morphisms are equal, so the two rows are equal and the
determinant restricts to zero.

A function whose restriction along `g` is zero has a germ at `g s` which `g`'s stalk map sends to
zero, so that germ is not a unit — the stalk of `S` at `s` is a local ring, hence nontrivial —
and therefore `g s` is outside the basic open of the function. The passage from that basic open
back to the nonvanishing locus of the determinant section is
`AlgebraicGeometry.Scheme.Modules.mem_basicOpen_iff_of_smul_eq`, whose hypothesis is exactly the
defining property `Stacks.SheafOfModules.smul_divBySection` of the ratio.

The two bookkeeping lemmas at the head of the file are about the dependence of
`AlgebraicGeometry.Scheme.Hom.appLE` and of `Stacks.SheafOfModules.sectionsOfTop` on data that
the statements do not see: `appLE` depends on the morphism only through its value, and a section
over `⊤` and the section rebuilt from it restrict to the same thing. Neither is specific to
projective space.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-- `AlgebraicGeometry.Scheme.Hom.appLE` depends on the morphism only through its value. -/
public theorem appLE_congr_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hff : f = f')
    (U : Y.Opens) (W : X.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ f' ⁻¹ᵁ U) :
    f.appLE U W e = f'.appLE U W e' := by
  subst hff
  rfl

/-- A global section of a sheaf of modules is the section rebuilt from its value over `⊤`. -/
public theorem sectionsOfTop_eval_top_self {X : Scheme.{u}}
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (t : M.sections) :
    sectionsOfTop M (t.eval (op ⊤)) = t :=
  sections_ext_of_eval_top M (sectionsOfTop_eval_top M (t.eval (op ⊤)))

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **On a chart the determinant section is nonvanishing exactly where the determinant of the
chart matrix is a unit.** This is the dictionary between collinearity, which is a condition on
sections of `𝒪(1,1,1)`, and the determinant of a matrix of honest functions, and it is used in
both directions: to show a point collinear by exhibiting the determinant as a non-unit, and to
extract the vanishing of the determinant from collinearity. -/
public theorem mem_nonvanishingLocus_detSection_iff_mem_basicOpen (u w : Fin 3 → V)
    {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 0)))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 1)))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 2)))
    {t : prodThree k V} (hx : t ∈ U) :
    t ∈ nonvanishingLocus (X := (prodThree k V).toRingedSpace)
        (tripleTwistModule k V) (detSection k V w) ↔
      t ∈ (prodThree k V).basicOpen ((chartMatrix k V u w h₁ h₂ h₃).det) := by
  have hframe := le_nonvanishingOpen_tripleSection k V (u 0) (u 1) (u 2) h₁ h₂ h₃
  have hdiv := divBySection_detSection k V u w h₁ h₂ h₃
  have htop1 : sectionsOfTop (tripleTwistModule k V) ((tripleSectionOf k V u).eval (op ⊤))
      = tripleSectionOf k V u := sectionsOfTop_eval_top_self _ _
  have htop2 : sectionsOfTop (tripleTwistModule k V) ((detSection k V w).eval (op ⊤))
      = detSection k V w := sectionsOfTop_eval_top_self _ _
  have hb := Scheme.Modules.mem_basicOpen_iff_of_smul_eq (tripleTwistModule k V) U
    ((detSection k V w).eval (op ⊤)) ((tripleSectionOf k V u).eval (op ⊤))
    (by rw [htop1]; exact hframe) ((chartMatrix k V u w h₁ h₂ h₃).det)
    (by
      rw [htop1, htop2, ← hdiv]
      exact smul_divBySection (tripleTwistModule k V) (tripleSectionOf k V u) hframe
        ((detSection k V w).eval (op U)))
    hx
  rw [htop2] at hb
  exact hb.symm

/-- **Every determinant section vanishes where the first two points of the triple agree.** -/
public theorem notMem_nonvanishingLocus_detSection_of_comp_eq
    {S : Scheme.{u}} (g : S ⟶ prodThree k V) (hg : g ≫ pr₁ k V = g ≫ pr₂ k V) (s : S)
    (w : Fin 3 → V) :
    g.base s ∉ nonvanishingLocus (X := (prodThree k V).toRingedSpace)
      (tripleTwistModule k V) (detSection k V w) := by
  -- a vector avoiding the homogeneous prime of the common first point, and one for the third
  obtain ⟨a, ha⟩ := exists_ι_notMem k V ((pr₁ k V).base (g.base s))
  obtain ⟨c, hc⟩ := exists_ι_notMem k V ((pr₃ k V).base (g.base s))
  have hpt : (pr₁ k V).base (g.base s) = (pr₂ k V).base (g.base s) :=
    congrArg (fun m : S ⟶ projectiveSpaceOfModule k V => m.base s) hg
  set u : Fin 3 → V := ![a, a, c]
  -- the chart around `g s`, whose first two frame vectors are the same vector
  set D₁ : (prodThree k V).Opens :=
    pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 0))
  set D₂ : (prodThree k V).Opens :=
    pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 1))
  set D₃ : (prodThree k V).Opens :=
    pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 2))
  set U : (prodThree k V).Opens := D₁ ⊓ D₂ ⊓ D₃
  have h₁ : U ≤ D₁ := le_trans inf_le_left inf_le_left
  have h₂ : U ≤ D₂ := le_trans inf_le_left inf_le_right
  have h₃ : U ≤ D₃ := inf_le_right
  have hx : g.base s ∈ U :=
    ⟨⟨(mem_nonvanishingLocus_tautologicalSection_iff k V a _).mpr ha,
      (mem_nonvanishingLocus_tautologicalSection_iff k V a _).mpr (hpt ▸ ha)⟩,
      (mem_nonvanishingLocus_tautologicalSection_iff k V c _).mpr hc⟩
  -- the first two rows of the chart matrix become equal after restriction along `g`
  have hrow : ∀ j : Fin 3,
      (g.app U).hom (chartRatio k V (pr₁ k V) (u 0) (w j) h₁) =
        (g.app U).hom (chartRatio k V (pr₂ k V) (u 1) (w j) h₂) := by
    intro j
    have key : (pr₁ k V).appLE
          (nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 0))) U h₁ ≫
            g.appLE U (g ⁻¹ᵁ U) le_rfl =
        (pr₂ k V).appLE
          (nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 1))) U h₂ ≫
            g.appLE U (g ⁻¹ᵁ U) le_rfl := by
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr_of_eq hg _ _ _ _
    unfold chartRatio
    rw [Scheme.Hom.app_eq_appLE]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key) (tautRatio k V (u 0) (w j))
  have hdet0 : (g.app U).hom ((chartMatrix k V u w h₁ h₂ h₃).det) = 0 := by
    rw [RingHom.map_det]
    exact Matrix.det_zero_of_row_eq (i := 0) (j := 1) (by decide) (funext hrow)
  -- a function whose restriction along `g` is zero is not a unit at `g s`
  intro hmem
  have hpush := (((prodThree k V).mem_basicOpen _ _ hx).mp
    ((mem_nonvanishingLocus_detSection_iff_mem_basicOpen k V u w h₁ h₂ h₃ hx).mp hmem)).map
      (g.stalkMap s).hom
  rw [Scheme.Hom.germ_stalkMap_apply g U s hx, hdet0, map_zero] at hpush
  exact not_isUnit_zero hpush

/-- **The image of a morphism whose first two components agree lies in the collinearity
locus.** -/
public theorem range_subset_collinearLocus_of_comp_eq {S : Scheme.{u}} (g : S ⟶ prodThree k V)
    (hg : g ≫ pr₁ k V = g ≫ pr₂ k V) :
    Set.range g.base ⊆ collinearLocus k V := by
  rintro _ ⟨s, rfl⟩
  exact (mem_collinearLocus_iff k V _).mpr fun w =>
    notMem_nonvanishingLocus_detSection_of_comp_eq k V g hg s w

/-- **The morphism `(y, z) ↦ (y, y, z)`** of the double product into the triple product, doubling
the first point. -/
public def diagThree : prodTwo k V ⟶ prodThree k V :=
  pullback.lift
    (pullback.lift
      (pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V))
      (pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)) rfl)
    (pullback.snd (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V))
    (by
      rw [prodTwoToSpec, ← Category.assoc, pullback.lift_fst]
      exact pullback.condition)

/-- The first point of `(y, y, z)` is `y`. -/
@[simp]
public theorem diagThree_comp_pr₁ :
    diagThree k V ≫ pr₁ k V =
      pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) := by
  rw [pr₁, ← Category.assoc, prFst, diagThree, pullback.lift_fst, pullback.lift_fst]

/-- The second point of `(y, y, z)` is also `y`. -/
@[simp]
public theorem diagThree_comp_pr₂ :
    diagThree k V ≫ pr₂ k V =
      pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) := by
  rw [pr₂, ← Category.assoc, prFst, diagThree, pullback.lift_fst, pullback.lift_snd]

/-- The third point of `(y, y, z)` is `z`. -/
@[simp]
public theorem diagThree_comp_pr₃ :
    diagThree k V ≫ pr₃ k V =
      pullback.snd (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) := by
  rw [pr₃, diagThree, pullback.lift_snd]

/-- **The triples `(y, y, z)` are collinear**, whatever `y` and `z` are. Together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.diagThree_comp_pr₃`, whose right-hand side is the
second projection of `𝐏(V) ×_k 𝐏(V)`, this says that over a pair whose two points coincide the
collinearity locus contains a whole copy of `𝐏(V)` in the third factor, so the fibre of
`AlgebraicGeometry.ProjectiveSpaceOfModule.collinearProj` there is not a line. -/
public theorem range_diagThree_subset_collinearLocus :
    Set.range (diagThree k V).base ⊆ collinearLocus k V :=
  range_subset_collinearLocus_of_comp_eq k V (diagThree k V)
    (by rw [diagThree_comp_pr₁, diagThree_comp_pr₂])

/-- **Collinearity at a point makes the chart determinant vanish in the residue field.** For a
collinear point `t` of a chart, the determinant of the matrix of residues at `t` of the chart
coordinates is zero. -/
public theorem det_residue_chartMatrix_eq_zero (u w : Fin 3 → V)
    {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 0)))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 1)))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 2)))
    {t : prodThree k V} (hx : t ∈ U) (ht : t ∈ collinearLocus k V) :
    ((chartMatrix k V u w h₁ h₂ h₃).map
        ((IsLocalRing.residue ((prodThree k V).presheaf.stalk t)).comp
          ((prodThree k V).presheaf.germ U t hx).hom)).det = 0 := by
  refine (RingHom.map_det _ (chartMatrix k V u w h₁ h₂ h₃)).symm.trans ?_
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff]
  exact fun hu => (mem_collinearLocus_iff k V t).mp ht w
    ((mem_nonvanishingLocus_detSection_iff_mem_basicOpen k V u w h₁ h₂ h₃ hx).mpr
      (((prodThree k V).mem_basicOpen _ _ hx).mpr hu))

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
