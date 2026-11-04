module

public import StacksFrontier.AlgebraicGeometry.AffineOpensDirectedGlueHom

/-!
# Sections of a sheaf of modules glued from the affine opens of a scheme

`AlgebraicGeometry.AffineOpensGlue.ChartComparison` glues a sheaf of modules on a scheme `X` out
of a sheaf of modules on each affine open together with a comparison isomorphism for each
inclusion of affine opens, and `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom` does
the same for *morphisms*. This file does it for *sections*: a family of sections, one on each
affine open, matched by the comparisons, comes from a section of the glued module over the whole
of `X`, and that section is the only one which reads as the family on every chart.

## Main definitions

* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.IsMatched`: **the compatibility condition** on
  a family of sections of the charts: for each inclusion `V ≤ W` of affine opens the comparison
  attached to that inclusion carries the member of the family at `V` to the restriction of the
  member at `W`.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartLift`: the section of the glued module
  over an affine open that a section of the chart there defines.

## Main results

* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.exists_section`: **a family of sections of
  the charts, matched by the comparisons, comes from a global section of the glued module.**
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.section_ext`: **uniqueness**: two global
  sections of the glued module which read the same on every chart are equal.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec_res_chartLift_of_le`: over an open
  inside a chart `k` below an affine open `V`, the lift of the member of the family at `V` reads
  on `k` as the member of the family at `k`.

## Implementation notes

The compatibility hypothesis is asked for only on *ordered* pairs `V ≤ W` of affine opens, which
is the form in which it arises: the comparisons of a chart comparison exist only along an
inclusion.

A member of the family is lifted to a section of the glued module by the inverse of the transposed
chart isomorphism `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHomIso`. Every
computation is on sections, through `AlgebraicGeometry.localAppFun` and
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec`.

## References

* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.AffineOpensGlue

variable {X : Scheme.{u}}

/-! ### Formal lemmas on sections -/

/-- Two successive restrictions of a section of a sheaf of modules on `X` are one restriction. -/
private theorem val_map_map (A : X.Modules) {O P Q : X.Opens} (h₁ : P ≤ O) (h₂ : Q ≤ P)
    (x : ToType (A.val.obj (op O))) :
    A.val.map (homOfLE h₂).op (A.val.map (homOfLE h₁).op x)
      = A.val.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← PresheafOfModules.map_comp_apply,
    show (homOfLE h₁).op ≫ (homOfLE h₂).op = (homOfLE (h₂.trans h₁)).op from
      Subsingleton.elim _ _]

/-- The components of a morphism of sheaves of modules on `X` commute with restriction of
sections. -/
private theorem app_naturality {A B : X.Modules} (g : A ⟶ B) {O P : X.Opens} (hPO : P ≤ O)
    (x : ToType (A.val.obj (op O))) :
    g.app P (A.val.map (homOfLE hPO).op x) = B.val.map (homOfLE hPO).op (g.app O x) := by
  have e1 := localAppFun_restrictFunctor_map (W := (⊤ : X.Opens)) g (le_top : P ≤ ⊤)
    (A.val.map (homOfLE hPO).op x)
  have e2 := localAppFun_restrictFunctor_map (W := (⊤ : X.Opens)) g (le_top : O ≤ ⊤) x
  have e3 := localAppFun_naturality ((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).map g)
    (le_top : O ≤ ⊤) (le_top : P ≤ ⊤) (homOfLE hPO) x
  rw [← e1, ← e2, e3]

/-- The sections map of an isomorphism of restrictions is injective. -/
private theorem localAppFun_hom_injective {A B : X.Modules} {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ≅ Scheme.Modules.restrict B W.ι) {O : X.Opens}
    (hO : O ≤ W) {a b : ToType (A.val.obj (op O))}
    (h : localAppFun φ.hom O hO a = localAppFun φ.hom O hO b) : a = b := by
  have inv_hom (c : ToType (A.val.obj (op O))) :
      localAppFun φ.inv O hO (localAppFun φ.hom O hO c) = c := by
    rw [← localAppFun_comp, φ.hom_inv_id, localAppFun_id]
  exact (inv_hom a).symm.trans ((congrArg (localAppFun φ.inv O hO) h).trans (inv_hom b))

namespace ChartComparison

variable (D : ChartComparison X)

/-! ### Lifting a section of a chart to the glued module -/

/-- **Reading a section of the glued module on a chart commutes with restriction of sections.** -/
theorem chartSec_naturality (V : X.affineOpens) {O P : X.Opens} (hPO : P ≤ O)
    (x : ToType (D.glued.val.obj (op O))) :
    D.chartSec V P (D.glued.val.map (homOfLE hPO).op x)
      = ((Scheme.Modules.pushforward (chart X V)).obj (D.mod V)).val.map (homOfLE hPO).op
          (D.chartSec V O x) :=
  app_naturality (D.chartHom V) hPO x

/-- **Reading a section of the glued module on a chart is injective.** -/
theorem chartSec_injective (V : X.affineOpens) {O : X.Opens} (hO : O ≤ (V.1 : X.Opens))
    {a b : ToType (D.glued.val.obj (op O))} (h : D.chartSec V O a = D.chartSec V O b) : a = b :=
  (D.localAppFun_chartHomIso_inv_chartSec V hO a).symm.trans
    ((congrArg (fun z => localAppFun (D.chartHomIso V).inv O hO z) h).trans
      (D.localAppFun_chartHomIso_inv_chartSec V hO b))

/-- **The section of the glued module over an affine open that a section of the chart there
defines.** It is the inverse of the transposed chart isomorphism, read on sections. -/
def chartLift (V : X.affineOpens)
    (t : ToType (openSections (chart X V) (D.mod V) (V.1 : X.Opens))) :
    ToType (D.glued.val.obj (op (V.1 : X.Opens))) :=
  localAppFun (D.chartHomIso V).inv (V.1 : X.Opens) le_rfl t

/-- The lift of a section of a chart reads on that chart as the section it came from. -/
theorem chartSec_chartLift (V : X.affineOpens)
    (t : ToType (openSections (chart X V) (D.mod V) (V.1 : X.Opens))) :
    D.chartSec V (V.1 : X.Opens) (D.chartLift V t) = t :=
  D.chartSec_localAppFun_chartHomIso_inv V le_rfl t

/-! ### The compatible family of lifts -/

variable {D}

/-- **A family of sections of the charts is matched by the comparisons** when, for every inclusion
`V ≤ W` of affine opens, the comparison attached to that inclusion carries the member of the
family at `V` to the restriction to `V` of the member at `W`. -/
def IsMatched (s : ∀ V : X.affineOpens, ToType (openSections (chart X V) (D.mod V)
    (V.1 : X.Opens))) : Prop :=
  ∀ {V W : X.affineOpens} (h : V ≤ W),
    localAppFun (D.comp h).hom (V.1 : X.Opens) le_rfl (s V) =
      ((Scheme.Modules.pushforward (chart X W)).obj (D.mod W)).val.map
        (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op (s W)

variable (D)

/-- **The lift at a larger chart reads on a smaller one as the member of the family there.** Over
an open `P` inside an affine open `k` below `V`, the lift of the member of the family at `V`,
restricted to `P` and read on the chart of `k`, is the restriction to `P` of the member of the
family at `k`. -/
theorem chartSec_res_chartLift_of_le
    {s : ∀ V : X.affineOpens, ToType (openSections (chart X V) (D.mod V) (V.1 : X.Opens))}
    (hs : IsMatched s) {k V : X.affineOpens} (h : k ≤ V) {P : X.Opens}
    (hP : P ≤ (k.1 : X.Opens)) :
    D.chartSec k P (D.glued.val.map
          (homOfLE (hP.trans (show (k.1 : X.Opens) ≤ (V.1 : X.Opens) from h))).op
            (D.chartLift V (s V)))
      = ((Scheme.Modules.pushforward (chart X k)).obj (D.mod k)).val.map (homOfLE hP).op (s k) := by
  have hPV : P ≤ (V.1 : X.Opens) := hP.trans h
  refine localAppFun_hom_injective (D.comp h) hP ?_
  have e1 : localAppFun (D.comp h).hom P hP
        (D.chartSec k P (D.glued.val.map (homOfLE hPV).op (D.chartLift V (s V))))
      = D.chartSec V P (D.glued.val.map (homOfLE hPV).op (D.chartLift V (s V))) :=
    D.localAppFun_comp_chartSec h hP _
  have e2 : D.chartSec V P (D.glued.val.map (homOfLE hPV).op (D.chartLift V (s V)))
      = ((Scheme.Modules.pushforward (chart X V)).obj (D.mod V)).val.map (homOfLE hPV).op
          (s V) := by
    rw [D.chartSec_naturality V hPV, D.chartSec_chartLift V (s V)]
  have e3 : ((Scheme.Modules.pushforward (chart X V)).obj (D.mod V)).val.map (homOfLE hPV).op
        (s V)
      = localAppFun (D.comp h).hom P hP
          (((Scheme.Modules.pushforward (chart X k)).obj (D.mod k)).val.map
            (homOfLE hP).op (s k)) := by
    rw [← localAppFun_naturality (D.comp h).hom le_rfl hP (homOfLE hP) (s k), hs h, val_map_map]
  exact (e1.trans e2).trans e3

/-- **The lifts of a matched family agree on the overlaps.** For affine opens `V` and `W`, the
lifts of the members of the family at `V` and at `W` have the same restriction to `V ⊓ W`. -/
theorem res_chartLift_eq
    {s : ∀ V : X.affineOpens, ToType (openSections (chart X V) (D.mod V) (V.1 : X.Opens))}
    (hs : IsMatched s) (V W : X.affineOpens) :
    D.glued.val.map
        (homOfLE (inf_le_left : (V.1 : X.Opens) ⊓ (W.1 : X.Opens) ≤ (V.1 : X.Opens))).op
          (D.chartLift V (s V))
      = D.glued.val.map
          (homOfLE (inf_le_right : (V.1 : X.Opens) ⊓ (W.1 : X.Opens) ≤ (W.1 : X.Opens))).op
            (D.chartLift W (s W)) := by
  refine D.glued.isSheaf.section_ext (U := op ((V.1 : X.Opens) ⊓ (W.1 : X.Opens))) ?_
  intro p hp
  have hpVW : p ∈ (chart X V).opensRange ⊓ (chart X W).opensRange := by
    rw [opensRange_chart, opensRange_chart]
    exact hp
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (locallyDirected V W hpVW)
  have hpk : p ∈ (k.1.1 : X.Opens) := by
    have h' := hk
    rwa [opensRange_chart] at h'
  refine ⟨((V.1 : X.Opens) ⊓ (W.1 : X.Opens)) ⊓ (k.1.1 : X.Opens), inf_le_left, ⟨hp, hpk⟩, ?_⟩
  have hPk : ((V.1 : X.Opens) ⊓ (W.1 : X.Opens)) ⊓ (k.1.1 : X.Opens) ≤ (k.1.1 : X.Opens) :=
    inf_le_right
  have eV := val_map_map D.glued
    (inf_le_left : (V.1 : X.Opens) ⊓ (W.1 : X.Opens) ≤ (V.1 : X.Opens))
    (inf_le_left : ((V.1 : X.Opens) ⊓ (W.1 : X.Opens)) ⊓ (k.1.1 : X.Opens)
      ≤ (V.1 : X.Opens) ⊓ (W.1 : X.Opens)) (D.chartLift V (s V))
  have eW := val_map_map D.glued
    (inf_le_right : (V.1 : X.Opens) ⊓ (W.1 : X.Opens) ≤ (W.1 : X.Opens))
    (inf_le_left : ((V.1 : X.Opens) ⊓ (W.1 : X.Opens)) ⊓ (k.1.1 : X.Opens)
      ≤ (V.1 : X.Opens) ⊓ (W.1 : X.Opens)) (D.chartLift W (s W))
  have emid := D.chartSec_injective k.1 hPk
    ((D.chartSec_res_chartLift_of_le hs k.2.1 hPk).trans
      (D.chartSec_res_chartLift_of_le hs k.2.2 hPk).symm)
  exact eV.trans (emid.trans eW.symm)

/-! ### The glued section -/

/-- The sections of the glued module over the opens of `X`, as a sheaf of `O_X`-modules on `⊤`.
-/
private def gluedPre : OModuleLocalPresheaf X.ringCatSheaf ⊤ :=
  OModuleLocalPresheaf.ofSheafOfModules D.glued ⊤

/-- The sections of the glued module over the opens of `X` satisfy the sheaf condition. -/
private theorem gluedPre_isSheaf : (D.gluedPre).toLocalPresheaf.IsSheaf :=
  OModuleLocalPresheaf.isSheaf_ofSheafOfModules _ _

/-- **A family of sections of the charts, matched by the comparisons, comes from a global section
of the glued module**: there is a section over `⊤` which reads on the chart of each affine open as
the member of the family there. -/
theorem exists_section (D : ChartComparison X)
    (s : ∀ V : X.affineOpens, ToType (openSections (chart X V) (D.mod V) (V.1 : X.Opens)))
    (hs : ∀ {V W : X.affineOpens} (h : V ≤ W),
      localAppFun (D.comp h).hom (V.1 : X.Opens) le_rfl (s V) =
        ((Scheme.Modules.pushforward (chart X W)).obj (D.mod W)).val.map
          (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op (s W)) :
    ∃ t : ToType (D.glued.val.obj (op ⊤)),
      ∀ V : X.affineOpens,
        D.chartSec V (V.1 : X.Opens) (D.glued.val.map (homOfLE le_top).op t) = s V := by
  have hmatched : IsMatched s := fun h => hs h
  have hcov : (⊤ : X.Opens) ≤ ⨆ V : X.affineOpens, (V.1 : X.Opens) :=
    (AlgebraicGeometry.iSup_affineOpens_eq_top X).ge
  obtain ⟨t, ht⟩ : ∃ t : ToType (D.glued.val.obj (op ⊤)), ∀ V : X.affineOpens,
      D.glued.val.map (homOfLE le_top).op t = D.chartLift V (s V) :=
    ⟨D.gluedPre_isSheaf.glue (le_refl (⊤ : X.Opens))
      (fun V : X.affineOpens => (V.1 : X.Opens)) (fun _ => le_top) hcov
      (fun V => D.chartLift V (s V)) (fun V W => D.res_chartLift_eq hmatched V W),
      D.gluedPre_isSheaf.map_glue (le_refl (⊤ : X.Opens))
      (fun V : X.affineOpens => (V.1 : X.Opens)) (fun _ => le_top) hcov
      (fun V => D.chartLift V (s V)) (fun V W => D.res_chartLift_eq hmatched V W)⟩
  exact ⟨t, fun V => by rw [ht, D.chartSec_chartLift]⟩

/-- **Uniqueness.** Two sections of the glued module over `⊤` which read the same on the chart of
every affine open are equal. -/
theorem section_ext (D : ChartComparison X) {t t' : ToType (D.glued.val.obj (op ⊤))}
    (h : ∀ V : X.affineOpens,
      D.chartSec V (V.1 : X.Opens) (D.glued.val.map (homOfLE le_top).op t)
        = D.chartSec V (V.1 : X.Opens) (D.glued.val.map (homOfLE le_top).op t')) :
    t = t' := by
  refine D.glued.isSheaf.section_ext (U := op (⊤ : X.Opens)) ?_
  intro p _
  obtain ⟨V, hpV⟩ := exists_mem_affineOpens p
  exact ⟨(V.1 : X.Opens), le_top, hpV, D.chartSec_injective V le_rfl (h V)⟩

end ChartComparison

end AlgebraicGeometry.AffineOpensGlue

end
