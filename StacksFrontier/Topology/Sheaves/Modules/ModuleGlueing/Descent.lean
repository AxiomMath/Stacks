module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic
/-!
# Glueing sheaves of modules along a locally directed cover

`Stacks.SheafOfModules.ModulesGlueData` — the shape in which Stacks 00AM is consumed in algebraic
geometry — asks for *pairwise* transition data: for every two charts `f i`, `f j` of the cover and
every open `V` of the base lying in the images of both, a comparison of the sections of `mod i` and
`mod j` over `V`. A relative `Proj`, however, is glued over a **locally directed** cover: its
charts are the projective spectra of the graded section rings over the affine opens `W` of the
base, and the comparison morphism of charts
`Stacks.RelativeProj.Situation.projInclusionMap` exists only for an *inclusion* `W ≤ W'` of affine
opens. Since `W ⊓ W'` need not be affine there is no chart over it, and hence no comparison of the
charts over `W` and `W'` to be read off.

The content of this file is a descent step for comparison isomorphisms: a family of
comparisons defined over the members of a covering family, agreeing wherever two of them are
defined, glues to a single comparison over every open — the sheaf condition for the two sheaves
being compared is all that is needed. Applied to the family of charts lying *below* both `i` and
`j`, it turns directed transition data into the pairwise transition data that
`ModulesGlueData` requires.

## Main definitions

* `Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv`: a family of `O`-linear comparison
  isomorphisms between two sheaves of `O`-modules on an open `U`, one over each member of a
  covering family of `U`, any two of them agreeing wherever both are defined.
* `Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv.glueLinearEquiv`: the comparison
  isomorphism glued from such a family, over an arbitrary open `V ≤ U`.
* `Stacks.SheafOfModules.ModulesDirectedGlueData`: locally directed glueing data of sheaves of
  modules on a scheme — a sheaf of modules on each chart together with a comparison for each
  *inclusion* `i ≤ j` of charts, functorial in the inclusion, over a cover whose pairwise overlaps
  are covered by the charts lying below both.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.pairTrans`: the pairwise transition isomorphism
  over an arbitrary open lying in two charts, glued from the comparisons through the charts below
  both.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.toModulesGlueData`: the resulting pairwise
  glueing datum, and hence (through `ModulesGlueData.glued`) the glued sheaf of modules.

## Main results

* `TopCat.Sheaf.LocalPresheaf.IsSheaf.glue`: the section glued from a compatible family, extracted
  from the sheaf condition.
* `Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv.glueLinearEquiv_eq`: the glued comparison
  agrees with the `k`-th comparison over any open contained in the `k`-th member of the covering
  family. This characterisation, together with the separation half of the sheaf condition, is what
  every property of the glued comparison is proved from.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.pairEquiv_eq_of_le`: passing through a smaller
  chart gives the same comparison. This is the content of the functoriality of the directed data,
  and it is what makes the comparisons through two different charts below `i` and `j` agree.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.pairTrans_eq`: the glued pairwise transition
  isomorphism is the comparison through `k`, over any open lying in a chart `k` below both.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.chartIso`: the glued sheaf of modules restricts
  along each chart to the module it was glued from.

## Implementation notes

The descent step is stated for `OModuleLocalPresheaf`, the semilinear presheaf-on-an-open of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/Basic.lean`, rather than for sheaves of
modules on a scheme, because that is the form in which the sheaf condition is available: the
sections of a
pushforward along a chart, read over the opens of the base, are
`OModuleLocalPresheaf.ofSheafOfModules`, and `OModuleLocalPresheaf.isSheaf_ofSheafOfModules` is its
sheaf condition. As there, every overlap is a single open of the base and no statement has to be
transported across an identification of opens.

Local directedness is asked for as the single inequality
`ModulesDirectedGlueData.locallyDirected`, with the charts below both `i` and `j` indexed by the
subtype `{k // k ≤ i ∧ k ≤ j}`; the three-chart version needed for the cocycle condition is
derived from it in `ModulesDirectedGlueData.locallyDirected₃`.

Note that the index preorder is *not* asked to be directed, nor to reflect the inclusion order of
the charts. Only the two consequences actually used are hypotheses: `opensRange_mono`, that `i ≤ j`
implies the `i`-th chart lies inside the `j`-th, and `locallyDirected`.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf.LocalPresheaf.IsSheaf

variable {X : TopCat.{u}} {U : Opens X} {F : LocalPresheaf X U}

/-- The section glued from a compatible family of local sections over a covering of `V` by opens
contained in `V`. -/
noncomputable def glue (hF : F.IsSheaf) {ι : Type u} {V : Opens X} (hV : V ≤ U) (B : ι → Opens X)
    (hBV : ∀ k, B k ≤ V) (hcov : V ≤ ⨆ k, B k) (s : ∀ k, F.obj (B k) ((hBV k).trans hV))
    (hs : ∀ k l, F.map (inf_le_left : B k ⊓ B l ≤ B k) (s k)
      = F.map (inf_le_right : B k ⊓ B l ≤ B l) (s l)) :
    F.obj V hV :=
  (hF hV B hBV hcov s hs).choose

/-- The glued section restricts on the `k`-th member of the covering to the `k`-th member of the
family it was glued from. -/
theorem map_glue (hF : F.IsSheaf) {ι : Type u} {V : Opens X} (hV : V ≤ U) (B : ι → Opens X)
    (hBV : ∀ k, B k ≤ V) (hcov : V ≤ ⨆ k, B k) (s : ∀ k, F.obj (B k) ((hBV k).trans hV))
    (hs : ∀ k l, F.map (inf_le_left : B k ⊓ B l ≤ B k) (s k)
      = F.map (inf_le_right : B k ⊓ B l ≤ B l) (s l)) (k : ι) :
    F.map (hBV k) (hF.glue hV B hBV hcov s hs) = s k :=
  (hF hV B hBV hcov s hs).choose_spec.1 k

end TopCat.Sheaf.LocalPresheaf.IsSheaf

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X}

/-- An open covered by a family is covered by its intersections with the members of the family. -/
private theorem le_iSup_inf_of_le_iSup {κ : Type*} {V : Opens X} {c : κ → Opens X}
    (h : V ≤ ⨆ k, c k) : V ≤ ⨆ k, V ⊓ c k :=
  le_trans (le_inf le_rfl h) (inf_iSup_eq V c).le

namespace OModuleLocalPresheaf

variable {U : Opens X} {F G : OModuleLocalPresheaf O U}

/-- A family of `O`-linear comparison isomorphisms between two sheaves of `O`-modules on `U`,
one over each member of a covering family of `U`, any two of them agreeing wherever both are
defined. -/
structure LocalEquiv (F G : OModuleLocalPresheaf O U) (ι : Type u) where
  /-- The opens over which the comparisons are given. -/
  cover : ι → Opens X
  /-- Each member of the family is contained in `U`. -/
  cover_le : ∀ k, cover k ≤ U
  /-- The family covers `U`. -/
  le_iSup_cover : U ≤ ⨆ k, cover k
  /-- The comparison over an open contained in the `k`-th member of the family. -/
  equiv : ∀ (k : ι) {V : Opens X} (hV : V ≤ cover k),
    F.obj V (hV.trans (cover_le k)) ≃ₗ[ToType (O.obj.obj (op V))]
      G.obj V (hV.trans (cover_le k))
  /-- The comparisons commute with the restriction maps. -/
  equiv_map : ∀ (k : ι) {V W : Opens X} (hV : V ≤ cover k) (hWV : W ≤ V)
      (t : F.obj V (hV.trans (cover_le k))),
    equiv k (hWV.trans hV) (F.map hWV t) = G.map hWV (equiv k hV t)
  /-- Any two comparisons agree wherever both are defined. -/
  equiv_agree : ∀ (k l : ι) {V : Opens X} (hk : V ≤ cover k) (hl : V ≤ cover l)
      (t : F.obj V (hk.trans (cover_le k))),
    equiv k hk t = equiv l hl t

namespace LocalEquiv

variable {ι : Type u} (E : LocalEquiv F G ι)

/-- The members of the covering family, cut down to an open `V ≤ U`, cover `V`. -/
theorem le_iSup_inf_cover {V : Opens X} (hV : V ≤ U) : V ≤ ⨆ k, V ⊓ E.cover k :=
  le_iSup_inf_of_le_iSup (hV.trans E.le_iSup_cover)

/-- Two sections over `V ≤ U` are equal as soon as they agree on each member of the covering
family. -/
theorem eq_of_locally_eq (hG : G.toLocalPresheaf.IsSheaf) {V : Opens X} {hV : V ≤ U}
    {a b : G.obj V hV}
    (h : ∀ k, G.map (inf_le_left : V ⊓ E.cover k ≤ V) a
      = G.map (inf_le_left : V ⊓ E.cover k ≤ V) b) : a = b :=
  hG.eq_of_locally_eq (fun k => V ⊓ E.cover k) (fun _ => inf_le_left) (E.le_iSup_inf_cover hV) h

/-- The comparison isomorphisms, read in the other direction. -/
noncomputable def symm : LocalEquiv G F ι where
  cover := E.cover
  cover_le := E.cover_le
  le_iSup_cover := E.le_iSup_cover
  equiv k _ hV := (E.equiv k hV).symm
  equiv_map k _ _ hV hWV t := by
    refine (E.equiv k (hWV.trans hV)).injective ?_
    rw [LinearEquiv.apply_symm_apply, E.equiv_map k hV hWV, LinearEquiv.apply_symm_apply]
  equiv_agree k l _ hk hl t := by
    refine (E.equiv l hl).injective ?_
    rw [LinearEquiv.apply_symm_apply, ← E.equiv_agree k l hk hl, LinearEquiv.apply_symm_apply]

/-- The covering family of the reversed comparison is that of the original one. -/
@[simp] theorem symm_cover : E.symm.cover = E.cover := rfl

/-- The comparisons of the reversed datum are the inverses of the original comparisons. -/
@[simp] theorem symm_equiv (k : ι) {V : Opens X} (hV : V ≤ E.cover k) :
    E.symm.equiv k hV = (E.equiv k hV).symm := rfl

/-- The local pieces of the glued comparison: the `k`-th one is the image under the `k`-th
comparison of the restriction of `t` to the `k`-th member of the covering family. -/
noncomputable def piece {V : Opens X} (hV : V ≤ U) (t : F.obj V hV) (k : ι) :
    G.obj (V ⊓ E.cover k) (inf_le_left.trans hV) :=
  E.equiv k (inf_le_right : V ⊓ E.cover k ≤ E.cover k) (F.map (inf_le_left : V ⊓ E.cover k ≤ V) t)

/-- The `k`-th local piece of `t` is the `k`-th comparison applied to the restriction of `t` to
`V ⊓ E.cover k`. -/
theorem piece_eq {V : Opens X} (hV : V ≤ U) (t : F.obj V hV) (k : ι) :
    E.piece hV t k = E.equiv k (inf_le_right : V ⊓ E.cover k ≤ E.cover k)
      (F.map (inf_le_left : V ⊓ E.cover k ≤ V) t) := rfl

/-- The restriction of a local piece of the glued comparison to a smaller open. -/
theorem map_piece {V : Opens X} (hV : V ≤ U) (t : F.obj V hV) (k : ι) {Z : Opens X}
    (hZ : Z ≤ V ⊓ E.cover k) :
    G.map hZ (E.piece hV t k)
      = E.equiv k (hZ.trans inf_le_right) (F.map (hZ.trans inf_le_left) t) := by
  rw [piece_eq, ← E.equiv_map, F.map_map]

/-- The local pieces of the glued comparison agree on the overlaps. -/
theorem piece_compat {V : Opens X} (hV : V ≤ U) (t : F.obj V hV) (k l : ι) :
    G.map (inf_le_left : (V ⊓ E.cover k) ⊓ (V ⊓ E.cover l) ≤ V ⊓ E.cover k) (E.piece hV t k)
      = G.map (inf_le_right : (V ⊓ E.cover k) ⊓ (V ⊓ E.cover l) ≤ V ⊓ E.cover l)
          (E.piece hV t l) := by
  rw [E.map_piece hV t k inf_le_left, E.map_piece hV t l inf_le_right]
  exact E.equiv_agree k l _ _ _

/-- The glued comparison, as a function on sections over an open `V ≤ U`. -/
noncomputable def glue (hG : G.toLocalPresheaf.IsSheaf) {V : Opens X} (hV : V ≤ U)
    (t : F.obj V hV) : G.obj V hV :=
  hG.glue hV (fun k => V ⊓ E.cover k) (fun _ => inf_le_left) (E.le_iSup_inf_cover hV)
    (E.piece hV t) (E.piece_compat hV t)

/-- The glued comparison restricts on the `k`-th member of the covering family to the `k`-th
local piece. -/
theorem map_glue (hG : G.toLocalPresheaf.IsSheaf) {V : Opens X} (hV : V ≤ U) (t : F.obj V hV)
    (k : ι) :
    G.map (inf_le_left : V ⊓ E.cover k ≤ V) (E.glue hG hV t) = E.piece hV t k :=
  hG.map_glue hV (fun k => V ⊓ E.cover k) (fun _ => inf_le_left) (E.le_iSup_inf_cover hV)
    (E.piece hV t) (E.piece_compat hV t) k

/-- The glued comparison, read on an open contained in a member of the covering family. -/
theorem map_glue_le (hG : G.toLocalPresheaf.IsSheaf) {V Z : Opens X} (hV : V ≤ U)
    (t : F.obj V hV) (k : ι) (hZ : Z ≤ V ⊓ E.cover k) :
    G.map (hZ.trans (inf_le_left : V ⊓ E.cover k ≤ V)) (E.glue hG hV t)
      = E.equiv k (hZ.trans inf_le_right) (F.map (hZ.trans inf_le_left) t) := by
  rw [← G.map_map (inf_le_left : V ⊓ E.cover k ≤ V) hZ, E.map_glue hG hV t k, E.map_piece]

/-- **The glued comparison agrees with the `k`-th comparison** over any open contained in the
`k`-th member of the covering family. -/
theorem glue_eq_equiv (hG : G.toLocalPresheaf.IsSheaf) (k : ι) {V : Opens X} (hV : V ≤ E.cover k)
    (t : F.obj V (hV.trans (E.cover_le k))) :
    E.glue hG (hV.trans (E.cover_le k)) t = E.equiv k hV t := by
  refine E.eq_of_locally_eq hG fun l => ?_
  rw [E.map_glue hG _ t l, piece_eq, ← E.equiv_map k hV (inf_le_left : V ⊓ E.cover l ≤ V)]
  exact (E.equiv_agree k l _ _ _).symm

/-- The glued comparison commutes with the restriction maps. -/
theorem glue_map (hG : G.toLocalPresheaf.IsSheaf) {V W : Opens X} (hV : V ≤ U) (hWV : W ≤ V)
    (t : F.obj V hV) :
    E.glue hG (hWV.trans hV) (F.map hWV t) = G.map hWV (E.glue hG hV t) := by
  refine E.eq_of_locally_eq hG fun k => ?_
  rw [E.map_glue hG (hWV.trans hV) (F.map hWV t) k, piece_eq, F.map_map, G.map_map]
  exact (E.map_glue_le hG hV t k (le_inf (inf_le_left.trans hWV) inf_le_right)).symm

/-- The glued comparison is additive. -/
theorem glue_add (hG : G.toLocalPresheaf.IsSheaf) {V : Opens X} (hV : V ≤ U)
    (t₁ t₂ : F.obj V hV) :
    E.glue hG hV (t₁ + t₂) = E.glue hG hV t₁ + E.glue hG hV t₂ := by
  refine E.eq_of_locally_eq hG fun k => ?_
  rw [map_add, E.map_glue hG hV _ k, E.map_glue hG hV t₁ k, E.map_glue hG hV t₂ k,
    piece_eq, piece_eq, piece_eq, map_add, map_add]

/-- The glued comparison is linear over the functions on `V`. -/
theorem glue_smul (hG : G.toLocalPresheaf.IsSheaf) {V : Opens X} (hV : V ≤ U)
    (r : ToType (O.obj.obj (op V))) (t : F.obj V hV) :
    E.glue hG hV (r • t) = r • E.glue hG hV t := by
  refine E.eq_of_locally_eq hG fun k => ?_
  rw [map_smulₛₗ, E.map_glue hG hV _ k, E.map_glue hG hV t k, piece_eq, piece_eq, map_smulₛₗ,
    map_smul]

/-- **The glued comparison isomorphism.** A family of comparison isomorphisms over the members of
a covering family of `U`, agreeing wherever two of them are defined, glues to a single comparison
isomorphism over every open `V ≤ U`. -/
noncomputable def glueLinearEquiv (hF : F.toLocalPresheaf.IsSheaf)
    (hG : G.toLocalPresheaf.IsSheaf) {V : Opens X} (hV : V ≤ U) :
    F.obj V hV ≃ₗ[ToType (O.obj.obj (op V))] G.obj V hV where
  toFun := E.glue hG hV
  map_add' := E.glue_add hG hV
  map_smul' := E.glue_smul hG hV
  invFun := E.symm.glue hF hV
  left_inv t := E.symm.eq_of_locally_eq hF fun k =>
    (E.symm.map_glue hF hV _ k).trans ((congrArg (E.equiv k _).symm (E.map_glue hG hV t k)).trans
      (LinearEquiv.symm_apply_apply _ _))
  right_inv u := E.eq_of_locally_eq hG fun k =>
    (E.map_glue hG hV _ k).trans ((congrArg (E.equiv k _) (E.symm.map_glue hF hV u k)).trans
      (LinearEquiv.apply_symm_apply _ _))

/-- The glued comparison isomorphism acts on sections as the glued comparison map `E.glue`. -/
theorem glueLinearEquiv_apply (hF : F.toLocalPresheaf.IsSheaf) (hG : G.toLocalPresheaf.IsSheaf)
    {V : Opens X} (hV : V ≤ U) (t : F.obj V hV) :
    E.glueLinearEquiv hF hG hV t = E.glue hG hV t := rfl

/-- **The glued comparison isomorphism agrees with the `k`-th comparison** over any open contained
in the `k`-th member of the covering family. -/
theorem glueLinearEquiv_eq (hF : F.toLocalPresheaf.IsSheaf) (hG : G.toLocalPresheaf.IsSheaf)
    (k : ι) {V : Opens X} (hV : V ≤ E.cover k) (t : F.obj V (hV.trans (E.cover_le k))) :
    E.glueLinearEquiv hF hG (hV.trans (E.cover_le k)) t = E.equiv k hV t :=
  E.glue_eq_equiv hG k hV t

/-- The glued comparison isomorphism commutes with the restriction maps. -/
theorem glueLinearEquiv_map (hF : F.toLocalPresheaf.IsSheaf) (hG : G.toLocalPresheaf.IsSheaf)
    {V W : Opens X} (hV : V ≤ U) (hWV : W ≤ V) (t : F.obj V hV) :
    E.glueLinearEquiv hF hG (hWV.trans hV) (F.map hWV t)
      = G.map hWV (E.glueLinearEquiv hF hG hV t) :=
  E.glue_map hG hV hWV t

end LocalEquiv

end OModuleLocalPresheaf

/-! ### Locally directed glueing data of sheaves of modules on a scheme -/

section Scheme

open AlgebraicGeometry

variable {S : Scheme.{u}} {ι : Type u} [Preorder ι] {Y : ι → Scheme.{u}}

/-- Locally directed glueing data of sheaves of modules on a scheme `S` along a family of open
immersions `f i : Y i ⟶ S`: a sheaf of modules on each `Y i`, together with a comparison
isomorphism for each *inclusion* `i ≤ j` of charts, functorial in the inclusion.

This is the shape in which transition data actually arises for a relative `Proj`, whose charts are
indexed by the affine opens of the base and compared only along inclusions of affine opens. The
cover is not asked to be pairwise directed, only *locally* so: the overlap of two charts need only
be covered by the charts lying below both of them. -/
structure ModulesDirectedGlueData (S : Scheme.{u}) {ι : Type u} [Preorder ι]
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)] where
  /-- The sheaf of modules on the `i`-th chart. -/
  mod : ∀ i, (Y i).Modules
  /-- The `i`-th chart lies inside the `j`-th whenever `i ≤ j`. -/
  opensRange_mono : ∀ {i j : ι}, i ≤ j → (f i).opensRange ≤ (f j).opensRange
  /-- The cover is locally directed: the overlap of the `i`-th and `j`-th charts is covered by the
  charts lying below both. -/
  locallyDirected : ∀ i j : ι, (f i).opensRange ⊓ (f j).opensRange
    ≤ ⨆ k : {k : ι // k ≤ i ∧ k ≤ j}, (f k.1).opensRange
  /-- The comparison attached to an inclusion `i ≤ j` of charts, on sections over an open
  contained in the `i`-th chart and linear over the functions there. -/
  trans : ∀ {i j : ι} (_h : i ≤ j) {V : S.Opens} (_hV : V ≤ (f i).opensRange),
    openSections (f i) (mod i) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (f j) (mod j) V
  /-- The comparisons commute with the restriction maps. -/
  trans_map : ∀ {i j : ι} (h : i ≤ j) {V W : S.Opens} (hV : V ≤ (f i).opensRange) (hWV : W ≤ V)
      (t : ToType (openSections (f i) (mod i) V)),
    trans h (hWV.trans hV)
        (((Scheme.Modules.pushforward (f i)).obj (mod i)).val.map (homOfLE hWV).op t)
      = ((Scheme.Modules.pushforward (f j)).obj (mod j)).val.map (homOfLE hWV).op (trans h hV t)
  /-- The comparisons are functorial in the inclusion. -/
  trans_trans : ∀ {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) {V : S.Opens}
      (hV : V ≤ (f i).opensRange) (t : ToType (openSections (f i) (mod i) V)),
    trans hjk (hV.trans (opensRange_mono hij)) (trans hij hV t) = trans (hij.trans hjk) hV t

namespace ModulesDirectedGlueData

variable {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)] (D : ModulesDirectedGlueData S f)

/-- The sections of the `i`-th chart's module, read as a sheaf of `O_S`-modules on an open `U` of
the base. -/
noncomputable abbrev pre (i : ι) (U : S.Opens) : OModuleLocalPresheaf S.ringCatSheaf U :=
  OModuleLocalPresheaf.ofSheafOfModules ((Scheme.Modules.pushforward (f i)).obj (D.mod i)) U

/-- The sections of the `i`-th chart's module over the opens of the base form a sheaf. -/
theorem pre_isSheaf (i : ι) (U : S.Opens) : (D.pre i U).toLocalPresheaf.IsSheaf :=
  OModuleLocalPresheaf.isSheaf_ofSheafOfModules _ _

/-- Restriction of the sections of the `i`-th chart's module, read over the opens of the base.
This is the restriction map appearing in the `trans_map` fields of
`Stacks.SheafOfModules.ModulesDirectedGlueData` and
`Stacks.SheafOfModules.ModulesGlueData`. -/
noncomputable abbrev res (i : ι) {V W : S.Opens} (hWV : W ≤ V)
    (t : ToType (openSections (f i) (D.mod i) V)) : ToType (openSections (f i) (D.mod i) W) :=
  ((Scheme.Modules.pushforward (f i)).obj (D.mod i)).val.map (homOfLE hWV).op t

/-- Restriction in `pre` is the restriction of sections. -/
theorem pre_map (i : ι) (U : S.Opens) {V W : S.Opens} {hV : V ≤ U} (hWV : W ≤ V)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    (D.pre i U).map (hV := hV) hWV t = D.res i hWV t := rfl

include D in
/-- The overlap of three charts is covered by the charts lying below all three. -/
theorem locallyDirected₃ (i j k : ι) :
    (f i).opensRange ⊓ (f j).opensRange ⊓ (f k).opensRange
      ≤ ⨆ m : {m : ι // m ≤ i ∧ m ≤ j ∧ m ≤ k}, (f m.1).opensRange := by
  intro x hx
  obtain ⟨p, hxp⟩ := TopologicalSpace.Opens.mem_iSup.mp (D.locallyDirected i j hx.1)
  obtain ⟨q, hxq⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (D.locallyDirected p.1 k ⟨hxp, hx.2⟩)
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨q.1, q.2.1.trans p.2.1, q.2.1.trans p.2.2, q.2.2⟩, hxq⟩

include D in
/-- An open contained in two charts is covered by its intersections with the charts lying below
both. -/
theorem le_iSup_inf_opensRange {i j : ι} {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) :
    V ≤ ⨆ m : {m : ι // m ≤ i ∧ m ≤ j}, V ⊓ (f m.1).opensRange :=
  le_iSup_inf_of_le_iSup ((le_inf hi hj).trans (D.locallyDirected i j))

include D in
/-- An open contained in three charts is covered by its intersections with the charts lying below
all three. -/
theorem le_iSup_inf_opensRange₃ {i j k : ι} {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange) :
    V ≤ ⨆ m : {m : ι // m ≤ i ∧ m ≤ j ∧ m ≤ k}, V ⊓ (f m.1).opensRange :=
  le_iSup_inf_of_le_iSup ((le_inf (le_inf hi hj) hk).trans (D.locallyDirected₃ i j k))

/-- **The comparison attached to the identity inclusion is the identity.** Functoriality at
`i ≤ i ≤ i` says that the comparison attached to `le_rfl` is idempotent, and it is a bijection,
so it is the identity. (The two inequality arguments appearing there are proofs of the same
proposition as the one given, hence identified by proof irrelevance.) -/
theorem trans_rfl {i : ι} {V : S.Opens} (hV : V ≤ (f i).opensRange)
    (t : ToType (openSections (f i) (D.mod i) V)) : D.trans (le_refl i) hV t = t :=
  (D.trans (le_refl i) hV).injective (D.trans_trans (le_refl i) (le_refl i) hV t)

/-! #### Comparing two charts through a chart below both -/

/-- The comparison of the `i`-th and `j`-th charts obtained by passing through a chart `k` below
both of them, on sections over an open contained in the `k`-th chart. -/
noncomputable def pairEquiv {i j : ι} (k : ι) (hki : k ≤ i) (hkj : k ≤ j) {V : S.Opens}
    (hV : V ≤ (f k).opensRange) :
    openSections (f i) (D.mod i) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (f j) (D.mod j) V :=
  (D.trans hki hV).symm.trans (D.trans hkj hV)

/-- The comparison through the `k`-th chart sends `t` to the image under `D.trans hkj hV` of the
preimage of `t` under `D.trans hki hV`. -/
theorem pairEquiv_apply {i j : ι} (k : ι) (hki : k ≤ i) (hkj : k ≤ j) {V : S.Opens}
    (hV : V ≤ (f k).opensRange) (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairEquiv k hki hkj hV t = D.trans hkj hV ((D.trans hki hV).symm t) := rfl

/-- The inverse of a comparison also commutes with the restriction maps. -/
theorem trans_symm_map {i j : ι} (h : i ≤ j) {V W : S.Opens} (hV : V ≤ (f i).opensRange)
    (hWV : W ≤ V) (t : ToType (openSections (f j) (D.mod j) V)) :
    (D.trans h (hWV.trans hV)).symm (D.res j hWV t) = D.res i hWV ((D.trans h hV).symm t) :=
  (LinearEquiv.symm_apply_eq _).mpr
    ((congrArg (D.res j hWV) (LinearEquiv.apply_symm_apply (D.trans h hV) t).symm).trans
      (D.trans_map h hV hWV ((D.trans h hV).symm t)).symm)

/-- A comparison through a chart below both commutes with the restriction maps. -/
theorem pairEquiv_map {i j : ι} (k : ι) (hki : k ≤ i) (hkj : k ≤ j) {V W : S.Opens}
    (hV : V ≤ (f k).opensRange) (hWV : W ≤ V)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairEquiv k hki hkj (hWV.trans hV) (D.res i hWV t)
      = D.res j hWV (D.pairEquiv k hki hkj hV t) :=
  (congrArg (D.trans hkj (hWV.trans hV)) (D.trans_symm_map hki hV hWV t)).trans
    (D.trans_map hkj hV hWV ((D.trans hki hV).symm t))

/-- **Passing through a smaller chart gives the same comparison.** -/
theorem pairEquiv_eq_of_le {i j k m : ι} (hki : k ≤ i) (hkj : k ≤ j) (hmk : m ≤ k)
    (hmi : m ≤ i) (hmj : m ≤ j) {V : S.Opens} (hV : V ≤ (f m).opensRange)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairEquiv k hki hkj (hV.trans (D.opensRange_mono hmk)) t = D.pairEquiv m hmi hmj hV t := by
  have h1 : (D.trans hki (hV.trans (D.opensRange_mono hmk))).symm t
      = D.trans hmk hV ((D.trans hmi hV).symm t) :=
    (LinearEquiv.symm_apply_eq _).mpr ((LinearEquiv.apply_symm_apply (D.trans hmi hV) t).symm.trans
      (D.trans_trans hmk hki hV ((D.trans hmi hV).symm t)).symm)
  rw [pairEquiv_apply, pairEquiv_apply, h1]
  exact D.trans_trans hmk hkj hV ((D.trans hmi hV).symm t)

/-- **Two comparisons through charts below both `i` and `j` agree** over an open contained in a
chart below both of those. -/
theorem pairEquiv_eq_pairEquiv {i j k l m : ι} (hki : k ≤ i) (hkj : k ≤ j) (hli : l ≤ i)
    (hlj : l ≤ j) (hmk : m ≤ k) (hml : m ≤ l) {V : S.Opens} (hV : V ≤ (f m).opensRange)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairEquiv k hki hkj (hV.trans (D.opensRange_mono hmk)) t
      = D.pairEquiv l hli hlj (hV.trans (D.opensRange_mono hml)) t :=
  (D.pairEquiv_eq_of_le hki hkj hmk (hmk.trans hki) (hmk.trans hkj) hV t).trans
    (D.pairEquiv_eq_of_le hli hlj hml (hmk.trans hki) (hmk.trans hkj) hV t).symm

/-- Composing the comparisons through one and the same chart below `i`, `j` and `k`. -/
theorem pairEquiv_pairEquiv {i j k m : ι} (hmi : m ≤ i) (hmj : m ≤ j) (hmk : m ≤ k)
    {V : S.Opens} (hV : V ≤ (f m).opensRange)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairEquiv m hmj hmk hV (D.pairEquiv m hmi hmj hV t) = D.pairEquiv m hmi hmk hV t :=
  congrArg (D.trans hmk hV) (LinearEquiv.symm_apply_apply (D.trans hmj hV) _)

/-! #### Descent to pairwise transition data -/

/-- The comparisons through the charts below both `i` and `j`, as a local comparison datum on the
overlap of the `i`-th and `j`-th charts. The agreement condition is `pairEquiv_eq_pairEquiv`,
checked on a cover and propagated by the sheaf condition. -/
noncomputable def pairLocalEquiv (i j : ι) :
    OModuleLocalPresheaf.LocalEquiv (D.pre i ((f i).opensRange ⊓ (f j).opensRange))
      (D.pre j ((f i).opensRange ⊓ (f j).opensRange)) {k : ι // k ≤ i ∧ k ≤ j} where
  cover k := (f k.1).opensRange
  cover_le k := le_inf (D.opensRange_mono k.2.1) (D.opensRange_mono k.2.2)
  le_iSup_cover := D.locallyDirected i j
  equiv k _ hV := D.pairEquiv k.1 k.2.1 k.2.2 hV
  equiv_map k _ _ hV hWV t := D.pairEquiv_map k.1 k.2.1 k.2.2 hV hWV t
  equiv_agree k l V hk hl t := by
    have key : ∀ m : {m : ι // m ≤ k.1 ∧ m ≤ l.1},
        D.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) (D.pairEquiv k.1 k.2.1 k.2.2 hk t)
          = D.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
              (D.pairEquiv l.1 l.2.1 l.2.2 hl t) := fun m =>
      ((D.pairEquiv_map k.1 k.2.1 k.2.2 hk
            (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t).symm.trans
          (D.pairEquiv_eq_pairEquiv k.2.1 k.2.2 l.2.1 l.2.2 m.2.1 m.2.2
            (inf_le_right : V ⊓ (f m.1).opensRange ≤ (f m.1).opensRange)
            (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t))).trans
        (D.pairEquiv_map l.1 l.2.1 l.2.2 hl (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t)
    exact (D.pre_isSheaf j ((f i).opensRange ⊓ (f j).opensRange)).eq_of_locally_eq
      (hV := hk.trans (le_inf (D.opensRange_mono k.2.1) (D.opensRange_mono k.2.2)))
      (fun m : {m : ι // m ≤ k.1 ∧ m ≤ l.1} => V ⊓ (f m.1).opensRange) (fun _ => inf_le_left)
      (D.le_iSup_inf_opensRange hk hl) key

/-- **The pairwise transition isomorphism**, over an *arbitrary* open contained in both the `i`-th
and the `j`-th chart: glued from the comparisons through the charts lying below both. This is the
step the pairwise form of Stacks 00AM needs and a locally directed cover does not supply
directly. -/
noncomputable def pairTrans (i j : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange ⊓ (f j).opensRange) :
    openSections (f i) (D.mod i) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (f j) (D.mod j) V :=
  (D.pairLocalEquiv i j).glueLinearEquiv (D.pre_isSheaf i _) (D.pre_isSheaf j _) hV

/-- **The pairwise transition isomorphism is the comparison through `k`** over an open contained
in a chart `k` below both `i` and `j`. -/
theorem pairTrans_eq (i j : ι) {k : ι} (hki : k ≤ i) (hkj : k ≤ j) {V : S.Opens}
    (hV : V ≤ (f k).opensRange) (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairTrans i j (hV.trans (le_inf (D.opensRange_mono hki) (D.opensRange_mono hkj))) t
      = D.pairEquiv k hki hkj hV t :=
  (D.pairLocalEquiv i j).glueLinearEquiv_eq (D.pre_isSheaf i _) (D.pre_isSheaf j _)
    ⟨k, hki, hkj⟩ hV t

/-- **The pairwise transition isomorphism down to a chart below is the inverse of the comparison
attached to that inclusion**, over an open lying in the smaller chart. This is `pairTrans_eq` at
`k = j`, where the second leg of the comparison through `k` is the identity. -/
theorem pairTrans_eq_trans_symm {i j : ι} (hji : j ≤ i) {V : S.Opens}
    (hV : V ≤ (f j).opensRange) (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairTrans i j (le_inf (hV.trans (D.opensRange_mono hji)) hV) t = (D.trans hji hV).symm t :=
  (D.pairTrans_eq i j hji le_rfl hV t).trans (D.trans_rfl hV ((D.trans hji hV).symm t))

/-- The pairwise transition isomorphism commutes with the restriction maps. -/
theorem pairTrans_map (i j : ι) {V W : S.Opens}
    (hV : V ≤ (f i).opensRange ⊓ (f j).opensRange) (hWV : W ≤ V)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairTrans i j (hWV.trans hV) (D.res i hWV t) = D.res j hWV (D.pairTrans i j hV t) :=
  (D.pairLocalEquiv i j).glueLinearEquiv_map (D.pre_isSheaf i _) (D.pre_isSheaf j _) hV hWV t

/-- The cocycle condition for the pairwise transition isomorphisms. -/
theorem pairTrans_pairTrans (i j k : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    D.pairTrans j k (le_inf hj hk) (D.pairTrans i j (le_inf hi hj) t)
      = D.pairTrans i k (le_inf hi hk) t := by
  have key : ∀ m : {m : ι // m ≤ i ∧ m ≤ j ∧ m ≤ k},
      D.res k (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
          (D.pairTrans j k (le_inf hj hk) (D.pairTrans i j (le_inf hi hj) t))
        = D.res k (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
            (D.pairTrans i k (le_inf hi hk) t) := fun m => by
    calc D.res k (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
            (D.pairTrans j k (le_inf hj hk) (D.pairTrans i j (le_inf hi hj) t))
        = D.pairTrans j k (inf_le_left.trans (le_inf hj hk))
            (D.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
              (D.pairTrans i j (le_inf hi hj) t)) :=
          (D.pairTrans_map j k (le_inf hj hk) inf_le_left _).symm
      _ = D.pairTrans j k (inf_le_left.trans (le_inf hj hk))
            (D.pairTrans i j (inf_le_left.trans (le_inf hi hj))
              (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t)) :=
          congrArg (D.pairTrans j k (inf_le_left.trans (le_inf hj hk)))
            (D.pairTrans_map i j (le_inf hi hj) inf_le_left t).symm
      _ = D.pairTrans j k (inf_le_left.trans (le_inf hj hk))
            (D.pairEquiv m.1 m.2.1 m.2.2.1
              (inf_le_right : V ⊓ (f m.1).opensRange ≤ (f m.1).opensRange)
              (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t)) :=
          congrArg (D.pairTrans j k (inf_le_left.trans (le_inf hj hk)))
            (D.pairTrans_eq i j m.2.1 m.2.2.1 inf_le_right _)
      _ = D.pairEquiv m.1 m.2.2.1 m.2.2.2
            (inf_le_right : V ⊓ (f m.1).opensRange ≤ (f m.1).opensRange)
            (D.pairEquiv m.1 m.2.1 m.2.2.1 inf_le_right
              (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t)) :=
          D.pairTrans_eq j k m.2.2.1 m.2.2.2 inf_le_right _
      _ = D.pairEquiv m.1 m.2.1 m.2.2.2 inf_le_right
            (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t) :=
          D.pairEquiv_pairEquiv m.2.1 m.2.2.1 m.2.2.2 inf_le_right _
      _ = D.pairTrans i k (inf_le_left.trans (le_inf hi hk))
            (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t) :=
          (D.pairTrans_eq i k m.2.1 m.2.2.2 inf_le_right _).symm
      _ = D.res k (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
            (D.pairTrans i k (le_inf hi hk) t) :=
          D.pairTrans_map i k (le_inf hi hk) inf_le_left t
  exact (D.pre_isSheaf k ((f i).opensRange ⊓ (f k).opensRange)).eq_of_locally_eq
    (hV := le_inf hi hk)
    (fun m : {m : ι // m ≤ i ∧ m ≤ j ∧ m ≤ k} => V ⊓ (f m.1).opensRange) (fun _ => inf_le_left)
    (D.le_iSup_inf_opensRange₃ hi hj hk) key

/-- **The pairwise glueing datum of a locally directed glueing datum.** The transition data over
an arbitrary open contained in two charts is glued from the comparisons through the charts lying
below both. -/
noncomputable def toModulesGlueData : ModulesGlueData S f where
  mod := D.mod
  trans i j _ hi hj := D.pairTrans i j (le_inf hi hj)
  trans_map i j _ _ hi hj hWV t := D.pairTrans_map i j (le_inf hi hj) hWV t
  trans_trans i j k _ hi hj hk t := D.pairTrans_pairTrans i j k hi hj hk t

/-- The modules of the pairwise glueing datum are those of the original datum. -/
@[simp] theorem toModulesGlueData_mod : D.toModulesGlueData.mod = D.mod := rfl

/-- The transition maps of the pairwise glueing datum are the glued comparisons `D.pairTrans`. -/
theorem toModulesGlueData_trans (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (t : ToType (openSections (f i) (D.mod i) V)) :
    D.toModulesGlueData.trans i j hi hj t = D.pairTrans i j (le_inf hi hj) t := rfl

/-- **The sheaf of modules glued from a locally directed glueing datum.** -/
noncomputable abbrev glued : S.Modules := D.toModulesGlueData.glued

/-- The glued sheaf of modules restricts along each chart to the module it was glued from. -/
noncomputable def chartIso (i : ι) : D.glued.restrict (f i) ≅ D.mod i :=
  D.toModulesGlueData.chartIso i

/-- The sections of the glued sheaf of modules over an open contained in the `i`-th chart are the
sections of `mod i` over its preimage. -/
noncomputable def chartSectionsIso (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange) :
    D.glued.val.obj (op V) ≅ openSections (f i) (D.mod i) V :=
  D.toModulesGlueData.chartSectionsIso i hV

end ModulesDirectedGlueData

end Scheme

end Stacks.SheafOfModules

end
