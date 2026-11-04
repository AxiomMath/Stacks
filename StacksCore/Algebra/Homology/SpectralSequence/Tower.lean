module

public import StacksCore.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksCore.Algebra.Homology.SpectralSequence.Basic
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksCore.CategoryTheory.Abelian.Subobject
import StacksCore.Tactic.StacksAttribute

/-! # The towers `B_r ⊆ Z_r ⊆ E_{r₀}` of a spectral sequence: Stacks 011N and 011O

Stacks 011N: a spectral sequence `(E_r, d_r)` in an abelian category has towers of subobjects
`0 = B_1 ⊆ B_2 ⊆ ⋯ ⊆ B_r ⊆ ⋯ ⊆ Z_r ⊆ ⋯ ⊆ Z_2 ⊆ Z_1 = E_1` of `E_1` with `E_r = Z_r/B_r`:
`B_2 = Im d_1`, `Z_2 = Ker d_1`, `B_3` is the unique subobject of `E_1` containing `B_2` with
`B_3/B_2 = Im(d_2)`, `Z_3` the one with `Z_3/B_2 = Ker(d_2)`, and so on. Stacks 011O: (1) if
`Z_∞ = ⋂ Z_r` and `B_∞ = ⋃ B_r` exist, the limit is `E_∞ = Z_∞/B_∞`; (2) the spectral sequence
degenerates at `E_r` if `d_r, d_{r+1}, …` all vanish, and then `E_r = E_{r+1} = ⋯ = E_∞`.

The spectral sequence is Mathlib's `SpectralSequence C c r₀` (any shape family `c`, any
starting page `r₀`, so also the graded and bigraded variants of 0AMI), and the towers are built
at every position `pq : κ` inside `E_{r₀}^{pq} = (E.page r₀).X pq`; the only hypothesis is
`[Abelian C]`.

* `SpectralSequence.TowerData E pq k` bundles the level `k` (`r = r₀ + k`) of the towers:
  subobjects `B ≤ Z` of `E_{r₀}^{pq}` and an identification `iso : E_{r₀+k}^{pq} ≅ Z/B`.
  `TowerData.q : Z_r ↠ E_r` is the quotient map (`q_iso_hom`, `isColimitCokernelCoforkQ`,
  `map_kernelSubobject_q : Ker q = B_r`). `TowerData.step` is Stacks' recursion:
  `Z_{r+1} = q⁻¹(Ker d_r)` and `B_{r+1} = q⁻¹(Im d_r)` inside `Z_r` (`Z'`, `B'`), pushed into
  `E_{r₀}` along `Z_r ⊆ E_{r₀}` (`step_Z`, `step_B`), and
  `E_{r+1} ≅ H(E_r) ≅ Ker d_r/Im d_r ≅ Z_{r+1}/B_{r+1}` (`step_iso`) by transport of
  subquotients along the epimorphism `q` and the monomorphism `Z_r ⊆ E_{r₀}`
  (`Abelian.Subobject.cokernelOfLEPullbackIso`, `cokernelOfLEMapIso` in
  `StacksCore.CategoryTheory.Abelian.Subobject`, `HomologicalComplex.homologyIsoCokernelOfLE` in
  `StacksCore.Algebra.Homology.ShortComplex.HomologicalComplex`). Stacks' "unique subobject
  containing `B_r` with given quotient" is `step_Z_unique`, `step_B_unique` (at the level of
  `E_{r₀}`; these carry the tag) and `Z'_unique`, `B'_unique` (inside `Z_r`); `step_q` computes
  `Z_{r+1} ↠ E_{r+1}` as the restriction of `q` followed by `Ker d_r ⟶ H(E_r) ≅ E_{r+1}`.
* `SpectralSequence.towerData E pq k` is the recursion (`towerDataZero`: `Z_{r₀} = ⊤`,
  `B_{r₀} = ⊥`), and `E.Z pq r`, `E.B pq r : Subobject E_{r₀}^{pq}` are the `ℤ`-indexed towers
  (`⊤`, `⊥` for `r ≤ r₀`), with `B_le_Z`, `Z_antitone`, `B_monotone`, `Z_self`, `B_self`,
  `Z_add_natCast`, `B_add_natCast`, the tag `pageIsoSubquotient : E_r ≅ Z_r/B_r` (011N), the
  quotient map `E.q pq r : Z_r ↠ E_r` (`q_pageIsoSubquotient_hom`) and the `r`-indexed
  recursion `Z_add_one`, `B_add_one`, with the base step `Z_add_one_self : Z_{r₀+1} = Ker d_{r₀}`,
  `B_add_one_self : B_{r₀+1} = Im d_{r₀}`. `pageOfNat`, `TowerData.Z'`, `TowerData.B'`, `Z` and
  `B` are `abbrev`s on purpose: the `r`-indexed statements are proved by instantiating
  `k`-indexed ones at `(r - r₀).toNat`, which needs the definitions to unfold at reducible
  transparency. `TowerData.step` is an `abbrev` for a different reason: `T.step.Z` must be
  reducibly `(Subobject.map T.Z.arrow).obj T.Z'` for `step_q` and the edge-map compatibilities to
  typecheck (with a `def`, their statements are "not type-correct under the implicit
  transparency level"); the price is that `simp` may expand `T.step.iso` into its four-fold
  composite (`step_iso`), and `step_Z`, `step_B` are `dsimp`-redundant.
* `q_add_one : Z_{r+1} ↠ E_{r+1}` is the class of `Z_{r+1} ⊆ Z_r ↠ E_r` (in `liftCycles` form,
  `r`-indexed; `TowerData.step_q_eq_liftCycles`, `TowerData.step_q_ι` are the `k`-indexed
  versions), with `kernelSubobject_q : Ker(Z_r ↠ E_r) = B_r` inside `Z_r`. The `Ungraded.*`
  restatements `Ungraded.Z_add_one_self`, `B_add_one_self`, `Z_add_one`, `B_add_one` spell the
  same facts with `Ungraded.d`: `rw [hd]` with `hd : E.d r = …` never fires on
  `(E.page r).d () ((ComplexShape.refl Unit).next ())`.
* Relation to the edge maps of mathlib#25848 (`StacksCore.Algebra.Homology.SpectralSequence.EdgeStep`):
  `Z_add_one_of_hasEdgeEpiAt` (`d_r` out of `pq` vanishes, so `Z_{r+1} = Z_r`),
  `B_add_one_of_hasEdgeMonoAt` (`d_r` into `pq` vanishes, so `B_{r+1} = B_r`), and through
  `E_r ≅ Z_r/B_r` the edge maps are the maps induced on subquotients by `Z_{r+1} ⊆ Z_r`, resp.
  `B_r ⊆ B_{r+1}`: `TowerData.step_q_edgeMonoStep`, `q_edgeEpiStep`, `edgeMonoStep_iso_hom`,
  `edgeEpiStep_iso_hom` (`k`-indexed) and `edgeMonoStep_pageIsoSubquotient_hom`,
  `edgeEpiStep_pageIsoSubquotient_hom` (`r`-indexed).
* Stacks 011O (1). `E_∞` is Riou's `pageInfinity` (mathlib#25848, ported in
  `StacksCore.Algebra.Homology.SpectralSequence.PageInfinity`): the stable page `E_{rMin pq}` when
  `E.HasPageInfinityAt pq` (all differentials into and out of `pq` vanish from some page on),
  and `0` otherwise. In the stabilising case the towers are eventually constant
  (`Z_eq_of_rMin_le`, `B_eq_of_rMin_le`), so `Z_∞ = ⋂ Z_r` and `B_∞ = ⋃ B_r` exist, as
  `Z (rMin pq)` and `B (rMin pq)` (the tags `isGLB_range_Z`, `isLUB_range_B`, phrased as
  0121 (8) phrases `⋂ F^iA`), and the tag is `pageInfinityIsoSubquotient : E_∞ ≅ Z_∞/B_∞`.
  When `Subobject E_{r₀}` is a complete lattice, `⨅ r, Z r` and `⨆ r, B r` are these bounds by
  `IsGLB.sInf_eq` and `IsLUB.sSup_eq`; no such statement is made here, because the `InfSet`
  instance on `Subobject` is found only when the universe of `WellPowered` is spelled out.
  In general, `limitObj hZ hB` is Stacks' limit `Z_∞/B_∞`, for any `Z_∞`, `B_∞` with
  `hZ : IsGLB (Set.range (E.Z pq)) Z_∞` and `hB : IsLUB (Set.range (E.B pq)) B_∞`
  (`le_of_isGLB_of_isLUB` gives `B_∞ ≤ Z_∞`); where the pages stabilise it is `pageInfinity`
  (`limitObjIsoPageInfinity`).
* Stacks 011O (2). `DegeneratesAt E r` is the tagged predicate; `DegeneratesAt.hasEdgeEpiAt`,
  `hasEdgeMonoAt`, `hasPageInfinityAt`, `hasEdgeMonoAtFrom`, `hasEdgeEpiAtFrom` are theorems
  (not instances), `Z_eq`, `B_eq` say the towers are constant from `r` on, and the remark
  `E_r = E_{r+1} = ⋯ = E_∞` is `DegeneratesAt.pageIso` (`E_r ≅ E_{r'}`) and
  `DegeneratesAt.pageInfinityIso` (`E_∞ ≅ E_{r'}`), for every `r' ≥ r`.

Not done: functoriality of the towers in `E` (a morphism of spectral sequences maps `Z_r`, `B_r`
into `Z'_r`, `B'_r`), and Riou's one-sided `edgeMono`/`edgeEpi` (`E_∞ ↪ E_r`, `E_r ↠ E_∞`) in
tower terms.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace SpectralSequence

variable {C : Type*} [Category* C] [Abelian C]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (E : SpectralSequence C c r₀) (pq : κ)

/-! ### The towers, indexed by `k : ℕ` (`r = r₀ + k`) -/

/-- The page `E_{r₀+k}`, indexed by `k : ℕ` (so that no proof of `r₀ ≤ r` is needed). -/
abbrev pageOfNat (k : ℕ) : HomologicalComplex C (c (r₀ + k)) :=
  E.page (r₀ + k) (Int.le.intro k rfl)

/-- `pageXIsoOfEq` along an equality `r = r` is the identity. -/
@[simp]
lemma pageXIsoOfEq_refl (r : ℤ) (h : r = r) (hr : r₀ ≤ r) :
    E.pageXIsoOfEq pq r r h hr = Iso.refl _ := by
  simp [pageXIsoOfEq]

/-- `edgeMonoStep`, reindexed along an equality `r' = r''` of its source page. -/
lemma edgeMonoStep_eq_pageXIsoOfEq_hom_comp (r r' r'' : ℤ) [E.HasEdgeMonoAt pq r]
    (h : r + 1 = r') (h' : r' = r'') :
    E.edgeMonoStep pq r r' h =
      (E.pageXIsoOfEq pq r' r'' h' (by have := E.le₀_of_hasEdgeMonoAt pq r; lia)).hom ≫
        E.edgeMonoStep pq r r'' (h.trans h') := by
  subst h'
  simp

/-- `edgeEpiStep`, reindexed along an equality `r' = r''` of its target page. -/
lemma edgeEpiStep_eq_comp_pageXIsoOfEq_inv (r r' r'' : ℤ) [E.HasEdgeEpiAt pq r]
    (h : r + 1 = r') (h' : r' = r'') :
    E.edgeEpiStep pq r r' h =
      E.edgeEpiStep pq r r'' (h.trans h') ≫
        (E.pageXIsoOfEq pq r' r'' h' (by have := E.le₀_of_hasEdgeEpiAt pq r; lia)).inv := by
  subst h'
  simp

/-- Stacks 011N, the towers at level `k` (`r = r₀ + k`) and position `pq`: subobjects
`B_r ⊆ Z_r` of `E_{r₀}^{pq}` together with an identification `E_r^{pq} ≅ Z_r/B_r`. -/
structure TowerData (k : ℕ) where
  /-- `Z_r ⊆ E_{r₀}` -/
  Z : Subobject ((E.page r₀).X pq)
  /-- `B_r ⊆ E_{r₀}` -/
  B : Subobject ((E.page r₀).X pq)
  /-- `B_r ⊆ Z_r` -/
  le : B ≤ Z
  /-- `E_r ≅ Z_r/B_r` -/
  iso : (E.pageOfNat k).X pq ≅ cokernel (Subobject.ofLE B Z le)

namespace TowerData

variable {E pq} {k : ℕ} (T : E.TowerData pq k)

/-- The canonical epimorphism `Z_r ↠ Z_r/B_r ≅ E_r`. -/
noncomputable def q : (T.Z : C) ⟶ (E.pageOfNat k).X pq :=
  cokernel.π (Subobject.ofLE T.B T.Z T.le) ≫ T.iso.inv

/-- `Z_r ↠ E_r` is an epimorphism. -/
instance : Epi T.q := by
  dsimp [q]
  infer_instance

/-- `Z_r ↠ E_r ≅ Z_r/B_r` is the quotient map. -/
@[reassoc (attr := simp)]
lemma q_iso_hom : T.q ≫ T.iso.hom = cokernel.π (Subobject.ofLE T.B T.Z T.le) := by
  simp [q]

/-- `B_r ⊆ Z_r ↠ E_r` vanishes. -/
@[reassoc (attr := simp)]
lemma ofLE_q : Subobject.ofLE T.B T.Z T.le ≫ T.q = 0 := by
  simp [q]

/-- `Z_r ↠ E_r` is a cokernel of `B_r ⊆ Z_r`. -/
noncomputable def isColimitCokernelCoforkQ : IsColimit (CokernelCofork.ofπ T.q T.ofLE_q) :=
  IsColimit.ofIsoColimit (cokernelIsCokernel _) (Cofork.ext T.iso.symm (by simp [q]))

/-- The kernel of `Z_r ↠ E_r`, as a subobject of `E_{r₀}`, is `B_r`. -/
@[simp]
lemma map_kernelSubobject_q : (Subobject.map T.Z.arrow).obj (kernelSubobject T.q) = T.B := by
  rw [q, kernelSubobject_comp_mono, ← Abelian.Subobject.imageSubobject_eq_kernelSubobject,
    imageSubobject_mono, Subobject.map_arrow_mk_ofLE]

/-- The kernel of `Z_r ↠ E_r` is `B_r`, as a subobject of `Z_r`. -/
lemma kernelSubobject_q : kernelSubobject T.q = (Subobject.pullback T.Z.arrow).obj T.B := by
  rw [← T.map_kernelSubobject_q, Subobject.pullback_map_self]

/-! #### The step `r ↦ r + 1` -/

/-- `Z_{r+1}` as a subobject of `Z_r`: the preimage of `Ker(d_r)` under `Z_r ↠ E_r`. -/
noncomputable abbrev Z' : Subobject (T.Z : C) :=
  (Subobject.pullback T.q).obj (kernelSubobject ((E.pageOfNat k).d pq ((c (r₀ + k)).next pq)))

/-- `B_{r+1}` as a subobject of `Z_r`: the preimage of `Im(d_r)` under `Z_r ↠ E_r`. -/
noncomputable abbrev B' : Subobject (T.Z : C) :=
  (Subobject.pullback T.q).obj (imageSubobject ((E.pageOfNat k).d ((c (r₀ + k)).prev pq) pq))

/-- `B_{r+1} ⊆ Z_{r+1}`, inside `Z_r`. -/
lemma B'_le_Z' : T.B' ≤ T.Z' :=
  (Subobject.pullback T.q).monotone.imp (image_le_kernel _ _ ((E.pageOfNat k).d_comp_d _ pq _))

/-- `B_r = Ker(Z_r ↠ E_r) ⊆ Z_{r+1}`, inside `Z_r`. -/
lemma kernelSubobject_q_le_Z' : kernelSubobject T.q ≤ T.Z' :=
  Subobject.kernelSubobject_le_pullback T.q _

/-- `B_r = Ker(Z_r ↠ E_r) ⊆ B_{r+1}`, inside `Z_r`. -/
lemma kernelSubobject_q_le_B' : kernelSubobject T.q ≤ T.B' :=
  Subobject.kernelSubobject_le_pullback T.q _

/-- The image of `Z_{r+1}` under `Z_r ↠ E_r` is `Ker(d_r)`. -/
lemma exists_q_Z' :
    (Subobject.exists T.q).obj T.Z' =
      kernelSubobject ((E.pageOfNat k).d pq ((c (r₀ + k)).next pq)) :=
  Abelian.Subobject.exists_pullback_eq_self_of_epi _ _

/-- The image of `B_{r+1}` under `Z_r ↠ E_r` is `Im(d_r)`. -/
lemma exists_q_B' :
    (Subobject.exists T.q).obj T.B' =
      imageSubobject ((E.pageOfNat k).d ((c (r₀ + k)).prev pq) pq) :=
  Abelian.Subobject.exists_pullback_eq_self_of_epi _ _

/-- A subobject of `Z_r` containing `Ker(Z_r ↠ E_r)` is the preimage of its image in `E_r`. -/
private lemma eq_pullback_of_exists_eq {X : Subobject (T.Z : C)} (hX : kernelSubobject T.q ≤ X)
    {S : Subobject ((E.pageOfNat k).X pq)} (h : (Subobject.exists T.q).obj X = S) :
    X = (Subobject.pullback T.q).obj S := by
  rw [← h, Abelian.Subobject.pullback_exists_eq_self_of_epi _ _ hX]

/-- Stacks' characterisation of `Z_{r+1}` inside `Z_r`: it is the unique subobject of `Z_r`
containing `B_r = Ker(Z_r ↠ E_r)` whose image in `E_r = Z_r/B_r` is `Ker(d_r)`. -/
lemma Z'_unique {X : Subobject (T.Z : C)} (hX : kernelSubobject T.q ≤ X)
    (h : (Subobject.exists T.q).obj X =
      kernelSubobject ((E.pageOfNat k).d pq ((c (r₀ + k)).next pq))) :
    X = T.Z' :=
  T.eq_pullback_of_exists_eq hX h

/-- Stacks' characterisation of `B_{r+1}` inside `Z_r`: it is the unique subobject of `Z_r`
containing `B_r = Ker(Z_r ↠ E_r)` whose image in `E_r = Z_r/B_r` is `Im(d_r)`. -/
lemma B'_unique {X : Subobject (T.Z : C)} (hX : kernelSubobject T.q ≤ X)
    (h : (Subobject.exists T.q).obj X =
      imageSubobject ((E.pageOfNat k).d ((c (r₀ + k)).prev pq) pq)) :
    X = T.B' :=
  T.eq_pullback_of_exists_eq hX h

/-- The step of Stacks 011N's recursion: `Z_{r+1}`, `B_{r+1}` are the preimages of `Ker(d_r)`,
`Im(d_r)` under `Z_r ↠ Z_r/B_r ≅ E_r`, pushed into `E_{r₀}`, and
`E_{r+1} ≅ H(E_r) ≅ Ker(d_r)/Im(d_r) ≅ Z_{r+1}/B_{r+1}` by transport of subquotients along
`Z_r ↠ E_r` and along `Z_r ⊆ E_{r₀}`. -/
noncomputable abbrev step : E.TowerData pq (k + 1) :=
  { Z := (Subobject.map T.Z.arrow).obj T.Z'
    B := (Subobject.map T.Z.arrow).obj T.B'
    le := (Subobject.map T.Z.arrow).monotone.imp T.B'_le_Z'
    iso := (E.iso (r₀ + k) (r₀ + (k + 1 : ℕ)) pq (by lia) (Int.le.intro k rfl)).symm ≪≫
      (E.pageOfNat k).homologyIsoCokernelOfLE _ pq _ rfl rfl ≪≫
      (Abelian.Subobject.cokernelOfLEPullbackIso T.q _).symm ≪≫
      (Abelian.Subobject.cokernelOfLEMapIso T.Z.arrow T.B'_le_Z').symm }

/-- `Z_{r+1} ⊆ E_{r₀}` is the image of `Z_{r+1} ⊆ Z_r`. -/
@[simp]
lemma step_Z : T.step.Z = (Subobject.map T.Z.arrow).obj T.Z' := rfl

/-- `B_{r+1} ⊆ E_{r₀}` is the image of `B_{r+1} ⊆ Z_r`. -/
@[simp]
lemma step_B : T.step.B = (Subobject.map T.Z.arrow).obj T.B' := rfl

/-- `E_{r+1} ≅ Z_{r+1}/B_{r+1}`, by definition: `E_{r+1} ≅ H(E_r) ≅ Ker(d_r)/Im(d_r)`, then
transport along `Z_r ↠ E_r` and along `Z_r ⊆ E_{r₀}`. -/
lemma step_iso :
    T.step.iso = (E.iso (r₀ + k) (r₀ + (k + 1 : ℕ)) pq (by lia) (Int.le.intro k rfl)).symm ≪≫
      (E.pageOfNat k).homologyIsoCokernelOfLE _ pq _ rfl rfl ≪≫
      (Abelian.Subobject.cokernelOfLEPullbackIso T.q _).symm ≪≫
      (Abelian.Subobject.cokernelOfLEMapIso T.Z.arrow T.B'_le_Z').symm := rfl

/-- `Z_{r+1} ↠ E_{r+1}` unfolded: the quotient map onto `Z_{r+1}/B_{r+1}` followed by `step_iso`. -/
lemma step_q_eq :
    T.step.q = cokernel.π (Subobject.ofLE ((Subobject.map T.Z.arrow).obj T.B')
      ((Subobject.map T.Z.arrow).obj T.Z') ((Subobject.map T.Z.arrow).monotone.imp T.B'_le_Z')) ≫
      T.step.iso.inv := rfl

/-- `Z_{r+1} ⊆ Z_r`. -/
lemma step_Z_le : T.step.Z ≤ T.Z :=
  Subobject.map_arrow_obj_le T.Z T.Z'

/-- `B_r ⊆ B_{r+1}`. -/
lemma le_step_B : T.B ≤ T.step.B := by
  rw [step_B, ← T.map_kernelSubobject_q]
  exact (Subobject.map T.Z.arrow).monotone.imp T.kernelSubobject_q_le_B'

/-- `Z_{r+1}`, pulled back to `Z_r`. -/
lemma pullback_arrow_step_Z : (Subobject.pullback T.Z.arrow).obj T.step.Z = T.Z' := by
  rw [step_Z, Subobject.pullback_map_self]

/-- `B_{r+1}`, pulled back to `Z_r`. -/
lemma pullback_arrow_step_B : (Subobject.pullback T.Z.arrow).obj T.step.B = T.B' := by
  rw [step_B, Subobject.pullback_map_self]

/-- If `B_r ⊆ X ⊆ Z_r` and the image of `X` in `E_r = Z_r/B_r` is `S`, then `X` is the image in
`E_{r₀}` of the preimage of `S` under `Z_r ↠ E_r`. -/
private lemma eq_map_pullback_of_exists_eq {X : Subobject ((E.page r₀).X pq)} (hB : T.B ≤ X)
    (hZ : X ≤ T.Z) {S : Subobject ((E.pageOfNat k).X pq)}
    (h : (Subobject.exists T.q).obj ((Subobject.pullback T.Z.arrow).obj X) = S) :
    X = (Subobject.map T.Z.arrow).obj ((Subobject.pullback T.q).obj S) := by
  rw [← T.eq_pullback_of_exists_eq (by
    rw [kernelSubobject_q]; exact (Subobject.pullback T.Z.arrow).monotone.imp hB) h,
    ← Subobject.inf_eq_map_pullback, inf_eq_right.2 hZ]

/-- Stacks' characterisation of `Z_{r+1}` at the level of `E_{r₀}`: it is the unique
subobject `X` with `B_r ⊆ X ⊆ Z_r` whose image in `E_r = Z_r/B_r` is `Ker(d_r)`. -/
@[stacks 011N "`Z_{r+1}`: the unique `X` with `B_r ⊆ X ⊆ Z_r` and `X/B_r = Ker(d_r)` in `Z_r/B_r`",
  ega "0 11.1.1" "(b) Z_k inverse image"]
lemma step_Z_unique {X : Subobject ((E.page r₀).X pq)} (hB : T.B ≤ X) (hZ : X ≤ T.Z)
    (h : (Subobject.exists T.q).obj ((Subobject.pullback T.Z.arrow).obj X) =
      kernelSubobject ((E.pageOfNat k).d pq ((c (r₀ + k)).next pq))) :
    X = T.step.Z :=
  T.eq_map_pullback_of_exists_eq hB hZ h

/-- Stacks' characterisation of `B_{r+1}` at the level of `E_{r₀}`: it is the unique
subobject `X` with `B_r ⊆ X ⊆ Z_r` whose image in `E_r = Z_r/B_r` is `Im(d_r)`. -/
@[stacks 011N "`B_{r+1}`: the unique `X` with `B_r ⊆ X ⊆ Z_r` and `X/B_r = Im(d_r)` in `Z_r/B_r`",
  ega "0 11.1.1" "(b) B_k inverse image"]
lemma step_B_unique {X : Subobject ((E.page r₀).X pq)} (hB : T.B ≤ X) (hZ : X ≤ T.Z)
    (h : (Subobject.exists T.q).obj ((Subobject.pullback T.Z.arrow).obj X) =
      imageSubobject ((E.pageOfNat k).d ((c (r₀ + k)).prev pq) pq)) :
    X = T.step.B :=
  T.eq_map_pullback_of_exists_eq hB hZ h

/-- If the differential out of `pq` on the page `E_r` vanishes, then `Z_{r+1} = Z_r`. -/
lemma step_Z_of_d_eq_zero (h : (E.pageOfNat k).d pq ((c (r₀ + k)).next pq) = 0) :
    T.step.Z = T.Z := by
  simp [*]

/-- If the differential into `pq` on the page `E_r` vanishes, then `B_{r+1} = B_r`. -/
lemma step_B_of_d_eq_zero (h : (E.pageOfNat k).d ((c (r₀ + k)).prev pq) pq = 0) :
    T.step.B = T.B := by
  simp [B', h, Subobject.pullback_bot]

/-- `Z_{r+1} ↠ E_{r+1}` is the restriction `Z_{r+1} = q⁻¹(Ker d_r) ⟶ Ker d_r` of `Z_r ↠ E_r`
followed by `Ker d_r ≅ Z(E_r) ⟶ H(E_r) ≅ E_{r+1}`. -/
@[reassoc]
lemma step_q :
    T.step.q = (Subobject.mapObjIso T.Z.arrow T.Z').hom ≫ Subobject.pullbackπ T.q _ ≫
      ((E.pageOfNat k).kernelSubobjectIsoCycles pq _ rfl).hom ≫
        (E.pageOfNat k).homologyπ pq ≫
          (E.iso (r₀ + k) (r₀ + (k + 1 : ℕ)) pq (by lia) (Int.le.intro k rfl)).hom := by
  rw [step_q_eq, step_iso]
  simp only [Iso.trans_inv, Iso.symm_inv, assoc]
  rw [Abelian.Subobject.π_cokernelOfLEMapIso_hom_assoc,
    Abelian.Subobject.π_cokernelOfLEPullbackIso_hom_assoc,
    HomologicalComplex.π_homologyIsoCokernelOfLE_inv_assoc]

/-- `Z_{r+1} ⊆ Z_r ↠ E_r` is the restriction of `q` to `q⁻¹(Ker d_r) ⟶ Ker d_r`. -/
@[reassoc]
lemma Z'_arrow_q :
    T.Z'.arrow ≫ T.q = Subobject.pullbackπ T.q _ ≫
      (kernelSubobject ((E.pageOfNat k).d pq ((c (r₀ + k)).next pq))).arrow :=
  (Subobject.isPullback T.q _).w.symm

/-- `Z_{r+1} ⊆ Z_r ↠ E_r →d_r E_r` vanishes (left-associated, the form `liftCycles` wants). -/
lemma ofLE_step_Z_q_d :
    (Subobject.ofLE T.step.Z T.Z T.step_Z_le ≫ T.q) ≫
      (E.pageOfNat k).d pq ((c (r₀ + k)).next pq) = 0 := by
  rw [← Subobject.mapObjIso_hom_comp_arrow T.Z T.Z', assoc, assoc, T.Z'_arrow_q_assoc,
    kernelSubobject_arrow_comp, comp_zero, comp_zero]

/-- `Z_{r+1} ↠ E_{r+1}` in `liftCycles` form: the class of `Z_{r+1} ⊆ Z_r ↠ E_r`. -/
lemma step_q_eq_liftCycles :
    T.step.q = (E.pageOfNat k).liftCycles (Subobject.ofLE T.step.Z T.Z T.step_Z_le ≫ T.q) _ rfl
      T.ofLE_step_Z_q_d ≫ (E.pageOfNat k).homologyπ pq ≫
        (E.iso (r₀ + k) (r₀ + (k + 1 : ℕ)) pq (by lia) (Int.le.intro k rfl)).hom := by
  have h : (E.pageOfNat k).liftCycles (Subobject.ofLE T.step.Z T.Z T.step_Z_le ≫ T.q) _ rfl
      T.ofLE_step_Z_q_d = (Subobject.mapObjIso T.Z.arrow T.Z').hom ≫ Subobject.pullbackπ T.q _ ≫
        ((E.pageOfNat k).kernelSubobjectIsoCycles pq _ rfl).hom := by
    rw [← cancel_mono ((E.pageOfNat k).iCycles pq), assoc, assoc,
      HomologicalComplex.kernelSubobjectIsoCycles_hom_iCycles, HomologicalComplex.liftCycles_i,
      (Subobject.isPullback T.q _).w, Subobject.mapObjIso_hom_comp_arrow_assoc]
  rw [step_q, h, assoc, assoc]

/-- `Z_{r+1} ↠ E_{r+1} ≅ H(E_r) ⟶ opcycles` is `Z_{r+1} ⊆ Z_r ↠ E_r ⟶ opcycles` (non-dependent
form of `step_q_eq_liftCycles`, since `homologyι` is a monomorphism). -/
lemma step_q_ι :
    T.step.q ≫ (E.iso (r₀ + k) (r₀ + (k + 1 : ℕ)) pq (by lia) (Int.le.intro k rfl)).inv ≫
      (E.pageOfNat k).homologyι pq =
    Subobject.ofLE T.step.Z T.Z T.step_Z_le ≫ T.q ≫ (E.pageOfNat k).pOpcycles pq := by
  rw [step_q_eq_liftCycles, assoc, assoc, Iso.hom_inv_id_assoc, HomologicalComplex.homology_π_ι,
    HomologicalComplex.liftCycles_i_assoc, assoc]

/-- `step_q_ι` for an arbitrary spelling `r'` of the page `r₀ + k + 1`. -/
lemma step_q_ι' (r' : ℤ) (h : r₀ + (k + 1 : ℕ) = r') :
    T.step.q ≫ (E.pageXIsoOfEq pq _ r' h).hom ≫
      (E.iso (r₀ + k) r' pq (by omega) (Int.le.intro k rfl)).inv ≫ (E.pageOfNat k).homologyι pq =
    Subobject.ofLE T.step.Z T.Z T.step_Z_le ≫ T.q ≫ (E.pageOfNat k).pOpcycles pq := by
  subst h
  rw [pageXIsoOfEq_refl, Iso.refl_hom, id_comp]
  exact T.step_q_ι

/-! #### Compatibility with the edge maps -/

/-- When the differentials into `pq` on `E_r` vanish, `Z_{r+1} ↠ E_{r+1} ⟶ E_r` is
`Z_{r+1} ⊆ Z_r ↠ E_r`. -/
@[reassoc]
lemma step_q_edgeMonoStep [E.HasEdgeMonoAt pq (r₀ + k)] :
    T.step.q ≫ E.edgeMonoStep pq (r₀ + k) (r₀ + (k + 1 : ℕ)) =
      Subobject.ofLE T.step.Z T.Z T.step_Z_le ≫ T.q := by
  rw [step_q, edgeMonoStep]
  simp only [assoc, Iso.hom_inv_id_assoc, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
    HomologicalComplex.kernelSubobjectIsoCycles_hom_iCycles]
  rw [(Subobject.isPullback T.q _).w, Subobject.mapObjIso_hom_comp_arrow_assoc]

/-- When the differentials out of `pq` on `E_r` vanish (so that `Z_{r+1} = Z_r`),
`Z_r ↠ E_r ⟶ E_{r+1}` is `Z_r = Z_{r+1} ↠ E_{r+1}`. -/
@[reassoc]
lemma q_edgeEpiStep [E.HasEdgeEpiAt pq (r₀ + k)] :
    T.q ≫ E.edgeEpiStep pq (r₀ + k) (r₀ + (k + 1 : ℕ)) =
      Subobject.ofLE T.Z T.step.Z
        (T.step_Z_of_d_eq_zero (E.d_eq_zero_of_hasEdgeEpiAt pq _ _)).ge ≫ T.step.q := by
  rw [step_q, edgeEpiStep,
    ← cancel_mono (E.iso (r₀ + k) (r₀ + (k + 1 : ℕ)) pq (by lia) (Int.le.intro k rfl)).inv,
    ← cancel_mono ((E.pageOfNat k).isoHomologyι pq _ rfl
      (E.d_eq_zero_of_hasEdgeEpiAt pq _ _)).hom]
  simp only [assoc, Iso.hom_inv_id_assoc, comp_id,
    HomologicalComplex.isoHomologyι_hom, HomologicalComplex.isoHomologyι_inv_hom_id,
    HomologicalComplex.homology_π_ι, HomologicalComplex.kernelSubobjectIsoCycles_hom_iCycles_assoc]
  rw [reassoc_of% (Subobject.isPullback T.q _).w, Subobject.mapObjIso_hom_comp_arrow_assoc,
    Subobject.ofLE_comp_ofLE_assoc, Subobject.ofLE_refl, id_comp]

/-- Through `E_r ≅ Z_r/B_r` and `E_{r+1} ≅ Z_{r+1}/B_{r+1}`, `edgeMonoStep` is the map
`Z_{r+1}/B_{r+1} ⟶ Z_r/B_r` induced by `Z_{r+1} ⊆ Z_r` (with `B_{r+1} = B_r`). -/
@[reassoc]
lemma edgeMonoStep_iso_hom [E.HasEdgeMonoAt pq (r₀ + k)] :
    E.edgeMonoStep pq (r₀ + k) (r₀ + (k + 1 : ℕ)) ≫ T.iso.hom =
      T.step.iso.hom ≫ cokernel.map _ _
        (Subobject.ofLE T.step.B T.B
          (T.step_B_of_d_eq_zero (E.d_eq_zero_of_hasEdgeMonoAt _ pq _)).le)
        (Subobject.ofLE T.step.Z T.Z T.step_Z_le)
        (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
  rw [← cancel_epi T.step.q, step_q_edgeMonoStep_assoc, q_iso_hom, q_iso_hom_assoc,
    cokernel.π_desc]

/-- Through `E_r ≅ Z_r/B_r` and `E_{r+1} ≅ Z_{r+1}/B_{r+1}`, `edgeEpiStep` is the map
`Z_r/B_r ⟶ Z_{r+1}/B_{r+1}` induced by `B_r ⊆ B_{r+1}` (with `Z_{r+1} = Z_r`). -/
@[reassoc]
lemma edgeEpiStep_iso_hom [E.HasEdgeEpiAt pq (r₀ + k)] :
    E.edgeEpiStep pq (r₀ + k) (r₀ + (k + 1 : ℕ)) ≫ T.step.iso.hom =
      T.iso.hom ≫ cokernel.map _ _ (Subobject.ofLE T.B T.step.B T.le_step_B)
        (Subobject.ofLE T.Z T.step.Z
          (T.step_Z_of_d_eq_zero (E.d_eq_zero_of_hasEdgeEpiAt pq _ _)).ge)
        (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
  rw [← cancel_epi T.q, q_edgeEpiStep_assoc, q_iso_hom, q_iso_hom_assoc, cokernel.π_desc]

/-- `edgeMonoStep_iso_hom` for an arbitrary spelling `r'` of the page `r₀ + k + 1`. -/
@[reassoc]
lemma edgeMonoStep_iso_hom' [E.HasEdgeMonoAt pq (r₀ + k)] (r' : ℤ) (h : r₀ + k + 1 = r') :
    E.edgeMonoStep pq (r₀ + k) r' h ≫ T.iso.hom =
      (E.pageXIsoOfEq pq r' (r₀ + (k + 1 : ℕ)) (by lia)).hom ≫ T.step.iso.hom ≫
        cokernel.map _ _
          (Subobject.ofLE T.step.B T.B
            (T.step_B_of_d_eq_zero (E.d_eq_zero_of_hasEdgeMonoAt _ pq _)).le)
          (Subobject.ofLE T.step.Z T.Z T.step_Z_le)
          (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
  rw [E.edgeMonoStep_eq_pageXIsoOfEq_hom_comp pq (r₀ + k) r' (r₀ + (k + 1 : ℕ)) h (by lia),
    assoc, T.edgeMonoStep_iso_hom]

/-- `edgeEpiStep_iso_hom` for an arbitrary spelling `r'` of the page `r₀ + k + 1`. -/
@[reassoc]
lemma edgeEpiStep_iso_hom' [E.HasEdgeEpiAt pq (r₀ + k)] (r' : ℤ) (h : r₀ + k + 1 = r') :
    E.edgeEpiStep pq (r₀ + k) r' h ≫ (E.pageXIsoOfEq pq r' (r₀ + (k + 1 : ℕ)) (by lia)).hom ≫
        T.step.iso.hom =
      T.iso.hom ≫ cokernel.map _ _ (Subobject.ofLE T.B T.step.B T.le_step_B)
        (Subobject.ofLE T.Z T.step.Z
          (T.step_Z_of_d_eq_zero (E.d_eq_zero_of_hasEdgeEpiAt pq _ _)).ge)
        (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
  rw [E.edgeEpiStep_eq_comp_pageXIsoOfEq_inv pq (r₀ + k) r' (r₀ + (k + 1 : ℕ)) h (by lia),
    assoc, Iso.inv_hom_id_assoc, T.edgeEpiStep_iso_hom]

end TowerData

/-! ### The towers, indexed by `r : ℤ` -/

/-- The start of the recursion: `Z_{r₀} = E_{r₀}`, `B_{r₀} = 0`. -/
noncomputable def towerDataZero : E.TowerData pq 0 where
  Z := ⊤
  B := ⊥
  le := bot_le
  iso := E.pageXIsoOfEq pq _ r₀ (by simp) ≪≫
    (asIso (⊤ : Subobject ((E.page r₀).X pq)).arrow).symm ≪≫
    cokernelZeroIsoTarget.symm ≪≫ cokernelIsoOfEq
      ((cancel_mono (⊤ : Subobject ((E.page r₀).X pq)).arrow).1 (by simp))

/-- `Z_{r₀} = E_{r₀}`. -/
@[simp]
lemma towerDataZero_Z : (E.towerDataZero pq).Z = ⊤ := rfl

/-- `B_{r₀} = 0`. -/
@[simp]
lemma towerDataZero_B : (E.towerDataZero pq).B = ⊥ := rfl

/-- The towers of Stacks 011N, by recursion on `k` (`r = r₀ + k`). -/
noncomputable def towerData : ∀ k : ℕ, E.TowerData pq k
  | 0 => E.towerDataZero pq
  | k + 1 => (towerData k).step

/-- `towerData 0` is the start of the recursion. -/
@[simp]
lemma towerData_zero : E.towerData pq 0 = E.towerDataZero pq := rfl

/-- `towerData (k + 1)` is the step applied to `towerData k`. -/
@[simp]
lemma towerData_succ (k : ℕ) : E.towerData pq (k + 1) = (E.towerData pq k).step := rfl

/-- The tower `Z_r ⊆ E_{r₀}` of Stacks 011N (`Z_r` for `r ≥ r₀`; for `r ≤ r₀` it is `⊤`). -/
noncomputable abbrev Z (r : ℤ) : Subobject ((E.page r₀).X pq) :=
  (E.towerData pq (r - r₀).toNat).Z

/-- The tower `B_r ⊆ E_{r₀}` of Stacks 011N (`B_r` for `r ≥ r₀`; for `r ≤ r₀` it is `⊥`). -/
noncomputable abbrev B (r : ℤ) : Subobject ((E.page r₀).X pq) :=
  (E.towerData pq (r - r₀).toNat).B

/-- `B_r ⊆ Z_r`. -/
lemma B_le_Z (r : ℤ) : E.B pq r ≤ E.Z pq r :=
  (E.towerData pq (r - r₀).toNat).le

/-- `Z_{r₀+k}` in terms of the `ℕ`-indexed recursion. -/
@[simp]
lemma Z_add_natCast (k : ℕ) : E.Z pq (r₀ + k) = (E.towerData pq k).Z := by
  rw [Z, show (r₀ + k - r₀).toNat = k by omega]

/-- `B_{r₀+k}` in terms of the `ℕ`-indexed recursion. -/
@[simp]
lemma B_add_natCast (k : ℕ) : E.B pq (r₀ + k) = (E.towerData pq k).B := by
  rw [B, show (r₀ + k - r₀).toNat = k by omega]

/-- `Z_r = E_{r₀}` for `r ≤ r₀`. -/
lemma Z_of_le {r : ℤ} (hr : r ≤ r₀) : E.Z pq r = ⊤ := by
  rw [Z, show (r - r₀).toNat = 0 by omega, towerData_zero, towerDataZero_Z]

/-- `B_r = 0` for `r ≤ r₀`. -/
lemma B_of_le {r : ℤ} (hr : r ≤ r₀) : E.B pq r = ⊥ := by
  rw [B, show (r - r₀).toNat = 0 by omega, towerData_zero, towerDataZero_B]

/-- `Z_{r₀} = E_{r₀}`. -/
@[simp]
lemma Z_self : E.Z pq r₀ = ⊤ := E.Z_of_le pq le_rfl

/-- `B_{r₀} = 0`. -/
@[simp]
lemma B_self : E.B pq r₀ = ⊥ := E.B_of_le pq le_rfl

/-- The canonical epimorphism `Z_r ↠ E_r`, for `r ≥ r₀`. -/
noncomputable def q (r : ℤ) (hr : r₀ ≤ r := by lia) : (E.Z pq r : C) ⟶ (E.page r).X pq :=
  (E.towerData pq (r - r₀).toNat).q ≫ (E.pageXIsoOfEq pq _ r (by omega)).hom

/-- `Z_r ↠ E_r` is an epimorphism. -/
instance (r : ℤ) (hr : r₀ ≤ r) : Epi (E.q pq r hr) :=
  epi_comp _ _

/-- Stacks 011N: `E_r = Z_r/B_r`, for every `r ≥ r₀`. -/
@[stacks 011N "the towers `B_r ⊆ Z_r ⊆ E_{r₀}` with `E_r = Z_r/B_r`, for any shape family and `r₀`"]
noncomputable def pageIsoSubquotient (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (E.page r).X pq ≅ cokernel (Subobject.ofLE (E.B pq r) (E.Z pq r) (E.B_le_Z pq r)) :=
  E.pageXIsoOfEq pq r (r₀ + (r - r₀).toNat) (by omega) ≪≫ (E.towerData pq (r - r₀).toNat).iso

/-- `Z_r ↠ E_r ≅ Z_r/B_r` is the quotient map. -/
@[reassoc (attr := simp)]
lemma q_pageIsoSubquotient_hom (r : ℤ) (hr : r₀ ≤ r) :
    E.q pq r hr ≫ (E.pageIsoSubquotient pq r hr).hom =
      cokernel.π (Subobject.ofLE (E.B pq r) (E.Z pq r) (E.B_le_Z pq r)) := by
  simp [q, pageIsoSubquotient, pageXIsoOfEq]

/-- The image in `E_{r₀}` of the preimage of `S ⊆ E_r` under `Z_r ↠ E_r`, with `Z_r` and `q`
`r`-indexed (`r = r₀ + k`) or `k`-indexed. -/
private lemma map_pullback_q_eq (k : ℕ) (hr : r₀ ≤ r₀ + k)
    (S : Subobject ((E.page (r₀ + k)).X pq)) :
    (Subobject.map (E.Z pq (r₀ + k)).arrow).obj ((Subobject.pullback (E.q pq (r₀ + k) hr)).obj S) =
      (Subobject.map (E.towerData pq k).Z.arrow).obj
        ((Subobject.pullback (E.towerData pq k).q).obj S) := by
  have aux : ∀ (n : ℕ) (hn : n = k) (h : r₀ + n = r₀ + k),
      (Subobject.map (E.towerData pq n).Z.arrow).obj
        ((Subobject.pullback ((E.towerData pq n).q ≫ (E.pageXIsoOfEq pq _ _ h).hom)).obj S) =
      (Subobject.map (E.towerData pq k).Z.arrow).obj
        ((Subobject.pullback (E.towerData pq k).q).obj S) := by
    rintro n rfl h
    simp [pageXIsoOfEq]
  exact aux _ (by omega) (by omega)

/-- Stacks 011N's recursion at the level of `E_{r₀}`, `r`-indexed: `Z_{r+1}` is the image in
`E_{r₀}` of the preimage of `Ker(d_r)` under `Z_r ↠ E_r`. -/
theorem Z_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.Z pq (r + 1) = (Subobject.map (E.Z pq r).arrow).obj ((Subobject.pullback (E.q pq r hr)).obj
      (kernelSubobject ((E.page r).d pq ((c r).next pq)))) := by
  obtain ⟨k, rfl⟩ := Int.le.dest hr
  rw [E.map_pullback_q_eq pq k hr]
  rw [add_assoc, ← Nat.cast_succ, E.Z_add_natCast]
  rfl

/-- Stacks 011N's recursion at the level of `E_{r₀}`, `r`-indexed: `B_{r+1}` is the image in
`E_{r₀}` of the preimage of `Im(d_r)` under `Z_r ↠ E_r`. -/
theorem B_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.B pq (r + 1) = (Subobject.map (E.Z pq r).arrow).obj ((Subobject.pullback (E.q pq r hr)).obj
      (imageSubobject ((E.page r).d ((c r).prev pq) pq))) := by
  obtain ⟨k, rfl⟩ := Int.le.dest hr
  rw [E.map_pullback_q_eq pq k hr]
  rw [add_assoc, ← Nat.cast_succ, E.B_add_natCast]
  rfl

/-- `Z_{r₀} ↠ E_{r₀}` is the inclusion `Z_{r₀} = ⊤ ⊆ E_{r₀}`. -/
lemma q_self : E.q pq r₀ le_rfl = (E.Z pq r₀).arrow := by
  have aux : ∀ (n : ℕ) (hn : n = 0) (h : r₀ + n = r₀),
      (E.towerData pq n).q ≫ (E.pageXIsoOfEq pq (r₀ + n) r₀ h).hom =
        (E.towerData pq n).Z.arrow := by
    rintro n rfl h
    rw [towerData_zero, ← Iso.eq_comp_inv, ← cancel_mono (E.towerDataZero pq).iso.hom,
      TowerData.q_iso_hom]
    simp [towerDataZero, Iso.trans_hom, Iso.symm_hom, asIso_inv, assoc, Iso.inv_hom_id_assoc,
      IsIso.hom_inv_id_assoc, cokernelZeroIsoTarget_inv, π_comp_cokernelIsoOfEq_hom]
  rw [q]
  exact aux _ (by lia) (by lia)

/-- Stacks 011N's base step: `Z_2 = Ker(d_1)`, i.e. `Z_{r₀+1} = Ker(d_{r₀})`. -/
@[stacks 011N "`Z_2 = Ker(d_1)`, i.e. `Z_{r₀+1} = Ker(d_{r₀})`"]
lemma Z_add_one_self :
    E.Z pq (r₀ + 1) = kernelSubobject ((E.page r₀).d pq ((c r₀).next pq)) := by
  rw [E.Z_add_one pq r₀ le_rfl, q_self, ← Subobject.inf_eq_map_pullback, Z_self, top_inf_eq]

/-- Stacks 011N's base step: `B_2 = Im(d_1)`, i.e. `B_{r₀+1} = Im(d_{r₀})`. -/
@[stacks 011N "`B_2 = Im(d_1)`, i.e. `B_{r₀+1} = Im(d_{r₀})`", ega "0 11.1.1" "(b) B_{r+1}=Im(d_r)"]
lemma B_add_one_self :
    E.B pq (r₀ + 1) = imageSubobject ((E.page r₀).d ((c r₀).prev pq) pq) := by
  rw [E.B_add_one pq r₀ le_rfl, q_self, ← Subobject.inf_eq_map_pullback, Z_self, top_inf_eq]

/-- The tower `Z` is decreasing, `k`-indexed version. -/
lemma towerData_Z_antitone : Antitone fun k => (E.towerData pq k).Z :=
  antitone_nat_of_succ_le fun k => (E.towerData pq k).step_Z_le

/-- The tower `B` is increasing, `k`-indexed version. -/
lemma towerData_B_monotone : Monotone fun k => (E.towerData pq k).B :=
  monotone_nat_of_le_succ fun k => (E.towerData pq k).le_step_B

/-- Stacks 011N: the tower `Z` is decreasing, `⋯ ⊆ Z_{r+1} ⊆ Z_r ⊆ ⋯ ⊆ Z_{r₀} = E_{r₀}`. -/
lemma Z_antitone : Antitone (E.Z pq) := fun r r' h =>
  E.towerData_Z_antitone pq (show (r - r₀).toNat ≤ (r' - r₀).toNat by omega)

/-- Stacks 011N: the tower `B` is increasing, `0 = B_{r₀} ⊆ ⋯ ⊆ B_r ⊆ B_{r+1} ⊆ ⋯`. -/
lemma B_monotone : Monotone (E.B pq) := fun r r' h =>
  E.towerData_B_monotone pq (show (r - r₀).toNat ≤ (r' - r₀).toNat by omega)

/-- `Ker(Z_r ↠ E_r)`, pushed into `E_{r₀}`, is `B_r` (`r`-indexed). -/
@[simp]
lemma map_kernelSubobject_q (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.map (E.Z pq r).arrow).obj (kernelSubobject (E.q pq r hr)) = E.B pq r := by
  rw [q, kernelSubobject_comp_mono, TowerData.map_kernelSubobject_q]

/-- `Ker(Z_r ↠ E_r) = B_r` inside `Z_r` (`r`-indexed). -/
lemma kernelSubobject_q (r : ℤ) (hr : r₀ ≤ r) :
    kernelSubobject (E.q pq r hr) = (Subobject.pullback (E.Z pq r).arrow).obj (E.B pq r) := by
  rw [← E.map_kernelSubobject_q pq r hr, Subobject.pullback_map_self]

/-- `Z_{r+1} ↠ E_{r+1} ≅ H(E_r) ⟶ opcycles` is `Z_{r+1} ⊆ Z_r ↠ E_r ⟶ opcycles`, `r`-indexed. -/
lemma q_add_one_ι (r : ℤ) (hr : r₀ ≤ r) :
    E.q pq (r + 1) ≫ (E.iso r (r + 1) pq rfl hr).inv ≫ (E.page r).homologyι pq =
      Subobject.ofLE (E.Z pq (r + 1)) (E.Z pq r) ((E.Z_antitone pq).imp (by lia)) ≫ E.q pq r hr ≫
        (E.page r).pOpcycles pq := by
  obtain ⟨k, rfl⟩ := Int.le.dest hr
  have aux : ∀ (n m : ℕ) (hn : n = k) (hm : m = k + 1) (h : r₀ + n = r₀ + k)
      (h' : r₀ + m = r₀ + k + 1) (hle : (E.towerData pq m).Z ≤ (E.towerData pq n).Z),
      ((E.towerData pq m).q ≫ (E.pageXIsoOfEq pq _ _ h').hom) ≫
          (E.iso (r₀ + k) (r₀ + k + 1) pq rfl hr).inv ≫ (E.page (r₀ + k)).homologyι pq =
        Subobject.ofLE (E.towerData pq m).Z (E.towerData pq n).Z hle ≫
          ((E.towerData pq n).q ≫ (E.pageXIsoOfEq pq _ _ h).hom) ≫
            (E.page (r₀ + k)).pOpcycles pq := by
    rintro n m rfl rfl h h' hle
    dsimp only [towerData_succ] at hle ⊢
    rw [pageXIsoOfEq_refl, Iso.refl_hom, comp_id, assoc]
    exact (E.towerData pq n).step_q_ι' _ h'
  rw [q, q]
  exact aux _ _ (by omega) (by omega) (by omega) (by omega) _

/-- `Z_{r+1} ⊆ Z_r ↠ E_r →d_r E_r` vanishes (`r`-indexed, left-associated): `d_r` factors as
`pOpcycles ≫ fromOpcycles` and `Z_{r+1} ⊆ Z_r ↠ E_r ⟶ opcycles` is `q_{r+1} ≫ … ≫ homologyι`
(`q_add_one_ι`), which `fromOpcycles` kills. -/
lemma ofLE_q_d (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.ofLE (E.Z pq (r + 1)) (E.Z pq r) ((E.Z_antitone pq).imp (by lia)) ≫ E.q pq r hr) ≫
      (E.page r).d pq ((c r).next pq) = 0 := by
  rw [← HomologicalComplex.p_fromOpcycles, assoc, ← reassoc_of% (E.q_add_one_ι pq r hr),
    HomologicalComplex.homologyι_comp_fromOpcycles, comp_zero, comp_zero]

/-- `Z_{r+1} ↠ E_{r+1}` in `liftCycles` form, `r`-indexed: the class of `Z_{r+1} ⊆ Z_r ↠ E_r`. -/
lemma q_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.q pq (r + 1) = (E.page r).liftCycles
      (Subobject.ofLE (E.Z pq (r + 1)) (E.Z pq r) ((E.Z_antitone pq).imp (by lia)) ≫ E.q pq r hr)
      _ rfl (E.ofLE_q_d pq r hr) ≫ (E.page r).homologyπ pq ≫ (E.iso r (r + 1) pq rfl hr).hom := by
  rw [← cancel_mono (E.iso r (r + 1) pq rfl hr).inv, ← cancel_mono ((E.page r).homologyι pq)]
  simp only [assoc]
  rw [E.q_add_one_ι pq r hr, Iso.hom_inv_id_assoc, HomologicalComplex.homology_π_ι,
    HomologicalComplex.liftCycles_i_assoc, assoc]

/-! ### Relation to the edge maps -/

/-- If all differentials out of `pq` on the page `E_r` vanish, then `Z_{r+1} = Z_r`. -/
theorem Z_add_one_of_hasEdgeEpiAt (r : ℤ) [E.HasEdgeEpiAt pq r] :
    E.Z pq (r + 1) = E.Z pq r := by
  obtain ⟨k, rfl⟩ := Int.le.dest (E.le₀_of_hasEdgeEpiAt pq r)
  rw [Z, Z, show (r₀ + k + 1 - r₀).toNat = k + 1 by omega, show (r₀ + k - r₀).toNat = k by omega]
  exact (E.towerData pq k).step_Z_of_d_eq_zero (E.d_eq_zero_of_hasEdgeEpiAt pq _ _)

/-- If all differentials into `pq` on the page `E_r` vanish, then `B_{r+1} = B_r`. -/
theorem B_add_one_of_hasEdgeMonoAt (r : ℤ) [E.HasEdgeMonoAt pq r] :
    E.B pq (r + 1) = E.B pq r := by
  obtain ⟨k, rfl⟩ := Int.le.dest (E.le₀_of_hasEdgeMonoAt pq r)
  rw [B, B, show (r₀ + k + 1 - r₀).toNat = k + 1 by omega, show (r₀ + k - r₀).toNat = k by omega]
  exact (E.towerData pq k).step_B_of_d_eq_zero (E.d_eq_zero_of_hasEdgeMonoAt _ pq _)

/-- A family `F : ℤ → α` with `F (r'' + 1) = F r''` for all `r'' ≥ r` is constant from `r` on. -/
private lemma eq_of_forall_succ_eq {α : Type*} (F : ℤ → α) {r : ℤ}
    (H : ∀ r'', r ≤ r'' → F (r'' + 1) = F r'') {r' : ℤ} (hr' : r ≤ r') : F r' = F r := by
  obtain ⟨k, rfl⟩ := Int.le.dest hr'
  clear hr'
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, ← add_assoc, H _ (by lia), ih]

/-- If all differentials out of `pq` vanish from the page `E_r` on, the tower `Z` is constant
from `r` on. -/
theorem Z_eq_of_forall_hasEdgeEpiAt {r : ℤ} (H : ∀ r'' (_ : r ≤ r''), E.HasEdgeEpiAt pq r'')
    {r' : ℤ} (hr' : r ≤ r') : E.Z pq r' = E.Z pq r :=
  eq_of_forall_succ_eq (E.Z pq) (fun r'' h => have := H r'' h; E.Z_add_one_of_hasEdgeEpiAt pq r'')
    hr'

/-- If all differentials into `pq` vanish from the page `E_r` on, the tower `B` is constant
from `r` on. -/
theorem B_eq_of_forall_hasEdgeMonoAt {r : ℤ} (H : ∀ r'' (_ : r ≤ r''), E.HasEdgeMonoAt pq r'')
    {r' : ℤ} (hr' : r ≤ r') : E.B pq r' = E.B pq r :=
  eq_of_forall_succ_eq (E.B pq) (fun r'' h => have := H r'' h; E.B_add_one_of_hasEdgeMonoAt pq r'')
    hr'

/-- Stacks 011N meets Riou's edge maps: when the differentials into `pq` on `E_r` vanish, so
that `B_{r+1} = B_r`, the edge monomorphism `E_{r+1} ⟶ E_r` is, through `E_r ≅ Z_r/B_r` and
`E_{r+1} ≅ Z_{r+1}/B_{r+1}`, the map `Z_{r+1}/B_{r+1} ⟶ Z_r/B_r` induced by `Z_{r+1} ⊆ Z_r`. -/
@[reassoc]
theorem edgeMonoStep_pageIsoSubquotient_hom (r : ℤ) [E.HasEdgeMonoAt pq r] :
    E.edgeMonoStep pq r (r + 1) ≫ (E.pageIsoSubquotient pq r (E.le₀_of_hasEdgeMonoAt pq r)).hom =
      (E.pageIsoSubquotient pq (r + 1) (by have := E.le₀_of_hasEdgeMonoAt pq r; lia)).hom ≫
        cokernel.map _ _ (Subobject.ofLE _ _ (E.B_add_one_of_hasEdgeMonoAt pq r).le)
          (Subobject.ofLE _ _ ((E.Z_antitone pq).imp (by lia : r ≤ r + 1)))
          (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
  obtain ⟨k, rfl⟩ := Int.le.dest (E.le₀_of_hasEdgeMonoAt pq r)
  have aux : ∀ (n m : ℕ) (hn : n = k) (hm : m = k + 1) (h₁ : r₀ + k = r₀ + n)
      (h₂ : r₀ + k + 1 = r₀ + m),
      E.edgeMonoStep pq (r₀ + k) (r₀ + k + 1) ≫
          (E.pageXIsoOfEq pq _ _ h₁ ≪≫ (E.towerData pq n).iso).hom =
        (E.pageXIsoOfEq pq _ _ h₂ ≪≫ (E.towerData pq m).iso).hom ≫ cokernel.map _ _
          (Subobject.ofLE (E.towerData pq m).B (E.towerData pq n).B (by
            subst hn hm
            rw [towerData_succ]
            exact ((E.towerData pq _).step_B_of_d_eq_zero
              (E.d_eq_zero_of_hasEdgeMonoAt _ pq _)).le))
          (Subobject.ofLE (E.towerData pq m).Z (E.towerData pq n).Z (by
            subst hn hm
            rw [towerData_succ]
            exact (E.towerData pq _).step_Z_le))
          (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
    intro n m hn hm h₁ h₂
    subst hn hm
    simp [(E.towerData pq _).edgeMonoStep_iso_hom']
  exact aux _ _ (by lia) (by lia) (by lia) (by lia)

/-- Stacks 011N meets Riou's edge maps: when the differentials out of `pq` on `E_r` vanish, so
that `Z_{r+1} = Z_r`, the edge epimorphism `E_r ⟶ E_{r+1}` is, through `E_r ≅ Z_r/B_r` and
`E_{r+1} ≅ Z_{r+1}/B_{r+1}`, the map `Z_r/B_r ⟶ Z_{r+1}/B_{r+1}` induced by `B_r ⊆ B_{r+1}`. -/
@[reassoc]
theorem edgeEpiStep_pageIsoSubquotient_hom (r : ℤ) [E.HasEdgeEpiAt pq r] :
    E.edgeEpiStep pq r (r + 1) ≫
        (E.pageIsoSubquotient pq (r + 1) (by have := E.le₀_of_hasEdgeEpiAt pq r; lia)).hom =
      (E.pageIsoSubquotient pq r (E.le₀_of_hasEdgeEpiAt pq r)).hom ≫
        cokernel.map _ _ (Subobject.ofLE _ _ ((E.B_monotone pq).imp (by lia : r ≤ r + 1)))
          (Subobject.ofLE _ _ (E.Z_add_one_of_hasEdgeEpiAt pq r).ge)
          (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
  obtain ⟨k, rfl⟩ := Int.le.dest (E.le₀_of_hasEdgeEpiAt pq r)
  have aux : ∀ (n m : ℕ) (hn : n = k) (hm : m = k + 1) (h₁ : r₀ + k = r₀ + n)
      (h₂ : r₀ + k + 1 = r₀ + m),
      E.edgeEpiStep pq (r₀ + k) (r₀ + k + 1) ≫
          (E.pageXIsoOfEq pq _ _ h₂ ≪≫ (E.towerData pq m).iso).hom =
        (E.pageXIsoOfEq pq _ _ h₁ ≪≫ (E.towerData pq n).iso).hom ≫ cokernel.map _ _
          (Subobject.ofLE (E.towerData pq n).B (E.towerData pq m).B (by
            subst hn hm
            rw [towerData_succ]
            exact (E.towerData pq _).le_step_B))
          (Subobject.ofLE (E.towerData pq n).Z (E.towerData pq m).Z (by
            subst hn hm
            rw [towerData_succ]
            exact ((E.towerData pq _).step_Z_of_d_eq_zero
              (E.d_eq_zero_of_hasEdgeEpiAt pq _ _)).ge))
          (by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_comp_ofLE]) := by
    intro n m hn hm h₁ h₂
    subst hn hm
    simp only [Iso.trans_hom, pageXIsoOfEq_refl, Iso.refl_hom, id_comp]
    exact (E.towerData pq _).edgeEpiStep_iso_hom' _ _
  exact aux _ _ (by lia) (by lia) (by lia) (by lia)

/-! ### Stacks 011O (1): the limit `E_∞ = Z_∞/B_∞` -/

section Limit

variable {pq} {Zinf Binf : Subobject ((E.page r₀).X pq)}

/-- Every `B_r` lies below every `Z_s`, so `B_∞ = ⋃ B_r` lies below `Z_∞ = ⋂ Z_r`. -/
theorem le_of_isGLB_of_isLUB (hZ : IsGLB (Set.range (E.Z pq)) Zinf)
    (hB : IsLUB (Set.range (E.B pq)) Binf) : Binf ≤ Zinf := by
  refine hB.2 ?_
  rintro _ ⟨r, rfl⟩
  refine hZ.2 ?_
  rintro _ ⟨s, rfl⟩
  exact ((E.B_monotone pq (le_max_left r s)).trans (E.B_le_Z pq _)).trans
    (E.Z_antitone pq (le_max_right r s))

/-- Stacks 011O (1): if `Z_∞ = ⋂ Z_r` and `B_∞ = ⋃ B_r` exist as subobjects of `E_{r₀}`, the
limit of the spectral sequence at `pq` is `E_∞ = Z_∞/B_∞`. -/
@[stacks 011O "(1) limit `E_∞ = Z_∞/B_∞` when `⋂ Z_r` and `⋃ B_r` exist"]
noncomputable def limitObj (hZ : IsGLB (Set.range (E.Z pq)) Zinf)
    (hB : IsLUB (Set.range (E.B pq)) Binf) : C :=
  cokernel (Subobject.ofLE Binf Zinf (E.le_of_isGLB_of_isLUB hZ hB))

end Limit

/-! ### Stacks 011O (1) where the pages stabilise -/

section HasPageInfinityAt

variable [E.HasPageInfinityAt pq]

/-- The tower `Z` is constant from `rMin pq` on. -/
theorem Z_eq_of_rMin_le {r : ℤ} (hr : E.rMin pq ≤ r) : E.Z pq r = E.Z pq (E.rMin pq) :=
  E.Z_eq_of_forall_hasEdgeEpiAt pq
    (fun r'' h => E.hasEdgeEpiAt_of_rFromMin_LE pq r'' ((E.rFromMin_LE_rMin pq).trans h)) hr

/-- The tower `B` is constant from `rMin pq` on. -/
theorem B_eq_of_rMin_le {r : ℤ} (hr : E.rMin pq ≤ r) : E.B pq r = E.B pq (E.rMin pq) :=
  E.B_eq_of_forall_hasEdgeMonoAt pq
    (fun r'' h => E.hasEdgeMonoAt_of_rToMin_LE pq r'' ((E.rToMin_LE_rMin pq).trans h)) hr

/-- Stacks 011O (1): `Z_∞ = ⋂ Z_r` exists, and is `Z_{rMin}`, when the pages stabilise. -/
@[stacks 011O "(1), stabilising case: `Z_∞ = ⋂ Z_r` exists and is `Z_{rMin}`"]
theorem isGLB_range_Z : IsGLB (Set.range (E.Z pq)) (E.Z pq (E.rMin pq)) := by
  refine IsLeast.isGLB ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨r, rfl⟩
  rcases le_or_gt r (E.rMin pq) with h | h
  · exact E.Z_antitone pq h
  · exact (E.Z_eq_of_rMin_le pq h.le).ge

/-- Stacks 011O (1): `B_∞ = ⋃ B_r` exists, and is `B_{rMin}`, when the pages stabilise. -/
@[stacks 011O "(1), stabilising case: `B_∞ = ⋃ B_r` exists and is `B_{rMin}`"]
theorem isLUB_range_B : IsLUB (Set.range (E.B pq)) (E.B pq (E.rMin pq)) := by
  refine IsGreatest.isLUB ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨r, rfl⟩
  rcases le_or_gt r (E.rMin pq) with h | h
  · exact E.B_monotone pq h
  · exact (E.B_eq_of_rMin_le pq h.le).le

/-- Stacks 011O (1): `E_∞ = Z_∞/B_∞`, where `E_∞` is the stable page `pageInfinity`. -/
@[stacks 011O "(1), stabilising case: `pageInfinity ≅ Z_{rMin}/B_{rMin}`"]
noncomputable def pageInfinityIsoSubquotient :
    E.pageInfinity pq ≅
      cokernel (Subobject.ofLE (E.B pq (E.rMin pq)) (E.Z pq (E.rMin pq)) (E.B_le_Z pq _)) :=
  E.pageInfinityIso' pq ≪≫ E.pageIsoSubquotient pq (E.rMin pq) (E.LE_rMin pq)

/-- Stacks 011O (1), stabilising case: the limit `Z_∞/B_∞` is the stable page `pageInfinity`. -/
@[stacks 011O "(1), stabilising case: the limit `Z_∞/B_∞` is the stable page `pageInfinity`"]
noncomputable def limitObjIsoPageInfinity {Zinf Binf : Subobject ((E.page r₀).X pq)}
    (hZ : IsGLB (Set.range (E.Z pq)) Zinf) (hB : IsLUB (Set.range (E.B pq)) Binf) :
    E.limitObj hZ hB ≅ E.pageInfinity pq :=
  cokernel.mapIso _ _ (Subobject.isoOfEq _ _ (hB.unique (E.isLUB_range_B pq)))
    (Subobject.isoOfEq _ _ (hZ.unique (E.isGLB_range_Z pq)))
    (by simp [Subobject.ofLE_comp_ofLE]) ≪≫ (E.pageInfinityIsoSubquotient pq).symm

end HasPageInfinityAt

/-! ### Stacks 011O (2): degeneration -/

/-- Stacks 011O (2): the spectral sequence degenerates at `E_r` if `d_r, d_{r+1}, …` all
vanish. -/
@[stacks 011O "(2) degeneration at `E_r`: all differentials `d_{r'}`, `r' ≥ r`, vanish"]
def DegeneratesAt (r : ℤ) (hr : r₀ ≤ r := by lia) : Prop :=
  ∀ (r' : ℤ) (_ : r ≤ r') (pq pq' : κ), (E.page r').d pq pq' = 0

namespace DegeneratesAt

variable {E} {r : ℤ} {hr : r₀ ≤ r} (h : E.DegeneratesAt r hr)
include h

/-- Degeneration at `E_r` gives `HasEdgeEpiAt` at every position on every page `E_{r'}`,
`r' ≥ r`. -/
theorem hasEdgeEpiAt (r' : ℤ) (hr' : r ≤ r') (pq : κ) : E.HasEdgeEpiAt pq r' :=
  ⟨by lia, fun pq' => h r' hr' pq pq'⟩

/-- Degeneration at `E_r` gives `HasEdgeMonoAt` at every position on every page `E_{r'}`,
`r' ≥ r`. -/
theorem hasEdgeMonoAt (r' : ℤ) (hr' : r ≤ r') (pq : κ) : E.HasEdgeMonoAt pq r' :=
  ⟨by lia, fun pq' => h r' hr' pq' pq⟩

/-- Stacks 011O, remark: if the spectral sequence degenerates at `E_r`, the pages stabilise at
every position, so that Riou's `pageInfinity` is Stacks' limit `E_∞`. -/
theorem hasPageInfinityAt (pq : κ) : E.HasPageInfinityAt pq :=
  ⟨⟨r, hr, fun r' hr' => h.hasEdgeMonoAt r' hr' pq⟩,
    ⟨r, hr, fun r' hr' => h.hasEdgeEpiAt r' hr' pq⟩⟩

/-- Under degeneration at `E_r`, `Z_{r'} = Z_r` for all `r' ≥ r`. -/
theorem Z_eq (pq : κ) {r' : ℤ} (hr' : r ≤ r') : E.Z pq r' = E.Z pq r :=
  E.Z_eq_of_forall_hasEdgeEpiAt pq (fun r'' h'' => h.hasEdgeEpiAt r'' h'' pq) hr'

/-- Under degeneration at `E_r`, `B_{r'} = B_r` for all `r' ≥ r`. -/
theorem B_eq (pq : κ) {r' : ℤ} (hr' : r ≤ r') : E.B pq r' = E.B pq r :=
  E.B_eq_of_forall_hasEdgeMonoAt pq (fun r'' h'' => h.hasEdgeMonoAt r'' h'' pq) hr'

/-- Under degeneration at `E_r`, `rToMin pq ≤ r`. -/
theorem rToMin_le (pq : κ) [E.HasPageInfinityAt pq] : E.rToMin pq ≤ r :=
  E.rToMin_LE pq r ⟨hr, fun r' hr' => h.hasEdgeMonoAt r' hr' pq⟩

/-- Under degeneration at `E_r`, `rFromMin pq ≤ r`. -/
theorem rFromMin_le (pq : κ) [E.HasPageInfinityAt pq] : E.rFromMin pq ≤ r :=
  E.rFromMin_LE pq r ⟨hr, fun r' hr' => h.hasEdgeEpiAt r' hr' pq⟩

/-- Under degeneration at `E_r`, the stable page is reached at `r`: `rMin pq ≤ r`. -/
theorem rMin_le (pq : κ) [E.HasPageInfinityAt pq] : E.rMin pq ≤ r :=
  max_le (h.rToMin_le pq) (h.rFromMin_le pq)

/-- Under degeneration at `E_r`, all differentials into `pq` vanish from `E_r` on. -/
theorem hasEdgeMonoAtFrom (pq : κ) [E.HasPageInfinityAt pq] : E.HasEdgeMonoAtFrom pq r :=
  ⟨h.rToMin_le pq⟩

/-- Under degeneration at `E_r`, all differentials out of `pq` vanish from `E_r` on. -/
theorem hasEdgeEpiAtFrom (pq : κ) [E.HasPageInfinityAt pq] : E.HasEdgeEpiAtFrom pq r :=
  ⟨h.rFromMin_le pq⟩

/-- Stacks 011O, remark: under degeneration at `E_r`, `E_r = E_{r+1} = ⋯`: the pages `E_r` and
`E_{r'}` agree for `r ≤ r'`. -/
@[stacks 011O "remark: degeneration at `E_r` gives `E_r = E_{r+1} = ⋯`"]
noncomputable def pageIso (pq : κ) (r' : ℤ) (hr' : r ≤ r' := by lia) :
    (E.page r hr).X pq ≅ (E.page r' (hr.trans hr')).X pq :=
  haveI := h.hasPageInfinityAt pq
  haveI := h.hasEdgeMonoAtFrom pq
  haveI := h.hasEdgeEpiAtFrom pq
  E.edgeIsoSteps pq r r' hr'

/-- Stacks 011O, remark: if the spectral sequence degenerates at `E_r`, then
`E_r = E_{r+1} = ⋯ = E_∞`: at every position `pq`, the infinity page is `E_{r'}^{pq}` for every
`r' ≥ r`. -/
@[stacks 011O "remark: degeneration at `E_r` gives `E_r = E_{r+1} = ⋯ = E_∞`"]
noncomputable def pageInfinityIso (pq : κ) (r' : ℤ) (hr' : r ≤ r' := by lia) :
    E.pageInfinity pq ≅ (E.page r' (hr.trans hr')).X pq :=
  haveI := h.hasPageInfinityAt pq
  haveI := h.hasEdgeMonoAtFrom pq
  haveI := h.hasEdgeEpiAtFrom pq
  haveI := E.hasEdgeMonoAtFrom_of_GE pq r r' hr'
  haveI := E.hasEdgeEpiAtFrom_of_GE pq r r' hr'
  E.pageInfinityIso pq r'

end DegeneratesAt

namespace Ungraded

variable (E : Ungraded C r₀)

/-- `Z_{r₀+1} = Ker d_{r₀}` in `Ungraded.d` terms (the `next ()` of the general statement is
`()` by `Unit` eta). -/
lemma Z_add_one_self : E.Z () (r₀ + 1) = kernelSubobject (E.d r₀) :=
  SpectralSequence.Z_add_one_self E ()

/-- `B_{r₀+1} = Im d_{r₀}` in `Ungraded.d` terms. -/
lemma B_add_one_self : E.B () (r₀ + 1) = imageSubobject (E.d r₀) :=
  SpectralSequence.B_add_one_self E ()

/-- `Z_{r+1}` recursion in `Ungraded.d` terms. -/
lemma Z_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.Z () (r + 1) = (Subobject.map (E.Z () r).arrow).obj
      ((Subobject.pullback (E.q () r hr)).obj (kernelSubobject (E.d r))) :=
  SpectralSequence.Z_add_one E () r hr

/-- `B_{r+1}` recursion in `Ungraded.d` terms. -/
lemma B_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.B () (r + 1) = (Subobject.map (E.Z () r).arrow).obj
      ((Subobject.pullback (E.q () r hr)).obj (imageSubobject (E.d r))) :=
  SpectralSequence.B_add_one E () r hr

end Ungraded

end SpectralSequence

end CategoryTheory
