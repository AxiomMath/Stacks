module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Step
public import StacksFrontier.AlgebraicGeometry.LimitApprox.DescendOpen
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Shrinking

/-!
# The one-affine-open step of Tag 07RN

Let `S` be a quasi-separated scheme, `V` a quasi-compact open of it which is the inverse limit of
a directed system `D` of finite-type schemes with affine transition morphisms, and `Y` an affine
open with `V ⊔ Y = ⊤`.  This file proves that `S` is then approximated relative to `V`, by a
system whose index projects cofinally to the index of `D`.  This is the single-affine-open step
of Tag 07RN; the induction over a finite affine cover is
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIsOneAffineOpenStep`.

## Main results

* `AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine`: the one-affine-open step of
  Tag 07RN.
* `AlgebraicGeometry.exists_approximation_of_lateStage`: the same step, from a charting family
  living at a single stage of the system.

## Implementation notes

* The index is shrunk twice: once onto the stages above the one at which the overlap `V ⊓ Y`
  descends to a compatible family of quasi-compact opens, and once more onto the stages above the
  one at which the charting family lives, the family being pushed to the later stages by
  `Stacks.transportedFam` so that it is stagewise compatible. Each shrink carries the limiting
  cone by `AlgebraicGeometry.isLimitWhiskerOfCofinal`; both are undone at the end by
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofWhisker`.

* Tag 01Z0 is applied to the limiting cone over the models of the overlap whose vertex is the
  overlap *as an open of the base*, so the ring of the fibre products is `Γ(V ⊓ Y, ⊤)`.

* One scheme universe is used; the index preorders live in it.  The two shrunk index preorders
  are `Set.Ici` subtypes, which stay in the same universe.

* The level-two data is the level-one data whiskered, and is *definitionally* so: the compatible
  family, the preimage condition, the two cones and the restricted limiting cone at level two are
  each introduced by a `have` with the level-two spelling written out and the level-one term as
  the proof.  That is where the second shrink is paid for.

* `AlgebraicGeometry.isAffineOpen_basicOpen_laterFam` is a term-mode `Eq.mpr` of a `congrArg` and
  not a rewrite: `rw` reports no occurrence of a pattern the goal visibly contains, the standard
  open being written through the reducible definition of the shrunk diagram.

* The affineness of the transition morphisms of the shrunk models is declared as an instance here
  rather than left to search, which halts one layer in at the plain composite.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks Stacks.GluedStep Stacks.StageSubalgebra

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

section Pushdown

variable {K : Type u} [Preorder K] {Dv : Kᵒᵈ ⥤ Scheme.{u}} (W : ∀ a, (Dv.obj a).Opens)
  (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a) (k₁ : K)

/-- A compatible family of opens, restricted to the stages above one of them. -/
@[reducible] noncomputable def laterW (a : (↥(Set.Ici k₁))ᵒᵈ) :
    ((laterDiagram Dv k₁).obj a).Opens :=
  W ((laterStages k₁).monotone.dual.functor.obj a)

include hW in
/-- The restricted family is again compatible. -/
lemma laterW_compatible ⦃a b : (↥(Set.Ici k₁))ᵒᵈ⦄ (v : a ⟶ b) :
    (laterDiagram Dv k₁).map v ⁻¹ᵁ laterW W k₁ b = laterW W k₁ a := hW _

/-- The base point of the shrunk index is below every stage of it. -/
lemma bot_le_Ici (k : ↥(Set.Ici k₁)) : (⟨k₁, le_rfl⟩ : ↥(Set.Ici k₁)) ≤ k := k.2

/-- The models of the overlap over the shrunk index. -/
@[reducible] noncomputable def laterMdl : (↥(Set.Ici k₁))ᵒᵈ ⥤ Scheme.{u} :=
  mdl (Dv := laterDiagram Dv k₁) (laterW W k₁) (laterW_compatible W hW k₁)

/-- The transition morphisms of the models of the overlap over the shrunk index are affine. -/
instance isAffineHom_laterMdl_map [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    {a b : (↥(Set.Ici k₁))ᵒᵈ} (v : a ⟶ b) : IsAffineHom ((laterMdl W hW k₁).map v) :=
  isAffineHom_compatibleOpensDiagram_map _ (laterW_compatible W hW k₁) v

variable {n : ℕ} (f₁ : Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁), ⊤))

/-- The charting family at one stage, pushed to every later stage along the transition
morphisms. -/
@[reducible] noncomputable def laterFam (k : ↥(Set.Ici k₁)) (l : Fin n) :
    Γ((laterMdl W hW k₁).obj (OrderDual.toDual k), ⊤) :=
  Stacks.transportedFam (secK (Dv := laterDiagram Dv k₁) (laterW W k₁)
    (laterW_compatible W hW k₁)) ⟨k₁, le_rfl⟩ (bot_le_Ici k₁) f₁ k l

/-- The standard open of the pushed family is the inverse image of the standard open at the one
stage. -/
lemma basicOpen_laterFam (k : ↥(Set.Ici k₁)) (l : Fin n) :
    ((laterMdl W hW k₁).obj (OrderDual.toDual k)).basicOpen (laterFam W hW k₁ f₁ k l) =
      (laterMdl W hW k₁).map
          (homOfLE (OrderDual.toDual_le_toDual.mpr (bot_le_Ici k₁ k))) ⁻¹ᵁ
        ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).basicOpen (f₁ l) :=
  (Scheme.preimage_basicOpen_top ((laterMdl W hW k₁).map
    (homOfLE (OrderDual.toDual_le_toDual.mpr (bot_le_Ici k₁ k)))) (f₁ l)).symm

/-- **The standard opens of the pushed charting family are affine.** -/
lemma isAffineOpen_basicOpen_laterFam [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    (haff₁ : ∀ l, IsAffineOpen
      (((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).basicOpen (f₁ l)))
    (k : ↥(Set.Ici k₁)) (l : Fin n) :
    IsAffineOpen (((laterMdl W hW k₁).obj (OrderDual.toDual k)).basicOpen
      (laterFam W hW k₁ f₁ k l)) :=
  Eq.mpr (congrArg IsAffineOpen (basicOpen_laterFam W hW k₁ f₁ k l))
    (@IsAffineOpen.preimage _ _ _ (haff₁ l) ((laterMdl W hW k₁).map
      (homOfLE (OrderDual.toDual_le_toDual.mpr (bot_le_Ici k₁ k))))
      (isAffineHom_laterMdl_map W hW k₁ _))

/-- **The standard opens of the pushed charting family cover the model.** -/
lemma iSup_basicOpen_laterFam_eq_top
    (hcov₁ : ⨆ l, ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).basicOpen (f₁ l) = ⊤)
    (k : ↥(Set.Ici k₁)) :
    ⨆ l, ((laterMdl W hW k₁).obj (OrderDual.toDual k)).basicOpen
      (laterFam W hW k₁ f₁ k l) = ⊤ := by
  refine top_unique fun x _ ↦ Opens.mem_iSup.mpr ?_
  have hx : ((laterMdl W hW k₁).map
      (homOfLE (OrderDual.toDual_le_toDual.mpr (bot_le_Ici k₁ k)))).base x ∈
      (⊤ : ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).Opens) := trivial
  rw [← hcov₁] at hx
  obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hx
  exact ⟨l, (basicOpen_laterFam W hW k₁ f₁ k l).ge hl⟩

end Pushdown

section LaterCone

variable {K : Type u} [Preorder K] [Nonempty K] [IsDirected K (· ≤ ·)]
  {Dv : Kᵒᵈ ⥤ Scheme.{u}} [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
  {S : Scheme.{u}} {V Y : S.Opens}
  (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
  (W : ∀ a, (Dv.obj a).Opens)
  (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
  (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y) (k₁ : K)

/-- The given cone over the stages, restricted to the stages above `k₁`. -/
@[reducible] noncomputable def laterPv :
    (Functor.const ((↥(Set.Ici k₁))ᵒᵈ)).obj (V : Scheme.{u}) ⟶ laterDiagram Dv k₁ :=
  ((Cone.mk (V : Scheme.{u}) pv).whisker (laterStages k₁).monotone.dual.functor).π

omit [Nonempty K] [IsDirected K (· ≤ ·)] [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)] in
include hT in
/-- The restricted family still cuts the overlap out of the vertex. -/
lemma laterT (a : (↥(Set.Ici k₁))ᵒᵈ) :
    (laterPv pv k₁).app a ⁻¹ᵁ laterW W k₁ a = V.ι ⁻¹ᵁ Y := hT _

include hT in
/-- The limiting cone over the models of the overlap, restricted. -/
noncomputable def isLimit_laterCw (hovl : IsLimit (cw pv W hW hT)) :
    IsLimit (cw (laterPv pv k₁) (laterW W k₁) (laterW_compatible W hW k₁)
      (laterT pv W hT k₁)) :=
  have : Nonempty ↥(Set.Ici k₁) := Stacks.Order.nonempty_Ici k₁
  have : IsDirected ↥(Set.Ici k₁) (· ≤ ·) := Stacks.Order.isDirected_Ici k₁
  isLimitWhiskerOfCofinal (laterStages k₁) (exists_le_laterStages k₁) hovl

include hT in
/-- **Tag 01Z0 for the restricted models of the overlap:** the sections of the overlap are the
filtered colimit of the sections of its models over the stages above `k₁`. -/
noncomputable def isColimit_Γ_mapCocone_laterCw (hovl : IsLimit (cw pv W hW hT))
    (hWc : ∀ a : Kᵒᵈ, IsCompact ((W a : (Dv.obj a).Opens) : Set (Dv.obj a)))
    (hqs : ∀ a : Kᵒᵈ, QuasiSeparatedSpace (Dv.obj a)) :
    IsColimit (Scheme.Γ.mapCocone (cw (laterPv pv k₁) (laterW W k₁)
      (laterW_compatible W hW k₁) (laterT pv W hT k₁)).op) :=
  have : Nonempty ↥(Set.Ici k₁) := Stacks.Order.nonempty_Ici k₁
  have : IsDirected ↥(Set.Ici k₁) (· ≤ ·) := Stacks.Order.isDirected_Ici k₁
  have : ∀ a, CompactSpace ((laterMdl W hW k₁).obj a) :=
    compactSpace_compatibleOpensDiagram_obj _ (laterW_compatible W hW k₁) fun _ ↦ hWc _
  have : ∀ a, QuasiSeparatedSpace ((laterMdl W hW k₁).obj a) :=
    quasiSeparatedSpace_compatibleOpensDiagram_obj _ (laterW_compatible W hW k₁) fun _ ↦ hqs _
  (nonempty_isColimit_Γ_mapCocone _ _ (isLimit_laterCw pv W hW hT k₁ hovl)).some

end LaterCone

section LaterFam

/-- **The pushed charting family still lifts the chosen sections of the affine open.** -/
lemma tau_laterFam {K : Type u} [Preorder K] {Dv : Kᵒᵈ ⥤ Scheme.{u}}
    {S : Scheme.{u}} {V Y : S.Opens}
    (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
    (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y) (k₁ : K) {n : ℕ}
    (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
    (f₁ : Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁), ⊤))
    (hf₁ : ∀ l, (tau pv W hW hT).app (op (OrderDual.toDual k₁)) (f₁ l) =
      str (V := V) (Y := Y) (g l))
    (k : ↥(Set.Ici k₁)) (l : Fin n) :
    (tau (laterPv pv k₁) (laterW W k₁) (laterW_compatible W hW k₁)
          (laterT pv W hT k₁)).app (op (OrderDual.toDual k)) (laterFam W hW k₁ f₁ k l) =
      str (V := V) (Y := Y) (g l) :=
  (Stacks.app_transportedFam (secK (Dv := laterDiagram Dv k₁) (laterW W k₁)
    (laterW_compatible W hW k₁)) ⟨k₁, le_rfl⟩ (bot_le_Ici k₁) f₁
    (tauK (laterPv pv k₁) (laterW W k₁) (laterW_compatible W hW k₁)
      (laterT pv W hT k₁)) k l).trans (hf₁ l)

/-- **The pushed charting family is stagewise compatible.** -/
lemma map_laterFam {K : Type u} [Preorder K] {Dv : Kᵒᵈ ⥤ Scheme.{u}}
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a) (k₁ : K) {n : ℕ}
    (f₁ : Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁), ⊤))
    ⦃k k' : ↥(Set.Ici k₁)⦄ (u : k ⟶ k') (l : Fin n) :
    (secK (Dv := laterDiagram Dv k₁) (laterW W k₁) (laterW_compatible W hW k₁)).map u
        (laterFam W hW k₁ f₁ k l) = laterFam W hW k₁ f₁ k' l :=
  Stacks.map_transportedFam (secK (Dv := laterDiagram Dv k₁) (laterW W k₁)
    (laterW_compatible W hW k₁)) ⟨k₁, le_rfl⟩ (bot_le_Ici k₁) f₁ u l

end LaterFam

/-- An approximation over a system restricted along a cofinal map yields one over the system. -/
private theorem exists_approximation_of_whisker {I K : Type u} [Preorder I] [Preorder K]
    {D : Iᵒᵈ ⥤ Scheme.{u}} (E : K →o I) (hE : ∀ i, ∃ k, i ≤ E k) {S : Scheme.{u}}
    {U : S.Opens} {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}
    (h : ∃ A : Scheme.FiniteTypeApproximation (E.monotone.dual.functor ⋙ D) S U
      ((Cone.mk (U : Scheme.{u}) p).whisker E.monotone.dual.functor).π,
      ∀ k, ∃ j : A.indexType, k ≤ A.index j) :
    ∃ A : Scheme.FiniteTypeApproximation D S U p, ∀ i, ∃ j : A.indexType, i ≤ A.index j :=
  let ⟨A, hA⟩ := h
  ⟨A.ofWhisker E, exists_le_comp A.index E hA hE⟩

/-- **The one-affine-open step, from a charting family at a single late stage.**  The second
shrink of the index: restrict to the stages above `k₁`, push the charting family down along the
transition morphisms, and apply `Stacks.GluedStep.exists_approximation`. -/
theorem exists_approximation_of_lateStage {K : Type u} [Preorder K] [Nonempty K]
    [IsDirected K (· ≤ ·)]
    {Dv : Kᵒᵈ ⥤ Scheme.{u}} [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    [∀ a, LocallyOfFiniteType (terminal.from (Dv.obj a))]
    [∀ a, QuasiCompact (terminal.from (Dv.obj a))]
    {S : Scheme.{u}} {V Y : S.Opens} [IsAffine (Y : Scheme.{u})]
    (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
    (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)
    (hWc : ∀ a : Kᵒᵈ, IsCompact ((W a : (Dv.obj a).Opens) : Set (Dv.obj a)))
    (hqs : ∀ a : Kᵒᵈ, QuasiSeparatedSpace (Dv.obj a))
    (hS : V ⊔ Y = ⊤)
    (hpv : IsLimit (Cone.mk (V : Scheme.{u}) pv))
    (hovl : IsLimit (cw pv W hW hT))
    {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
    (hin : ∀ l, (Y : Scheme.{u}).basicOpen (g l) ≤
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange)
    (hgcov : (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange ≤
      ⨆ l, (Y : Scheme.{u}).basicOpen (g l))
    (k₁ : K) (f₁ : Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁), ⊤))
    (hf₁ : ∀ l, (tau pv W hW hT).app (op (OrderDual.toDual k₁)) (f₁ l) =
      str (V := V) (Y := Y) (g l))
    (haff₁ : ∀ l, IsAffineOpen
      (((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).basicOpen (f₁ l)))
    (hcov₁ : ⨆ l, ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).basicOpen (f₁ l) = ⊤) :
    ∃ A : Scheme.FiniteTypeApproximation Dv S V pv,
      ∀ k : K, ∃ j : A.indexType, k ≤ A.index j := by
  classical
  have hne₂ : Nonempty ↥(Set.Ici k₁) := Stacks.Order.nonempty_Ici k₁
  have hdir₂ : IsDirected ↥(Set.Ici k₁) (· ≤ ·) := Stacks.Order.isDirected_Ici k₁
  have hpv₂ : IsLimit (Cone.mk (V : Scheme.{u}) (laterPv pv k₁)) :=
    isLimitWhiskerOfCofinal (laterStages k₁) (exists_le_laterStages k₁) hpv
  refine exists_approximation_of_whisker (laterStages k₁) (exists_le_laterStages k₁) ?_
  exact Stacks.GluedStep.exists_approximation (laterPv pv k₁)
    (laterW W k₁) (laterW_compatible W hW k₁) (laterT pv W hT k₁) (fun a ↦ hWc _) hS
    hpv₂ (isLimit_laterCw pv W hW hT k₁ hovl)
    (isColimit_Γ_mapCocone_laterCw pv W hW hT k₁ hovl hWc hqs)
    g hin hgcov (laterFam W hW k₁ f₁)
    (tau_laterFam pv W hW hT k₁ g f₁ hf₁) (fun u l ↦ map_laterFam W hW k₁ f₁ u l)
    (isAffineOpen_basicOpen_laterFam W hW k₁ f₁ haff₁)
    (iSup_basicOpen_laterFam_eq_top W hW k₁ f₁ hcov₁)

/-- **The one-affine-open step of Tag 07RN.**  A directed system of finite-type schemes with
affine transition morphisms whose limit is a quasi-compact open `V` of a quasi-separated scheme
`S` extends to a system approximating `S`, as soon as `V` together with one affine open covers
`S`.  The index of the extended system projects cofinally to the original one. -/
theorem exists_finiteTypeApproximation_of_sup_affine {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵈ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵈ} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
    [∀ i, QuasiCompact (terminal.from (D.obj i))]
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (V Y : S.Opens) [CompactSpace (V : Scheme.{u})]
    (hY : IsAffineOpen Y) (hS : V ⊔ Y = ⊤)
    (p : (Functor.const Iᵒᵈ).obj (V : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (V : Scheme.{u}) p)) :
    ∃ A : Scheme.FiniteTypeApproximation D S V p, ∀ i : I, ∃ j : A.indexType, i ≤ A.index j := by
  classical
  have hYaff : IsAffine (Y : Scheme.{u}) := hY
  -- the overlap descends to a compatible family of quasi-compact opens
  obtain ⟨i₀, V₀, hV₀c, hV₀⟩ := exists_stage_preimage_eq_inf D V p hp Y hY.isCompact
  have hne₁ : Nonempty ↥(Set.Ici i₀) := Stacks.Order.nonempty_Ici i₀
  have hdir₁ : IsDirected ↥(Set.Ici i₀) (· ≤ ·) := Stacks.Order.isDirected_Ici i₀
  have hqs₁ : ∀ a : (↥(Set.Ici i₀))ᵒᵈ, QuasiSeparatedSpace ((laterDiagram D i₀).obj a) :=
    fun _ ↦ quasiSeparatedSpace_of_locallyOfFiniteType_terminal _
  have hT₁ : ∀ a, (laterPv p i₀).app a ⁻¹ᵁ laterPreimage D V₀ a = V.ι ⁻¹ᵁ Y :=
    laterPreimage_preimage_eq D V p V₀ hV₀
  have hpv₁ : IsLimit (Cone.mk (V : Scheme.{u}) (laterPv p i₀)) :=
    isLimitWhiskerOfCofinal (laterStages i₀) (exists_le_laterStages i₀) hp
  have hovl₁ : IsLimit (cw (laterPv p i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀) hT₁ (Y := Y)) :=
    isLimitOverlapCone V Y (laterPv p i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀) hT₁ (isLimitLaterCompatibleOpensCone D V p hp V₀ hV₀)
  have hmc₁ : ∀ a, CompactSpace ((mdl (Dv := laterDiagram D i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀)).obj a) :=
    compactSpace_compatibleOpensDiagram_obj _ (laterPreimage_compatible D V₀)
      (isCompact_laterPreimage D V₀ hV₀c)
  have hmqs₁ : ∀ a, QuasiSeparatedSpace ((mdl (Dv := laterDiagram D i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀)).obj a) :=
    quasiSeparatedSpace_compatibleOpensDiagram_obj _ (laterPreimage_compatible D V₀) hqs₁
  have hzc : CompactSpace ((V ⊓ Y : S.Opens) : Scheme.{u}) :=
    Scheme.compactSpace_of_isLimit _ _ hovl₁
  -- the finite family of sections of the affine open whose standard opens cover the overlap
  obtain ⟨n, g, hin, hgcov⟩ :=
    exists_fin_basicOpen_le_opensRange (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y))
  -- the charting family at one stage
  obtain ⟨j₁, f₁, hf₁, haff₁, hcov₁⟩ :=
    exists_stage_affine_basicOpen_cover_of_opensRange _ _ hovl₁
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)) g hin hgcov
  refine exists_approximation_of_whisker (laterStages i₀) (exists_le_laterStages i₀) ?_
  exact exists_approximation_of_lateStage (laterPv p i₀) (laterPreimage D V₀)
    (laterPreimage_compatible D V₀) hT₁ (isCompact_laterPreimage D V₀ hV₀c) hqs₁ hS hpv₁ hovl₁
    g hin hgcov (OrderDual.ofDual j₁) f₁ hf₁ haff₁ hcov₁

end AlgebraicGeometry
