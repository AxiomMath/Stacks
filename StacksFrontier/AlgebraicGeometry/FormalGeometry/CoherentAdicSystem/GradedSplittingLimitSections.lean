module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplittingExists
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.RingTheory.ReesAlgebra.SmulDescend

/-!
# The sections of the limit of a coherent adic system are the limit of the sections

Let `X` be a scheme, let `ℐ` be a quasi-coherent ideal sheaf and let `(F_n)` be a coherent adic
system along `ℐ` with inverse limit `F = lim F_n`. The limit is taken in `𝒪_X`-modules, so its
sections over an open `U` are *a priori* only mapped to by the sections of the terms. In fact
evaluation at `U` preserves the limit — limits of sheaves of modules are computed on sections —
so

`Γ(lim F_n, U) = lim_m Γ(F_m, U)`,

the right-hand side being `Stacks.Coherent.sectionsLimit`. This file records that comparison and
its two consequences for [Stacks, Tag 0EH6]: the projections out of `Γ(F, U)` to the terms are
jointly injective, and relation-killing for `Stacks.Coherent.sectionsLimit` is relation-killing
for `Γ(F, U)`, which is the hypothesis that
`Stacks.Coherent.exists_gradedSplitting_of_killsRelationsHom_affineOpens` consumes.

The affine quotient presentation of the terms is stated for `Stacks.Coherent.sectionsLimit`
(`Stacks.Coherent.affineOpen_limit_projection_surjective` and
`Stacks.Coherent.affineOpen_limit_projection_ker`), while the existence half of
[Stacks, Tag 0EH6] is stated for `Γ(F, U)`; this comparison is what joins the two.

## Main definitions

* `Stacks.Coherent.limitSectionsIso` — evaluation at an open preserves the inverse limit of a
  tower of `𝒪_X`-modules.
* `Stacks.Coherent.sectionsOfLimitIso` — that comparison for the tower of a coherent adic
  system: `Γ(lim F_n, U) = lim_m Γ(F_m, U)`.

## Main results

* `Stacks.Coherent.sectionsOfLimitIso_hom_projection` — the comparison carries the restriction
  of the limit cone's projection to the projection of the limit of sections.
* `Stacks.Coherent.eq_zero_of_sectionsProjection_eq_zero` — a section of `F` over `U` killed by
  every projection is zero.
* `Stacks.Coherent.killsRelationsHom_sections_of_sectionsLimit` — relation-killing for
  `lim_m Γ(F_m, U)` is relation-killing for `Γ(F, U)`.
* `Stacks.Coherent.sum_eq_zero_sectionsSystem` — the shifted relation-killing statement for the
  tower `m ↦ Γ(F_m, W)` over an affine open, from relation-killing for `Γ(F, W)` and the affine
  quotient presentation of the terms. The exponent does not depend on `m`.
* `Stacks.Coherent.killsRelationsHom_sectionsLimit_basicOpen` — **relation-killing passes from
  an affine open to the basic opens inside it, without moving the exponent.**
* `Stacks.Coherent.killsRelationsHom_sections_of_basicOpen_charts` — and from the basic opens of
  the charts of an affine cover to every open.
* `Stacks.Coherent.exists_gradedSplitting_of_killsRelationsHom_charts` — hence the existence
  half of [Stacks, Tag 0EH6] granted relation-killing for `Γ(F, W)` for the charts `W` of *one*
  affine cover, which for a Noetherian `X` is a *finite* hypothesis — the shape
  [Stacks, Tag 0EIC] supplies through
  `Stacks.ReesAlgebra.exists_extendLinearMaps_killsRelationsHom_finset`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, so every
categorical construction is given its category explicitly as `(C := X.Modules)`, as elsewhere in
this directory. `SheafOfModules.evaluationPreservesLimit` is stated for the bare
`SheafOfModules.evaluation`, whose target is modules over `X.ringCatSheaf.obj.obj (op U)`; that
is the ring `Γ(X, U)` unfolds to, which is why no restriction of scalars is needed here, unlike
in `Stacks.Algebraization.affineSectionFunctor`.

## References

* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.ReesAlgebra Stacks.Cohomology.FormalFunctions
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-- The scalar action on `Stacks.Coherent.sectionsLimit`, at the `X.ringCatSheaf` spelling of
the ring of sections. The two spellings of `Γ(X, U)` are definitionally equal but not
syntactically so, and instance search does not bridge them; this is the same device as the
`local instance`s of `CoherentAdicSystem/AssociatedGraded.lean`. -/
local instance moduleSectionsLimitRingCatSheaf {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens) :
    Module (X.ringCatSheaf.obj.obj (op U)) (sectionsLimit F U) :=
  (sectionsLimit F U).isModule

/-! ### Evaluation at an open preserves the limit of a tower -/

/-- **Evaluation at an open preserves the inverse limit of a tower of `𝒪_X`-modules**: the
sections of the limit over `U` are the limit of the sections over `U`. -/
public def limitSectionsIso (D : ℕᵒᵖ ⥤ X.Modules) (U : X.Opens) :
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (limit (C := X.Modules) D) ≅
      limit (D ⋙ _root_.SheafOfModules.evaluation X.ringCatSheaf (op U)) :=
  IsLimit.conePointUniqueUpToIso
    (@isLimitOfPreserves _ _ _ _ _ _ _
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U))
      (limit.cone D) (limit.isLimit D)
      (_root_.SheafOfModules.evaluationPreservesLimit _ (op U)))
    (limit.isLimit _)

/-- The comparison of `Stacks.Coherent.limitSectionsIso` carries the restriction to `U` of the
`n`-th projection of the limit cone to the `n`-th projection of the limit of the sections. -/
public lemma limitSectionsIso_hom_π (D : ℕᵒᵖ ⥤ X.Modules) (U : X.Opens) (n : ℕ) :
    (limitSectionsIso D U).hom ≫
        limit.π (D ⋙ _root_.SheafOfModules.evaluation X.ringCatSheaf (op U)) (op n) =
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).map
        (limit.π (C := X.Modules) D (op n)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (op n)

/-! ### The comparison for a coherent adic system -/

/-- **`Γ(lim F_n, U) = lim_m Γ(F_m, U)`**: the sections over an open of the inverse limit of a
coherent adic system are the inverse limit of the sections of its terms. -/
public def sectionsOfLimitIso {I : X.IdealSheafData} (F : CoherentAdicSystems I) (U : X.Opens) :
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).obj
        (limit (C := X.Modules) F.obj) ≅
      sectionsLimit F U :=
  limitSectionsIso F.obj U

/-- The comparison `Γ(lim F_n, U) = lim_m Γ(F_m, U)` carries the restriction of the `n`-th
projection of the limit cone to `Stacks.Coherent.sectionsProjection`. -/
public lemma sectionsOfLimitIso_hom_projection {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens) (n : ℕ) :
    (sectionsOfLimitIso F U).hom ≫ sectionsProjection F U n =
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).map
        (limit.π (C := X.Modules) F.obj (op n)) :=
  limitSectionsIso_hom_π F.obj U n

/-- The comparison `Γ(lim F_n, U) = lim_m Γ(F_m, U)` is injective on sections. -/
public lemma sectionsOfLimitIso_injective {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens) :
    Function.Injective (sectionsOfLimitIso F U).hom.hom := by
  intro x y hxy
  have hinv : ∀ w, (sectionsOfLimitIso F U).inv.hom ((sectionsOfLimitIso F U).hom.hom w) = w :=
    fun w => ConcreteCategory.congr_hom (sectionsOfLimitIso F U).hom_inv_id w
  have h := congrArg (fun w => (sectionsOfLimitIso F U).inv.hom w) hxy
  rwa [hinv x, hinv y] at h

/-- A section of `lim_m Γ(F_m, U)` killed by every projection is zero. -/
private lemma eq_zero_of_forall_sectionsProjection {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens) (x : sectionsLimit F U)
    (h : ∀ m : ℕ, (sectionsProjection F U m).hom x = 0) : x = 0 := by
  refine Limits.Concrete.limit_ext (sectionsSystem F U) x 0 fun j => ?_
  have hj : limit.π (sectionsSystem F U) j x = (sectionsProjection F U j.unop).hom x := rfl
  rw [hj, h j.unop, map_zero]

/-- The projections out of `lim_m Γ(F_m, U)` are compatible with the transition maps. -/
private lemma sectionsProjection_transition {I : X.IdealSheafData} (F : CoherentAdicSystems I)
    (U : X.Opens) (j k : ℕ) (z : sectionsLimit F U) :
    ((sectionsSystem F U).map (homOfLE (Nat.le_add_right j k)).op).hom
        ((sectionsProjection F U (j + k)).hom z) = (sectionsProjection F U j).hom z :=
  ConcreteCategory.congr_hom (limit.w (sectionsSystem F U) (homOfLE (Nat.le_add_right j k)).op) z

/-- **A section of `F = lim F_n` over an open killed by every projection to a term is zero.**
The projections out of the sections of the limit are jointly injective, because the sections of
the limit *are* the limit of the sections. -/
public lemma eq_zero_of_sectionsProjection_eq_zero {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens)
    (x : (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).obj
      (limit (C := X.Modules) F.obj))
    (h : ∀ n : ℕ, (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).map
      (limit.π (C := X.Modules) F.obj (op n)) x = 0) :
    x = 0 := by
  refine sectionsOfLimitIso_injective F U ?_
  rw [map_zero]
  refine eq_zero_of_forall_sectionsProjection F U _ fun n => ?_
  exact (ConcreteCategory.congr_hom (sectionsOfLimitIso_hom_projection F U n) x).trans (h n)

/-! ### Relation-killing for the sections of the limit -/

/-- **Relation-killing for `lim_m Γ(F_m, U)` is relation-killing for `Γ(lim F_n, U)`.**

The two modules are identified by `Stacks.Coherent.sectionsOfLimitIso`, over the same ring
`Γ(X, U)` and hence for the same action of `A`; so
`Stacks.ReesAlgebra.killsRelationsHom_of_injective` transports the statement. This is what turns
the affine quotient presentation of the terms, which speaks of
`Stacks.Coherent.sectionsLimit`, into the hypothesis of
`Stacks.Coherent.exists_gradedSplitting_of_killsRelationsHom_affineOpens`, which speaks of the
sections of the limit sheaf. -/
public theorem killsRelationsHom_sections_of_sectionsLimit (A : Type u) [CommRing A]
    (J : Ideal A) (fX : X ⟶ Spec (.of A)) {I : X.IdealSheafData} (F : CoherentAdicSystems I)
    (U : X.Opens) {r d : ℕ} (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (h : KillsRelationsHom (baseSectionHom A fX U)
      (sectionsLimit F U : ModuleCat.{u} Γ(X, U)) J d ψ) :
    KillsRelationsHom (baseSectionHom A fX U)
      Γ(limit (C := X.Modules) F.obj, U) J d ψ :=
  killsRelationsHom_of_injective (baseSectionHom A fX U) (baseSectionHom A fX U)
    (sectionsOfLimitIso F U).hom.hom.toAddMonoidHom
    (fun a x => (sectionsOfLimitIso F U).hom.hom.map_smul (baseSectionHom A fX U a) x)
    (sectionsOfLimitIso_injective F U) h

/-! ### The shifted statement for the tower of sections over an affine open -/

/-- **The shifted relation-killing statement, for the tower of sections of the terms over an
affine open.**

On an affine open `W` of a Noetherian scheme the terms of the system are the quotients
`Γ(F_m, W) = Γ(F, W) / I(W) ^ (m + 1) Γ(F, W)` of the limit of the sections
(`Stacks.Coherent.affineOpen_limit_projection_surjective` and
`Stacks.Coherent.affineOpen_limit_projection_ker`), and `I(W) ^ (m + 1)` is generated by the
image of `J ^ (m + 1)` (`Stacks.Coherent.baseIdealSheaf_ideal_pow_eq_map`). So if the splitting
kills the relations of `Γ(F, W)` then, by
`Stacks.ReesAlgebra.sum_eq_zero_of_quotientTower`, a relation in degree `n` holding in
`Γ(F_{m + n d}, W)` forces the combination of coefficients to vanish in `Γ(F_m, W)` — with the
same exponent `d` for every `m`.

This is the step [Stacks, Tag 0EH6] performs when it reads the maps
`Φ^n_m : I ^ (n c) F_m ⟶ ⨁_{|e| = n} F_{m - n c}` off the single map `Φ_N`. -/
public theorem sum_eq_zero_sectionsSystem (A : Type u) [CommRing A] (J : Ideal A)
    [IsNoetherian X] (fX : X ⟶ Spec (.of A))
    (F : CoherentAdicSystems (baseIdealSheaf A J fX)) (W : X.affineOpens)
    {r d : ℕ} (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (h : KillsRelationsHom (baseSectionHom A fX W.1)
      (sectionsLimit F W.1 : ModuleCat.{u} Γ(X, W.1)) J d ψ)
    (n : ℕ) (σ : Fin r →₀ ℕ) (m p : ℕ) (g : Fin p → A)
    (hg : ∀ k, g k ∈ ((J ^ d : Ideal A) ^ n))
    (y : Fin p → (sectionsSystem F W.1).obj (op (m + n * d)))
    (hrel : (∑ k, baseSectionHom A fX W.1 (g k) • y k) = 0) :
    (∑ k, baseSectionHom A fX W.1 (extendCoeff J d n ψ σ ⟨g k, hg k⟩) •
        ((sectionsSystem F W.1).map (homOfLE (Nat.le_add_right m (n * d))).op).hom (y k)) = 0 :=
  sum_eq_zero_of_quotientTower (baseSectionHom A fX W.1) h
    (fun j => (sectionsProjection F W.1 j).hom)
    (fun j k => ((sectionsSystem F W.1).map (homOfLE (Nat.le_add_right j k)).op).hom)
    (fun j => affineOpen_limit_projection_surjective (baseIdealSheaf A J fX) F W j)
    (fun j => by
      rw [affineOpen_limit_projection_ker (baseIdealSheaf A J fX) F W j,
        baseIdealSheaf_ideal_pow_eq_map A J fX W (j + 1)])
    (fun j k z => sectionsProjection_transition F W.1 j k z)
    n σ m p g hg y hrel

/-! ### From an affine open to a basic open inside it -/

/-- A section of `lim_m Γ(F_m, U)` killed by every projection is zero. -/
public lemma eq_zero_of_sectionsProjection {I : X.IdealSheafData} (F : CoherentAdicSystems I)
    (U : X.Opens) (x : sectionsLimit F U)
    (h : ∀ m : ℕ, (sectionsProjection F U m).hom x = 0) : x = 0 :=
  eq_zero_of_forall_sectionsProjection F U x h

/-- The transition map of the system on the sections over a smaller open `V ≤ U`, as a linear
map for the action of `Γ(X, U)` through restriction. This is the shape in which the tower of
sections over `V` is a localization of the tower of sections over `U`: the localization is at a
submonoid of `Γ(X, U)`, so every map in sight has to be `Γ(X, U)`-linear. -/
public def transitionₗOfLE {I : X.IdealSheafData} (F : CoherentAdicSystems I)
    {V U : X.Opens} (hVU : V ≤ U) (j k : ℕ) :
    letI := moduleOfLE (F.obj.obj (op (j + k))) hVU
    letI := moduleOfLE (F.obj.obj (op j)) hVU
    Γ(F.obj.obj (op (j + k)), V) →ₗ[Γ(X, U)] Γ(F.obj.obj (op j), V) :=
  letI := moduleOfLE (F.obj.obj (op (j + k))) hVU
  letI := moduleOfLE (F.obj.obj (op j)) hVU
  { toFun := ((sectionsSystem F V).map (homOfLE (Nat.le_add_right j k)).op).hom
    map_add' := fun x y => map_add _ x y
    map_smul' := fun c x => ((sectionsSystem F V).map
      (homOfLE (Nat.le_add_right j k)).op).hom.map_smul
        ((X.presheaf.map (homOfLE hVU).op).hom c) x }

/-- **Relation-killing passes from an affine open to a basic open inside it**, and the exponent
does not move.

The sections of the *limit* over a basic open are not a localization of the sections over the
chart — that is the whole difficulty of [Stacks, Tag 0EH6] — but the sections of each *term*
are, `F_m` being coherent and hence quasi-coherent
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`). So the
shifted statement is transported level by level: it holds for the tower `m ↦ Γ(F_m, W)` by
`Stacks.Coherent.sum_eq_zero_sectionsSystem`, hence for the localized tower
`m ↦ Γ(F_m, X.basicOpen a)` by `Stacks.ReesAlgebra.sum_eq_zero_of_localizedTower`, and
`Stacks.ReesAlgebra.killsRelationsHom_of_shift` then gives relation-killing for
`lim_m Γ(F_m, X.basicOpen a)`, the projections of that limit being jointly injective.

This is the uniformity of the exponent: a single `d`, found once on the chart `W`, serves every
basic open inside it. -/
public theorem killsRelationsHom_sectionsLimit_basicOpen (A : Type u) [CommRing A] (J : Ideal A)
    [IsNoetherian X] (fX : X ⟶ Spec (.of A))
    (F : CoherentAdicSystems (baseIdealSheaf A J fX)) (W : X.affineOpens) (a : Γ(X, W.1))
    {r d : ℕ} (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (h : KillsRelationsHom (baseSectionHom A fX W.1)
      (sectionsLimit F W.1 : ModuleCat.{u} Γ(X, W.1)) J d ψ) :
    KillsRelationsHom (baseSectionHom A fX (X.basicOpen a))
      (sectionsLimit F (X.basicOpen a) : ModuleCat.{u} Γ(X, X.basicOpen a)) J d ψ := by
  have hle : X.basicOpen a ≤ W.1 := X.basicOpen_le a
  have hqc : ∀ j : ℕ, (F.obj.obj (op j)).IsQuasicoherent := fun j =>
    have : (F.obj.obj (op j)).IsCoherent := F.property.1 j
    isQuasicoherent_of_isCoherent (F.obj.obj (op j))
  have hloc : ∀ j : ℕ,
      letI := moduleOfLE (F.obj.obj (op j)) hle
      IsLocalizedModule (Submonoid.powers a) (restrictₗ (F.obj.obj (op j)) hle) := fun j =>
    have := hqc j
    isLocalizedModule_restrictₗ (F.obj.obj (op j)) W.2 a rfl hle
  have hbase : ∀ (j : ℕ) (c : A) (y : Γ(F.obj.obj (op j), X.basicOpen a)),
      baseSectionHom A fX (X.basicOpen a) c • y =
        (X.presheaf.map (homOfLE hle).op).hom (baseSectionHom A fX W.1 c) • y := by
    intro j c y
    rw [baseSectionHom_map]
  refine killsRelationsHom_of_shift (baseSectionHom A fX (X.basicOpen a)) J d ψ
    (fun j => (sectionsProjection F (X.basicOpen a) j).hom)
    (fun j k => ((sectionsSystem F (X.basicOpen a)).map
      (homOfLE (Nat.le_add_right j k)).op).hom) ?_ ?_ ?_
  · exact fun j k y => sectionsProjection_transition F _ j k y
  · exact fun y hy => eq_zero_of_sectionsProjection F _ y hy
  · intro n σ m p g hg z hrel
    have hrel' : (∑ k, (X.presheaf.map (homOfLE hle).op).hom
        (baseSectionHom A fX W.1 (g k)) • z k) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hrel
      exact (hbase (m + n * d) (g k) (z k)).symm
    have key := sum_eq_zero_of_localizedTower (baseSectionHom A fX W.1) J d ψ
      (P := fun j => (sectionsSystem F W.1).obj (op j))
      (Q := fun j => Γ(F.obj.obj (op j), X.basicOpen a))
      (instQM := fun j => moduleOfLE (F.obj.obj (op j)) hle)
      (instLoc := hloc)
      (fun j k => ((sectionsSystem F W.1).map (homOfLE (Nat.le_add_right j k)).op).hom)
      (fun j k => transitionₗOfLE F hle j k)
      (Submonoid.powers a) (fun j => restrictₗ (F.obj.obj (op j)) hle)
      (fun j k y => (app_presheaf_map
        (F.obj.map (homOfLE (Nat.le_add_right j k)).op) hle y).symm)
      (sum_eq_zero_sectionsSystem A J fX F W ψ h) n σ m p g hg z hrel'
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) key
    exact hbase m (extendCoeff J d n ψ σ ⟨g k, hg k⟩)
      (((sectionsSystem F (X.basicOpen a)).map
        (homOfLE (Nat.le_add_right m (n * d))).op).hom (z k))

/-! ### From the charts of an affine cover to every open -/

/-- **The basic opens of the charts of an affine cover that are contained in `V` cover `V`.**
Every point of `V` lies in a chart, and the basic opens of an affine open form a basis of it
(`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`). -/
public lemma le_iSup_basicOpen_charts {ι : Type u} (W : ι → X.affineOpens)
    (hcov : (⨆ i, (W i).1) = ⊤) (V : X.Opens) :
    V ≤ ⨆ q : { p : (i : ι) × Γ(X, (W i).1) // X.basicOpen p.2 ≤ V }, X.basicOpen q.1.2 := by
  intro x hx
  have hxtop : x ∈ (⨆ i, (W i).1) := hcov ▸ trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.1 hxtop
  obtain ⟨f, hfV, hxf⟩ := (W i).2.exists_basicOpen_le (⟨x, hx⟩ : V) hxi
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨i, f⟩, hfV⟩, hxf⟩

/-- **Relation-killing over the basic opens of the charts of an affine cover gives it over every
open.** The restrictions to those basic opens are jointly injective, by
`Stacks.Coherent.le_iSup_basicOpen_charts` and because `F` is a sheaf, and they are compatible
with the scalars by `Stacks.Coherent.baseSectionHom_map`. -/
public theorem killsRelationsHom_sections_of_basicOpen_charts (A : Type u) [CommRing A]
    (J : Ideal A) (fX : X ⟶ Spec (.of A)) (G : X.Modules) {r d : ℕ}
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A) {ι : Type u} (W : ι → X.affineOpens)
    (hcov : (⨆ i, (W i).1) = ⊤)
    (hkill : ∀ (i : ι) (a : Γ(X, (W i).1)),
      KillsRelationsHom (baseSectionHom A fX (X.basicOpen a)) Γ(G, X.basicOpen a) J d ψ)
    (V : X.Opens) : KillsRelationsHom (baseSectionHom A fX V) Γ(G, V) J d ψ := by
  refine killsRelationsHom_of_compat (baseSectionHom A fX V)
    (ι := { p : (i : ι) × Γ(X, (W i).1) // X.basicOpen p.2 ≤ V })
    (fun q => baseSectionHom A fX (X.basicOpen q.1.2))
    (fun q => (G.presheaf.map (homOfLE q.2).op).hom) ?_ ?_ fun q => hkill q.1.1 q.1.2
  · intro q c x
    change G.presheaf.map (homOfLE q.2).op (baseSectionHom A fX V c • x) = _
    rw [G.map_smul (homOfLE q.2), baseSectionHom_map]
  · intro s hs
    refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf G.isSheaf
      (fun q : { p : (i : ι) × Γ(X, (W i).1) // X.basicOpen p.2 ≤ V } => X.basicOpen q.1.2)
      (fun q => q.2) (le_iSup_basicOpen_charts W hcov V) fun q => ?_
    have h2 : G.presheaf.map (homOfLE q.2).op (0 : Γ(G, V)) = 0 := map_zero _
    exact (hs q).trans h2.symm

/-- **Stacks Project, Tag 0EH6**, the existence of the graded map, granted that the splitting
kills the relations of `Γ(F, W)` for the finitely many charts `W` of *one* affine cover of `X`.

This is the hypothesis in the shape [Stacks, Tag 0EIC] can supply it:
`Stacks.ReesAlgebra.exists_extendLinearMaps_killsRelationsHom_finset` produces a single
exponent for a *finite* family of modules, and
`Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top` provides
the finite affine cover of a Noetherian `X`. Everything between the charts and a general open is
discharged here: `Stacks.Coherent.killsRelationsHom_sectionsLimit_basicOpen` passes
relation-killing from a chart to the basic opens inside it without moving the exponent,
`Stacks.Coherent.killsRelationsHom_sections_of_sectionsLimit` moves it from the limit of the
sections to the sections of the limit, and
`Stacks.Coherent.killsRelationsHom_sections_of_basicOpen_charts` spreads it from those basic
opens to every open. -/
public theorem exists_gradedSplitting_of_killsRelationsHom_charts (A : Type u) [CommRing A]
    (J : Ideal A) [IsNoetherian X] (fX : X ⟶ Spec (.of A))
    (F : CoherentAdicSystems (baseIdealSheaf A J fX)) {r d : ℕ}
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A) {ι : Type u} (W : ι → X.affineOpens)
    (hcov : (⨆ i, (W i).1) = ⊤)
    (hchart : ∀ i : ι, KillsRelationsHom (baseSectionHom A fX (W i).1)
      (sectionsLimit F (W i).1 : ModuleCat.{u} Γ(X, (W i).1)) J d ψ) :
    ∃ Ψ : GradedSplittingComponents A J fX (limit (C := X.Modules) F.obj) r d,
      IsGradedSplitting A J fX (limit (C := X.Modules) F.obj) d ψ Ψ :=
  exists_gradedSplitting_of_killsRelationsHom A J fX _ ψ
    (killsRelationsHom_sections_of_basicOpen_charts A J fX _ ψ W hcov fun i a =>
      killsRelationsHom_sections_of_sectionsLimit A J fX F (X.basicOpen a) ψ
        (killsRelationsHom_sectionsLimit_basicOpen A J fX F (W i) a ψ (hchart i)))

end Stacks.Coherent

end
