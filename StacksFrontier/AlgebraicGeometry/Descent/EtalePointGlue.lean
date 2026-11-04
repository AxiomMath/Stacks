module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleSectionGlue
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.HomPresheaf

/-!
# Glueing points of a quasi-coherent module along an étale covering

A *point* of a module `M` on a scheme `S` is a morphism `𝒪_S ⟶ M` out of the structure sheaf,
where `𝒪_S` is `AlgebraicGeometry.Scheme.unitModule S`.  Points and global sections are the same
thing, so Stacks 03DT — the sheaf condition of the presheaf of Stacks 03DS for the étale
topology — can be read on points instead of on global sections.  This file supplies that
reading: the dictionary between points and global sections, the two restriction operations on
points, their compatibility with the restriction maps on global sections, and the resulting
glueing theorem.

## Main definitions

* `AlgebraicGeometry.pointSectionEquiv`: a point of `M` is a global section of `M`.
* `AlgebraicGeometry.pullbackPoint`: the restriction of a point of `M` along a morphism
  `φ : T ⟶ S`, a point of `φ⁺M`.
* `AlgebraicGeometry.restrictPoint`: the restriction of a point of `φ⁺M` along a morphism
  `ρ : V ⟶ T` over `S`, a point of `ψ⁺M` for a factorisation `ρ ≫ φ = ψ`.

## Main results

* `AlgebraicGeometry.pointSectionEquiv_pullbackPoint` and
  `AlgebraicGeometry.pointSectionEquiv_restrictPoint`: the dictionary carries `pullbackPoint`
  and `restrictPoint` to `AlgebraicGeometry.coverSectionsMap` and
  `AlgebraicGeometry.pullbackSectionsMap`, which are the restriction maps that
  `AlgebraicGeometry.existsUnique_glue_etale` is stated with.
* `AlgebraicGeometry.restrictPoint_pullbackPoint`: restricting the restriction of a point is
  restricting it along the composite.
* `AlgebraicGeometry.existsUnique_glue_point`: **the glueing theorem for points.**  Points of
  the pullbacks of a quasi-coherent module `M` to the members of an étale cover of `S` which
  agree on the pairwise fibre products come from a unique point of `M`.
* `AlgebraicGeometry.point_eq_of_etale_cover`: the separatedness half, stated on its own.

## Implementation notes

Everything is transported along `AlgebraicGeometry.pointSectionEquiv`, which is
`AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` read backwards; the glueing theorems are
`AlgebraicGeometry.existsUnique_glue_etale` and
`AlgebraicGeometry.section_eq_of_etale_cover` carried across it.  The whole content is therefore
the compatibility of the dictionary with restriction, and that is proved once, for a morphism
`g` of `Over S`, in the private lemma `unitHomEquivTop_pullbackSectionsMap`: the morphism
`𝒪_V ⟶ ψ⁺M` attached to the restriction of a global section of `φ⁺M` along `g` is the
restriction of the morphism `𝒪_T ⟶ φ⁺M` attached to that section.  Its proof is
`AlgebraicGeometry.pullbackSectionsHomEquiv_naturality`, which says the same thing about
morphisms `ψ⁺𝒪_S ⟶ ψ⁺M` out of the pulled-back structure sheaf, composed with
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`, which replaces `ψ⁺𝒪_S` by `𝒪_V`
compatibly with the factorisation `ρ ≫ φ = ψ`.

`pullbackPoint` is the restriction along `φ : T ⟶ S` of a point of a module on `S`, and
`restrictPoint` is the restriction of a point of a module *already pulled back* to `T`; the
first is not an instance of the second, because `coverSectionsMap` — the restriction map of
global sections that `existsUnique_glue_etale` uses — is the value of the presheaf of Tag 03DS
at `Over.homMk φ : Over.mk φ ⟶ Over.mk (𝟙 S)` read through
`AlgebraicGeometry.pullbackIdSectionsIso`.  Comparing the two therefore needs the unit
coherence of the pullback pseudofunctor, which is the private lemma
`map_pullbackId_inv_app`, a component of Mathlib's
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality`.

The index universe of the cover is left free, `AlgebraicGeometry.Scheme.Cover.{v}`, exactly as
in `AlgebraicGeometry.existsUnique_glue_etale`.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory Opposite Limits
open scoped AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

variable {S T V : Scheme.{u}}

/-! ### Points and global sections -/

/-- **A point of a module is a global section of it.**  A point of `M` is a morphism from the
structure sheaf, and `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` identifies those with
the global sections of `M`. -/
noncomputable def pointSectionEquiv (M : S.Modules) :
    (Scheme.unitModule S ⟶ M) ≃ Γ(M, ⊤) :=
  (Scheme.Modules.unitHomEquivTop M).symm

/-- The global section attached to the point attached to a global section is that section. -/
@[simp]
lemma pointSectionEquiv_unitHomEquivTop (M : S.Modules) (x : Γ(M, ⊤)) :
    pointSectionEquiv M (Scheme.Modules.unitHomEquivTop M x) = x :=
  (Scheme.Modules.unitHomEquivTop M).symm_apply_apply x

/-- The point attached to the global section attached to a point is that point. -/
@[simp]
lemma unitHomEquivTop_pointSectionEquiv (M : S.Modules) (p : Scheme.unitModule S ⟶ M) :
    Scheme.Modules.unitHomEquivTop M (pointSectionEquiv M p) = p :=
  (Scheme.Modules.unitHomEquivTop M).apply_symm_apply p

/-! ### Restriction of points -/

/-- **Restriction of a point of `M` along a morphism `φ : T ⟶ S`.**  Pull the morphism
`𝒪_S ⟶ M` back along `φ` and identify `φ⁺𝒪_S` with `𝒪_T` by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
noncomputable def pullbackPoint (φ : T ⟶ S) {M : S.Modules} (p : Scheme.unitModule S ⟶ M) :
    Scheme.unitModule T ⟶ (Scheme.Modules.pullback φ).obj M :=
  (Scheme.Modules.pullbackUnitIso φ).inv ≫ (Scheme.Modules.pullback φ).map p

/-- **Restriction of a point of `φ⁺M` along a morphism over `S`.**  For a factorisation
`ρ ≫ φ = ψ`, a point of `φ⁺M` on `T` restricts to a point of `ψ⁺M` on `V`: pull the morphism
`𝒪_T ⟶ φ⁺M` back along `ρ`, identify `ρ⁺𝒪_T` with `𝒪_V`, and identify `ρ⁺φ⁺M` with `ψ⁺M` by
the comparison isomorphisms `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
noncomputable def restrictPoint (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S) (w : ρ ≫ φ = ψ)
    {M : S.Modules} (q : Scheme.unitModule T ⟶ (Scheme.Modules.pullback φ).obj M) :
    Scheme.unitModule V ⟶ (Scheme.Modules.pullback ψ).obj M :=
  (Scheme.Modules.pullbackUnitIso ρ).inv ≫ (Scheme.Modules.pullback ρ).map q ≫
    (Scheme.Modules.pullbackComp ρ φ).hom.app M ≫
    (Scheme.Modules.pullbackCongr w).hom.app M

/-- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq` with the comparison isomorphisms
inverted: the identification of `ψ⁺𝒪_S` with `𝒪_V` is the identification of `φ⁺𝒪_S` with `𝒪_T`
pulled back along `ρ`. -/
private lemma pullbackUnitIso_inv_comp (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S) (w : ρ ≫ φ = ψ) :
    (Scheme.Modules.pullbackUnitIso ψ).inv =
      (Scheme.Modules.pullbackUnitIso ρ).inv ≫
        (Scheme.Modules.pullback ρ).map (Scheme.Modules.pullbackUnitIso φ).inv ≫
        (Scheme.Modules.pullbackComp ρ φ).hom.app (Scheme.unitModule S) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Scheme.unitModule S) := by
  rw [← cancel_epi ((Scheme.Modules.pullbackUnitIso ψ).hom), Iso.hom_inv_id,
    ← Scheme.Modules.pullbackUnitIso_comp_eq ρ φ ψ w]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

/-- **Restricting the restriction of a point is restricting along the composite.** -/
lemma restrictPoint_pullbackPoint (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S) (w : ρ ≫ φ = ψ)
    {M : S.Modules} (p : Scheme.unitModule S ⟶ M) :
    restrictPoint ρ φ ψ w (pullbackPoint φ p) = pullbackPoint ψ p := by
  have h1 := (Scheme.Modules.pullbackComp ρ φ).hom.naturality p
  have h2 := (Scheme.Modules.pullbackCongr w).hom.naturality p
  simp only [Functor.comp_map] at h1
  simp only [restrictPoint, pullbackPoint, pullbackUnitIso_inv_comp ρ φ ψ w, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% h1, h2]

/-! ### The dictionary is compatible with restriction -/

/-- The section of a module attached to a global section is natural in the module. -/
private lemma sectionsTopEquiv_naturality {X : Scheme.{u}} {M N : X.Modules} (α : M ⟶ N)
    (x : Γ(M, ⊤)) :
    Scheme.Modules.sectionsTopEquiv N (α.app ⊤ x) =
      SheafOfModules.sectionsMap α (Scheme.Modules.sectionsTopEquiv M x) := by
  ext U
  rw [Scheme.Modules.sectionsMap_val, Scheme.Modules.sectionsTopEquiv_val,
    Scheme.Modules.sectionsTopEquiv_val, Scheme.Modules.Hom.app_presheaf_map]

/-- **The point attached to a global section is natural in the module.**  The point of `N`
attached to the image of a global section of `M` under `α : M ⟶ N` is the point of `M` attached
to that section, followed by `α`. -/
private lemma unitHomEquivTop_naturality {X : Scheme.{u}} {M N : X.Modules} (α : M ⟶ N)
    (x : Γ(M, ⊤)) :
    Scheme.Modules.unitHomEquivTop N (α.app ⊤ x) =
      Scheme.Modules.unitHomEquivTop M x ≫ α :=
  (SheafOfModules.unitHomEquiv N).injective
    (((Scheme.Modules.unitHomEquiv_unitHomEquivTop N (α.app ⊤ x)).trans
        (sectionsTopEquiv_naturality α x)).trans
      ((SheafOfModules.unitHomEquiv_comp_apply (Scheme.Modules.unitHomEquivTop M x) α).trans
        (congrArg (SheafOfModules.sectionsMap α)
          (Scheme.Modules.unitHomEquiv_unitHomEquivTop M x))).symm)

/-- The restriction map of the presheaf of morphisms of
`AlgebraicGeometry.modulePullbackPseudofunctor`, written out in terms of the comparison
isomorphisms of iterated pullback.  This is
`AlgebraicGeometry.modulePullbackPseudofunctor_pullHom` read at a morphism of `Over S`. -/
private lemma presheafHom_map_apply (M : S.Modules) {U T : Over S} (g : U ⟶ T)
    (z : (Scheme.Modules.pullback T.hom).obj (Scheme.unitModule S) ⟶
      (Scheme.Modules.pullback T.hom).obj M) :
    (modulePullbackPseudofunctor.presheafHom (Scheme.unitModule S) M).map (op g) z =
      (Scheme.Modules.pullbackCongr (Over.w g)).inv.app (Scheme.unitModule S) ≫
        (Scheme.Modules.pullbackComp g.left T.hom).inv.app (Scheme.unitModule S) ≫
        (Scheme.Modules.pullback g.left).map z ≫
        (Scheme.Modules.pullbackComp g.left T.hom).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app M :=
  modulePullbackPseudofunctor_pullHom g.left T.hom U.hom (Over.w g) (Scheme.unitModule S) M z

/-- **The dictionary carries `AlgebraicGeometry.pullbackSectionsMap` to
`AlgebraicGeometry.restrictPoint`.**  The global section attached to the restriction of a point
of `φ⁺M` along a morphism `g` of `Over S` is the restriction of the global section attached to
that point. -/
private lemma pointSectionEquiv_restrictPoint_over (M : S.Modules) {U T : Over S} (g : U ⟶ T)
    (q : Scheme.unitModule T.left ⟶ (Scheme.Modules.pullback T.hom).obj M) :
    pointSectionEquiv _ (restrictPoint g.left T.hom U.hom (Over.w g) q) =
      pullbackSectionsMap M g (pointSectionEquiv _ q) := by
  have h := pullbackSectionsHomEquiv_naturality M g (pointSectionEquiv _ q)
  rw [pullbackSectionsHomEquiv_apply, pullbackSectionsHomEquiv_apply,
    presheafHom_map_apply, unitHomEquivTop_pointSectionEquiv] at h
  apply (Scheme.Modules.unitHomEquivTop _).injective
  rw [← cancel_epi ((Scheme.Modules.pullbackUnitIso U.hom).hom), h, restrictPoint,
    unitHomEquivTop_pointSectionEquiv,
    ← Scheme.Modules.pullbackUnitIso_comp_eq g.left T.hom U.hom (Over.w g)]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_assoc]

/-- The left unitality coherence of the pullback pseudofunctor, at a module: identifying `M`
with `(𝟙 S)⁺M`, pulling that back along `f` and identifying `f⁺(𝟙 S)⁺M` with `f⁺M` is the
identity.  This is a component of
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality`. -/
private lemma map_pullbackId_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).inv.app F) ≫
        (Scheme.Modules.pullbackComp f (𝟙 Y)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Category.comp_id f)).hom.app F =
      𝟙 ((Scheme.Modules.pullback f).obj F) := by
  have p := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, CategoryTheory.Functor.id_obj, eqToHom_app, Category.comp_id] at p
  have hD : (Scheme.Modules.pullbackCongr (Category.comp_id f)).hom.app F =
      (Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app F ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app F) := by
    rw [p]
    simp [Scheme.Modules.pullbackCongr]
  rw [hD, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (Scheme.Modules.pullback f).map_id _

/-- **The dictionary carries `AlgebraicGeometry.coverSectionsMap` to
`AlgebraicGeometry.pullbackPoint`.**  The global section attached to the restriction of a point
of `M` along `φ : T ⟶ S` is the restriction of the global section attached to that point. -/
theorem pointSectionEquiv_pullbackPoint (φ : T ⟶ S) (M : S.Modules)
    (p : Scheme.unitModule S ⟶ M) :
    pointSectionEquiv _ (pullbackPoint φ p) = coverSectionsMap M φ (pointSectionEquiv M p) := by
  have h := pointSectionEquiv_restrictPoint_over M (Over.homMk φ : Over.mk φ ⟶ Over.mk (𝟙 S))
    (p ≫ (Scheme.Modules.pullbackId S).inv.app M)
  have h2 : Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback (𝟙 S)).obj M)
        ((pullbackIdSectionsIso S M).inv (pointSectionEquiv M p)) =
      Scheme.Modules.unitHomEquivTop M (pointSectionEquiv M p) ≫
        (Scheme.Modules.pullbackId S).inv.app M :=
    unitHomEquivTop_naturality _ _
  rw [unitHomEquivTop_pointSectionEquiv] at h2
  replace h2 := congrArg (pointSectionEquiv _) h2.symm
  rw [pointSectionEquiv_unitHomEquivTop] at h2
  have h3 : restrictPoint φ (𝟙 S) φ (Category.comp_id φ)
      (p ≫ (Scheme.Modules.pullbackId S).inv.app M) = pullbackPoint φ p := by
    rw [restrictPoint, pullbackPoint, Functor.map_comp]
    simp only [Category.assoc]
    rw [map_pullbackId_inv_app, Category.comp_id]
  exact (congrArg _ h3.symm).trans (h.trans (congrArg _ h2))

/-- **The dictionary carries `AlgebraicGeometry.pullbackSectionsMap` to
`AlgebraicGeometry.restrictPoint`.**  The global section attached to the restriction of a point
of `φ⁺M` along `ρ : V ⟶ T` over `S` is the restriction of the global section attached to that
point, along the corresponding morphism of `Over S`. -/
theorem pointSectionEquiv_restrictPoint (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S) (w : ρ ≫ φ = ψ)
    (M : S.Modules) (q : Scheme.unitModule T ⟶ (Scheme.Modules.pullback φ).obj M) :
    pointSectionEquiv _ (restrictPoint ρ φ ψ w q) =
      pullbackSectionsMap M (Over.homMk ρ w : Over.mk ψ ⟶ Over.mk φ)
        (pointSectionEquiv _ q) :=
  pointSectionEquiv_restrictPoint_over M (Over.homMk ρ w : Over.mk ψ ⟶ Over.mk φ) q

/-! ### Glueing -/

/-- **Glueing points of a quasi-coherent module along an étale covering.**  Let `M` be a
quasi-coherent module on a scheme `S` and let `𝒰` be an étale cover of `S`.  A family of points
`q i` of the pullbacks of `M` to the members of `𝒰` whose two restrictions to each fibre product
`𝒰.X i ×_S 𝒰.X j` agree is the family of restrictions of a unique point of `M`.

This is `AlgebraicGeometry.existsUnique_glue_etale` transported along
`AlgebraicGeometry.pointSectionEquiv`; the two restrictions are compared as points of the
pullback of `M` along the structure morphism `pullback.fst ≫ 𝒰.f i` of
`AlgebraicGeometry.coverPair`, with `CategoryTheory.Limits.pullback.condition` identifying it
with `pullback.snd ≫ 𝒰.f j`. -/
theorem existsUnique_glue_point (M : S.Modules) [M.IsQuasicoherent]
    (𝒰 : S.Cover.{v} Scheme.etalePrecoverage.{u})
    (q : ∀ i, Scheme.unitModule (𝒰.X i) ⟶ (Scheme.Modules.pullback (𝒰.f i)).obj M)
    (hq : ∀ i j, restrictPoint (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f i)
          (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl (q i) =
        restrictPoint (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f j)
          (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm (q j)) :
    ∃! p : Scheme.unitModule S ⟶ M, ∀ i, pullbackPoint (𝒰.f i) p = q i := by
  have hs : ∀ i j, pullbackSectionsMap M (coverPairFst 𝒰 i j) (pointSectionEquiv _ (q i)) =
      pullbackSectionsMap M (coverPairSnd 𝒰 i j) (pointSectionEquiv _ (q j)) := by
    intro i j
    have h1 := pointSectionEquiv_restrictPoint (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f i)
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl M (q i)
    have h2 := pointSectionEquiv_restrictPoint (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f j)
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm M (q j)
    rw [hq i j] at h1
    exact h1.symm.trans h2
  obtain ⟨t, ht, huniq⟩ :=
    existsUnique_glue_etale M 𝒰 (fun i ↦ pointSectionEquiv _ (q i)) hs
  refine ⟨Scheme.Modules.unitHomEquivTop M t, fun i ↦ ?_, fun p hp ↦ ?_⟩
  · have h := pointSectionEquiv_pullbackPoint (𝒰.f i) M (Scheme.Modules.unitHomEquivTop M t)
    rw [pointSectionEquiv_unitHomEquivTop, ht i] at h
    exact (pointSectionEquiv _).injective h
  · have hcompat : ∀ i, coverSectionsMap M (𝒰.f i) (pointSectionEquiv M p) =
        pointSectionEquiv _ (q i) := by
      intro i
      rw [← pointSectionEquiv_pullbackPoint, hp i]
    rw [← huniq (pointSectionEquiv M p) hcompat, unitHomEquivTop_pointSectionEquiv]

/-- **Two points of a quasi-coherent module which agree on an étale cover are equal.**  The
separatedness half of `AlgebraicGeometry.existsUnique_glue_point`, stated on its own: it is
`AlgebraicGeometry.section_eq_of_etale_cover` transported along
`AlgebraicGeometry.pointSectionEquiv`. -/
theorem point_eq_of_etale_cover (M : S.Modules) [M.IsQuasicoherent]
    (𝒰 : S.Cover.{v} Scheme.etalePrecoverage.{u}) {p₁ p₂ : Scheme.unitModule S ⟶ M}
    (h : ∀ i, pullbackPoint (𝒰.f i) p₁ = pullbackPoint (𝒰.f i) p₂) : p₁ = p₂ := by
  apply (pointSectionEquiv M).injective
  refine section_eq_of_etale_cover M 𝒰 fun i ↦ ?_
  rw [← pointSectionEquiv_pullbackPoint, ← pointSectionEquiv_pullbackPoint, h i]

end AlgebraicGeometry

end
