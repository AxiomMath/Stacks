module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.BoundaryChernComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Shifted short exact sequences from unshifted ones

Stacks Tag 0FMW and Tag 0FUF produce short exact sequences of complexes of the shape

`0 → P → M → N[-1] → 0`,

and the proofs of Tags 0FUG and 0FUQ read their boundary maps off the translated sequences
`0 → P[1] → M[1] → N → 0` ("we define `δ` as the boundary map corresponding to the shifted short
exact sequence"). This file performs that translation: it turns an unshifted sequence into a
`Stacks.ShiftedBoundary.Sequence`, whose boundary map `N ⟶ P[2]` is the one of the source.

## Main definitions

* `Stacks.ShiftedBoundary.Sequence.ofShortExact`: the translate by one of a short exact sequence
  `0 → P → M → N[-1] → 0`, with the canonical identification `N[-1][1] ≅ N` on its right-hand
  term.
* `Stacks.ShiftedBoundary.Morphism.ofShortExact`: a morphism of unshifted sequences, over maps
  `p : P₁ ⟶ P₂` and `n : N₁ ⟶ N₂` on the outer terms (`n[-1]` on the right-hand terms), gives a
  morphism of the shifted sequences over `p` and `n`.
* `Stacks.ShiftedBoundary.Sequence.map`: the image of a shifted short exact sequence under an exact
  functor.

## Main results

* `Stacks.ShiftedBoundary.Sequence.map_boundary`: the boundary map of the image of a shifted short
  exact sequence under an exact functor is the image of its boundary map.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w v u

namespace Stacks.ShiftedBoundary

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace Sequence

variable {P M N : CochainComplex C ℤ} (i : P ⟶ M) (r : M ⟶ N⟦(-1 : ℤ)⟧) (w : i ≫ r = 0)
  (hS : (ShortComplex.mk i r w).ShortExact)

/-- The canonical identification `N[-1][1] ≅ N`. -/
abbrev unshiftIso (N : CochainComplex C ℤ) : N⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅ N :=
  (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).app N

/-- **The translate by one of a short exact sequence `0 → P → M → N[-1] → 0`**: the shifted short
exact sequence `0 → P[1] → M[1] → N → 0`, with the canonical identification `N[-1][1] ≅ N` on its
right-hand term. -/
def ofShortExact : Sequence P N where
  middle := M⟦(1 : ℤ)⟧
  incl := i⟦(1 : ℤ)⟧'
  res := r⟦(1 : ℤ)⟧' ≫ (unshiftIso N).hom
  incl_comp_res := by
    rw [← Category.assoc, ← Functor.map_comp, w, Functor.map_zero, zero_comp]
  shortExact := by
    refine ShortComplex.shortExact_of_iso ?_
      (hS.map_of_exact (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (unshiftIso N)
      ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)

omit [HasDerivedCategory C] in
/-- The middle term of `ofShortExact i r w hS` is `M[1]`. -/
@[simp]
theorem ofShortExact_middle : (ofShortExact i r w hS).middle = M⟦(1 : ℤ)⟧ := rfl

omit [HasDerivedCategory C] in
/-- The inclusion of `ofShortExact i r w hS` is the translate `i[1]`. -/
@[simp]
theorem ofShortExact_incl : (ofShortExact i r w hS).incl = i⟦(1 : ℤ)⟧' := rfl

omit [HasDerivedCategory C] in
/-- The projection of `ofShortExact i r w hS` is the translate `r[1]` followed by
`N[-1][1] ≅ N`. -/
@[simp]
theorem ofShortExact_res : (ofShortExact i r w hS).res = r⟦(1 : ℤ)⟧' ≫ (unshiftIso N).hom := rfl

end Sequence

namespace Morphism

variable {P₁ M₁ N₁ P₂ M₂ N₂ : CochainComplex C ℤ}
  {i₁ : P₁ ⟶ M₁} {r₁ : M₁ ⟶ N₁⟦(-1 : ℤ)⟧} {w₁ : i₁ ≫ r₁ = 0}
  {hS₁ : (ShortComplex.mk i₁ r₁ w₁).ShortExact}
  {i₂ : P₂ ⟶ M₂} {r₂ : M₂ ⟶ N₂⟦(-1 : ℤ)⟧} {w₂ : i₂ ≫ r₂ = 0}
  {hS₂ : (ShortComplex.mk i₂ r₂ w₂).ShortExact}

/-- **A morphism of unshifted short exact sequences gives a morphism of the shifted ones**: for
maps `p : P₁ ⟶ P₂`, `m : M₁ ⟶ M₂` and `n : N₁ ⟶ N₂` with `i₁ ≫ m = p ≫ i₂` and
`m ≫ r₂ = r₁ ≫ n[-1]`, the translate `m[1]` is a morphism of the shifted sequences over `p`
and `n`. -/
def ofShortExact (p : P₁ ⟶ P₂) (m : M₁ ⟶ M₂) (n : N₁ ⟶ N₂) (h₁ : i₁ ≫ m = p ≫ i₂)
    (h₂ : m ≫ r₂ = r₁ ≫ n⟦(-1 : ℤ)⟧') :
    Morphism (Sequence.ofShortExact i₁ r₁ w₁ hS₁) (Sequence.ofShortExact i₂ r₂ w₂ hS₂) p n where
  mid := m⟦(1 : ℤ)⟧'
  comm_incl := by
    change p⟦(1 : ℤ)⟧' ≫ i₂⟦(1 : ℤ)⟧' = i₁⟦(1 : ℤ)⟧' ≫ m⟦(1 : ℤ)⟧'
    rw [← Functor.map_comp, ← Functor.map_comp, h₁]
  comm_res := by
    change m⟦(1 : ℤ)⟧' ≫ (r₂⟦(1 : ℤ)⟧' ≫ (Sequence.unshiftIso N₂).hom) =
      (r₁⟦(1 : ℤ)⟧' ≫ (Sequence.unshiftIso N₁).hom) ≫ n
    have hn : n⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫ (Sequence.unshiftIso N₂).hom =
        (Sequence.unshiftIso N₁).hom ≫ n :=
      (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).hom.naturality n
    rw [← Category.assoc, ← Functor.map_comp, h₂, Functor.map_comp, Category.assoc, hn,
      Category.assoc]

end Morphism

/-! ### Shifted sequences under an exact functor -/

section Map

variable {C₂ : Type u} [Category.{v} C₂] [Abelian C₂] [HasDerivedCategory.{w} C₂]
  (F : C ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace Sequence

variable {P N : CochainComplex C ℤ} (S : Sequence P N)

/-- **The image of a shifted short exact sequence under an exact functor**, again in the shifted
presentation: `0 → F(P)[1] → F(M) → F(N) → 0`, the left-hand term being identified with
`F(P[1])` by the commutation of `F` with the translation. -/
noncomputable def map :
    Sequence ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) where
  middle := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj S.middle
  incl := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app P ≫
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map S.incl
  res := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map S.res
  incl_comp_res := by
    rw [Category.assoc, ← Functor.map_comp, S.incl_comp_res, Functor.map_zero, comp_zero]
  shortExact := by
    refine ShortComplex.shortExact_of_iso ?_
      (S.shortExact.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ)))
    exact ShortComplex.isoMk
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app P)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- **The boundary map of the image of a shifted short exact sequence under an exact functor is
the image of the boundary map**, conjugated by the identifications of `F` on derived categories
with `F` on complexes and by the commutation of `F` with the translation by two. -/
theorem map_boundary :
    (S.map F).boundary =
      F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map S.boundary ≫
        (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app (DerivedCategory.Q.obj P) ≫
          (F.mapDerivedCategoryFactors.hom.app P)⟦(2 : ℤ)⟧' := by
  let F' := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let φ : (S.map F).shortComplex ⟶ S.shortComplex.map F' :=
    { τ₁ := (F'.commShiftIso (1 : ℤ)).inv.app P
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have hnat := DerivedCategory.triangleOfSESδ_naturality (S.map F).shortExact
    (S.shortExact.map_of_exact F') φ
  have hmap := DerivedCategory.map_triangleOfSESδ F S.shortExact
  have hδ : DerivedCategory.triangleOfSESδ (S.map F).shortExact =
      DerivedCategory.triangleOfSESδ (S.shortExact.map_of_exact F') ≫
        (DerivedCategory.Q.map ((F'.commShiftIso (1 : ℤ)).hom.app P))⟦(1 : ℤ)⟧' := by
    have h : DerivedCategory.triangleOfSESδ (S.map F).shortExact ≫
        (DerivedCategory.Q.map ((F'.commShiftIso (1 : ℤ)).inv.app P))⟦(1 : ℤ)⟧' =
        DerivedCategory.triangleOfSESδ (S.shortExact.map_of_exact F') := by
      refine hnat.trans ?_
      change DerivedCategory.Q.map (𝟙 _) ≫ _ = _
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← h, Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·)
      (((congrArg (shiftFunctor (DerivedCategory C₂) (1 : ℤ)).map
        (DerivedCategory.Q.map_id _)).trans
        ((shiftFunctor (DerivedCategory C₂) (1 : ℤ)).map_id _)).symm))
  have ha := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom (1 : ℤ) P
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at ha
  have hb : F.mapDerivedCategory.map
        ((shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 (by omega)).inv.app
          (DerivedCategory.Q.obj P)) ≫
        (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app (DerivedCategory.Q.obj P) =
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app ((DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧) ≫
        ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj P))⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory C₂) (1 : ℤ) 1 2 (by omega)).inv.app
            (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
    rw [Functor.commShiftIso_add' F.mapDerivedCategory (show (1 : ℤ) + 1 = 2 by omega),
      Functor.CommShift.isoAdd'_hom_app, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hc : ∀ {X Y : DerivedCategory C} (g : X ⟶ Y),
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app X ≫
        F.mapDerivedCategory.map (g⟦(1 : ℤ)⟧') ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app Y =
          (F.mapDerivedCategory.map g)⟦(1 : ℤ)⟧' := fun g => by
    rw [Functor.commShiftIso_hom_naturality, Iso.inv_hom_id_app_assoc]
  have hd := (shiftFunctorAdd' (DerivedCategory C₂) (1 : ℤ) 1 2 (by omega)).inv.naturality
    (F.mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hd
  rw [boundary, boundary, hδ, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    hmap]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hb, reassoc_of% (hc ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P)),
    ← hd]
  have key : F.mapDerivedCategoryFactors.inv.app (P⟦(1 : ℤ)⟧) ≫
      F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj P) ≫
          (F.mapDerivedCategoryFactors.hom.app P)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map ((F'.commShiftIso (1 : ℤ)).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (F'.obj P) := by
    rw [← Category.assoc (F.mapDerivedCategory.map _), ha, Iso.inv_hom_id_app_assoc]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  rw [key]

end Sequence

namespace Morphism

variable {P M N : CochainComplex C ℤ} {i : P ⟶ M} {r : M ⟶ N⟦(-1 : ℤ)⟧} {w : i ≫ r = 0}
  {hS : (ShortComplex.mk i r w).ShortExact}
  {P₁ M₁ N₁ : CochainComplex C₂ ℤ} {i₁ : P₁ ⟶ M₁} {r₁ : M₁ ⟶ N₁⟦(-1 : ℤ)⟧} {w₁ : i₁ ≫ r₁ = 0}
  {hS₁ : (ShortComplex.mk i₁ r₁ w₁).ShortExact}

/-- **A morphism of unshifted short exact sequences into the image of one under an exact functor
gives a morphism of the shifted sequences**: for `p : P₁ ⟶ F(P)`, `m : M₁ ⟶ F(M)` and
`n : N₁ ⟶ F(N)` with `i₁ ≫ m = p ≫ F(i)` and `m ≫ F(r) = r₁ ≫ n[-1]` (up to the commutation of
`F` with the translation), the translate of `m` is a morphism from the shifted first sequence to
the image of the shifted second one, over `p` and `n`. -/
def toMapOfShortExact (p : P₁ ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (m : M₁ ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (n : N₁ ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    (h₁ : i₁ ≫ m = p ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map i)
    (h₂ : m ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map r ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1 : ℤ)).hom.app N =
      r₁ ≫ n⟦(-1 : ℤ)⟧') :
    Morphism (Sequence.ofShortExact i₁ r₁ w₁ hS₁) ((Sequence.ofShortExact i r w hS).map F) p n where
  mid := m⟦(1 : ℤ)⟧' ≫
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app M
  comm_incl := by
    change p⟦(1 : ℤ)⟧' ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app P ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (i⟦(1 : ℤ)⟧') =
      i₁⟦(1 : ℤ)⟧' ≫ m⟦(1 : ℤ)⟧' ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app M
    rw [← Functor.commShiftIso_inv_naturality, ← Category.assoc, ← Functor.map_comp,
      ← Category.assoc, ← Functor.map_comp, h₁]
  comm_res := by
    change (m⟦(1 : ℤ)⟧' ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app M) ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (r⟦(1 : ℤ)⟧' ≫ (Sequence.unshiftIso N).hom) =
      (r₁⟦(1 : ℤ)⟧' ≫ (Sequence.unshiftIso N₁).hom) ≫ n
    have hn : n⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
        (Sequence.unshiftIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).hom =
        (Sequence.unshiftIso N₁).hom ≫ n :=
      (shiftFunctorCompIsoId (CochainComplex C₂ ℤ) (-1 : ℤ) 1 (by omega)).hom.naturality n
    have hu : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Sequence.unshiftIso N).hom =
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
            (N⟦(-1 : ℤ)⟧) ≫
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1 : ℤ)).hom.app
            N)⟦(1 : ℤ)⟧' ≫
            (Sequence.unshiftIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).hom :=
      Functor.map_shiftFunctorCompIsoId_hom_app _ N (-1 : ℤ) 1 (by omega)
    have h₂' : (m ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map r) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1 : ℤ)).hom.app N =
        r₁ ≫ n⟦(-1 : ℤ)⟧' := (Category.assoc _ _ _).trans h₂
    rw [Functor.map_comp, hu, Category.assoc, ← Functor.commShiftIso_inv_naturality_assoc,
      Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h₂',
      Functor.map_comp, Category.assoc, hn, Category.assoc]

end Morphism

end Map

end Stacks.ShiftedBoundary
