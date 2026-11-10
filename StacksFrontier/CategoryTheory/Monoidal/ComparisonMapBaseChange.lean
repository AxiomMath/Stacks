module

public import StacksFrontier.CategoryTheory.Adjunction.CounitHomExt
public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChangeUnitCounit
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaDualizable
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap

/-!
# The projection and comparison maps under base change

Consider a square of monoidal categories

```
     Lf
  S ---→ T
Lg |     | Lg'
   v     v
  S' --→ T'
     Lf'
```

whose four functors are oplax monoidal with right adjoints `Rf, Rf', Rg, Rg'`, the two composites
around the square being identified with one functor (`eg`, `ef`), compatibly with the oplax
structures. The *projection map* `K ⊗ Rf E ⟶ Rf (Lf K ⊗ E)` of `Lf ⊣ Rf`
(`CategoryTheory.Adjunction.projectionMap`) is compatible with the base change map
`β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` (`Stacks.CategoryTheory.BaseChange.twoSquare`); this is the categorical
content of [Stacks, Tag 0B6B]. If moreover `Rf ⊣ a` and `Rf' ⊣ a'`, the projection maps are
invertible and `β` is invertible, the *comparison map* `Lf K ⊗ a L ⟶ a (K ⊗ L)`
(`CategoryTheory.Adjunction.comparisonMap`, the two-variable form of Equation 48.8.0.1) is
compatible with `β` and with the base change map `α : a ⋙ Lg' ⟶ Lg ⋙ a'` of the right adjoints
(`Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange`); this is the categorical content of
[Stacks, Tag 0B6P], and its proof is the source's: the comparison map is built from the unit, the
inverse projection map and the trace, and each piece is compatible with base change by
[Stacks, Tag 0B6K], [Stacks, Tag 0B6B] and [Stacks, Tag 0B6J].

## Main results

* `CategoryTheory.NatTrans.IsMonoidal.δ_comp_tensorHom` — a monoidal transformation between
  strong monoidal functors is compatible with the oplax structures.
* `Stacks.CategoryTheory.BaseChange.squareComposite_δ_compat` — the compatibility hypothesis of
  this file, from the compatibility of the two identifications `eg`, `ef` with one functor.
* `Stacks.CategoryTheory.BaseChange.projectionMap_baseChange` — the projection maps of `Lf ⊣ Rf`
  and `Lf' ⊣ Rf'` agree via `β`.
* `CategoryTheory.Adjunction.map_comparisonMap_comp_counit` — the defining equation of the
  comparison map, transposed.
* `CategoryTheory.Adjunction.comparisonMap_naturality_right` — naturality in the second variable.
* `Stacks.CategoryTheory.BaseChange.isIso_map_comparisonMap_iff` — for strong monoidal pullbacks,
  where `α` is invertible at `L` and at `K ⊗ L`, any functor inverts `Lg'` of the comparison map
  of `f` at `(K, L)` exactly when it inverts the comparison map of `f'` at `(Lg K, Lg L)`.
* `Stacks.CategoryTheory.BaseChange.comparisonMap_baseChange` — the comparison maps of
  `(Lf ⊣ Rf, Rf ⊣ a)` and `(Lf' ⊣ Rf', Rf' ⊣ a')` agree via `α` and `β`.
* `Stacks.CategoryTheory.BaseChange.comparisonMap_unit_baseChange` — the same at the unit, for
  the one-variable comparison map `Lf K ⊗ a 𝟙 ⟶ a K`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal]
  [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] {a : C ⥤ D} (adj₂ : G ⊣ a)

/-- **The defining equation of the comparison map, transposed**: `G` of the comparison map
followed by the counit of `G ⊣ a` is the inverse projection map followed by `K` tensored with
that counit. -/
@[reassoc]
lemma map_comparisonMap_comp_counit (K L : C) :
    G.map (adj.comparisonMap adj₂ K L) ≫ adj₂.counit.app (K ⊗ L) =
      inv (adj.projectionMap K (a.obj L)) ≫ K ◁ adj₂.counit.app L := by
  have h := (adj₂.homEquiv _ _).symm_apply_apply
    (inv (adj.projectionMap K (a.obj L)) ≫ K ◁ adj₂.counit.app L)
  rwa [Adjunction.homEquiv_counit] at h

/-- **The comparison map is natural in the second variable.** -/
@[reassoc]
lemma comparisonMap_naturality_right (K : C) {L L' : C} (g : L ⟶ L') :
    F.obj K ◁ a.map g ≫ adj.comparisonMap adj₂ K L' =
      adj.comparisonMap adj₂ K L ≫ a.map (K ◁ g) := by
  have h := (adj.comparisonTwoSquare adj₂ K).naturality g
  simp only [Functor.comp_map, comparisonTwoSquare_natTrans_app] at h
  exact h

/-- **Invertibility of the comparison map only depends on the second variable up to
isomorphism**, after any functor. -/
lemma isIso_map_comparisonMap_iff_of_iso_right {E : Type*} [Category E] (H : D ⥤ E) (K : C)
    {L L' : C} (e : L ≅ L') :
    IsIso (H.map (adj.comparisonMap adj₂ K L)) ↔ IsIso (H.map (adj.comparisonMap adj₂ K L')) := by
  have h := congrArg H.map (adj.comparisonMap_naturality_right adj₂ K e.hom)
  simp only [Functor.map_comp] at h
  rw [← isIso_comp_right_iff (H.map (adj.comparisonMap adj₂ K L)) (H.map (a.map (K ◁ e.hom))),
    ← h, isIso_comp_left_iff]

end CategoryTheory.Adjunction

namespace CategoryTheory.NatTrans.IsMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]

/-- **A monoidal transformation between strong monoidal functors is compatible with the oplax
structures.** -/
@[reassoc]
lemma δ_comp_tensorHom (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C) :
    δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) = τ.app (X ⊗ Y) ≫ δ G X Y := by
  rw [← cancel_mono (Functor.LaxMonoidal.μ G X Y), Category.assoc, Category.assoc,
    Functor.Monoidal.δ_μ, Category.comp_id, ← IsMonoidal.tensor, Functor.Monoidal.δ_μ_assoc]

end CategoryTheory.NatTrans.IsMonoidal

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  [MonoidalCategory S] [MonoidalCategory T] [MonoidalCategory S'] [MonoidalCategory T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Rg : S' ⥤ S} {Lg' : T ⥤ T'} {Rg' : T' ⥤ T} {Lc : S ⥤ T'}
  [Lf.OplaxMonoidal] [Lf'.OplaxMonoidal] [Lg.OplaxMonoidal] [Lg'.OplaxMonoidal]
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (hsq : ∀ K N : S, Lf'.map (δ Lg K N) ≫ δ Lf' (Lg.obj K) (Lg.obj N) ≫
      ((squareCompositeIso eg ef).hom.app K ⊗ₘ (squareCompositeIso eg ef).hom.app N) =
    (squareCompositeIso eg ef).hom.app (K ⊗ N) ≫ Lg'.map (δ Lf K N) ≫
      δ Lg' (Lf.obj K) (Lf.obj N))

omit [Lf.OplaxMonoidal] [Lf'.OplaxMonoidal] [Lg.OplaxMonoidal] [Lg'.OplaxMonoidal] in
/-- **The compatibility of the identification of the two composites around the square with the
oplax structures**, from that of each of the two identifications `eg` and `ef` with one oplax
monoidal functor `Lc`. -/
theorem squareComposite_δ_compat [Lf.OplaxMonoidal] [Lf'.OplaxMonoidal] [Lg.OplaxMonoidal]
    [Lg'.OplaxMonoidal] [Lc.OplaxMonoidal]
    (hg : ∀ K N : S, δ (Lg ⋙ Lf') K N ≫ (eg.hom.app K ⊗ₘ eg.hom.app N) =
      eg.hom.app (K ⊗ N) ≫ δ Lc K N)
    (hf : ∀ K N : S, δ (Lf ⋙ Lg') K N ≫ (ef.hom.app K ⊗ₘ ef.hom.app N) =
      ef.hom.app (K ⊗ N) ≫ δ Lc K N) (K N : S) :
    Lf'.map (δ Lg K N) ≫ δ Lf' (Lg.obj K) (Lg.obj N) ≫
        ((squareCompositeIso eg ef).hom.app K ⊗ₘ (squareCompositeIso eg ef).hom.app N) =
      (squareCompositeIso eg ef).hom.app (K ⊗ N) ≫ Lg'.map (δ Lf K N) ≫
        δ Lg' (Lf.obj K) (Lf.obj N) := by
  have hg' := hg K N
  have hf' : δ Lc K N ≫ (ef.inv.app K ⊗ₘ ef.inv.app N) =
      ef.inv.app (K ⊗ N) ≫ δ (Lf ⋙ Lg') K N := by
    rw [← cancel_epi (ef.hom.app (K ⊗ N)), ← reassoc_of% (hf K N), Iso.hom_inv_id_app_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
    exact (congrArg _ (MonoidalCategory.id_tensorHom_id _ _)).trans (Category.comp_id _)
  simp only [Functor.OplaxMonoidal.comp_δ] at hg' hf'
  rw [squareCompositeIso_hom_app, squareCompositeIso_hom_app, squareCompositeIso_hom_app,
    ← MonoidalCategory.tensorHom_comp_tensorHom, reassoc_of% hg', hf', Category.assoc]

include hsq in
/-- **[Stacks, Tag 0B6B] over abstract monoidal adjunctions: the projection maps agree via the
base change map.** The oplax structure of `Lg` at `(K, Rf E)`, then `Lg K` tensored with the base
change map `β` at `E`, then the projection map of `Lf' ⊣ Rf'`, is `Lg` of the projection map of
`Lf ⊣ Rf`, then `β`, then `Rf'` of the oplax structure of `Lg'` and the identification of the two
composites around the square in the first factor. -/
theorem projectionMap_baseChange (K : S) (E : T) :
    δ Lg K (Rf.obj E) ≫ Lg.obj K ◁ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef E ≫
        adjf'.projectionMap (Lg.obj K) (Lg'.obj E) =
      Lg.map (adjf.projectionMap K E) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (Lf.obj K ⊗ E) ≫
          Rf'.map (δ Lg' (Lf.obj K) E ≫ (squareCompositeIso eg ef).inv.app K ▷ Lg'.obj E) := by
  set sq := squareCompositeIso eg ef
  set β := Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adjf'
  have l₁ : Lf'.map (Lg.obj K ◁ β E) ≫ δ Lf' (Lg.obj K) (Rf'.obj (Lg'.obj E)) =
      δ Lf' (Lg.obj K) (Lg.obj (Rf.obj E)) ≫ Lf'.obj (Lg.obj K) ◁ Lf'.map (β E) :=
    (δ_natural_right Lf' _ _).symm
  have l₂ : Lf'.obj (Lg.obj K) ◁ Lf'.map (β E) ≫
      Lf'.obj (Lg.obj K) ◁ adjf'.counit.app (Lg'.obj E) =
      Lf'.obj (Lg.obj K) ◁ (sq.hom.app (Rf.obj E) ≫ Lg'.map (adjf.counit.app E)) := by
    rw [← MonoidalCategory.whiskerLeft_comp, map_baseChangeMap_comp_counit adjf adjf' eg ef E]
  have r₁ : Lf'.map (Rf'.map (δ Lg' (Lf.obj K) E)) ≫
      Lf'.map (Rf'.map (sq.inv.app K ▷ Lg'.obj E)) ≫
        adjf'.counit.app (Lf'.obj (Lg.obj K) ⊗ Lg'.obj E) =
      adjf'.counit.app (Lg'.obj (Lf.obj K ⊗ E)) ≫
        δ Lg' (Lf.obj K) E ≫ sq.inv.app K ▷ Lg'.obj E := by
    have h := adjf'.counit.naturality (δ Lg' (Lf.obj K) E ≫ sq.inv.app K ▷ Lg'.obj E)
    simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Category.assoc] at h
    exact h
  have r₂ : Lf'.map (β (Lf.obj K ⊗ E)) ≫ adjf'.counit.app (Lg'.obj (Lf.obj K ⊗ E)) =
      sq.hom.app (Rf.obj (Lf.obj K ⊗ E)) ≫ Lg'.map (adjf.counit.app (Lf.obj K ⊗ E)) :=
    map_baseChangeMap_comp_counit adjf adjf' eg ef _
  have r₃ : Lf'.map (Lg.map (adjf.projectionMap K E)) ≫ sq.hom.app (Rf.obj (Lf.obj K ⊗ E)) =
      sq.hom.app (K ⊗ Rf.obj E) ≫ Lg'.map (Lf.map (adjf.projectionMap K E)) :=
    sq.hom.naturality (adjf.projectionMap K E)
  have r₃' : Lg'.map (Lf.map (adjf.projectionMap K E)) ≫
      Lg'.map (adjf.counit.app (Lf.obj K ⊗ E)) =
      Lg'.map (δ Lf K (Rf.obj E)) ≫ Lg'.map (Lf.obj K ◁ adjf.counit.app E) := by
    rw [← Lg'.map_comp, ← Lg'.map_comp, Adjunction.map_projectionMap_comp_counit]
  have r₄ : Lg'.map (Lf.obj K ◁ adjf.counit.app E) ≫ δ Lg' (Lf.obj K) E =
      δ Lg' (Lf.obj K) (Lf.obj (Rf.obj E)) ≫ Lg'.obj (Lf.obj K) ◁ Lg'.map (adjf.counit.app E) :=
    (δ_natural_right Lg' _ _).symm
  have r₅ : (sq.hom.app K ⊗ₘ sq.hom.app (Rf.obj E)) ≫
      Lg'.obj (Lf.obj K) ◁ Lg'.map (adjf.counit.app E) ≫ sq.inv.app K ▷ Lg'.obj E =
      Lf'.obj (Lg.obj K) ◁ (sq.hom.app (Rf.obj E) ≫ Lg'.map (adjf.counit.app E)) := by
    rw [MonoidalCategory.tensorHom_def, Category.assoc]
    simp only [Functor.comp_obj]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← whisker_exchange_assoc]
    simp only [Functor.id_obj]
    rw [← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id_app]
    exact (congrArg _ (MonoidalCategory.id_whiskerRight _ _)).trans (Category.comp_id _)
  have r₆ := hsq K (Rf.obj E)
  simp only [Functor.map_comp, Category.assoc]
  rw [Adjunction.map_projectionMap_comp_counit, reassoc_of% l₁, l₂, r₁, reassoc_of% r₂,
    reassoc_of% r₃, reassoc_of% r₃', reassoc_of% r₄, ← r₅, reassoc_of% r₆]

variable {a : S ⥤ T} {a' : S' ⥤ T'} (adja : Rf ⊣ a) (adja' : Rf' ⊣ a')
  [∀ (K : S) (M : T), IsIso (adjf.projectionMap K M)]
  [∀ (K : S') (M : T'), IsIso (adjf'.projectionMap K M)]
  [IsIso (twoSquare adjf adjf' eg ef)]

/-- `ξ` is invertible when `β` is. -/
instance : IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja') :=
  isIso_rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja'

include hsq in
/-- **[Stacks, Tag 0B6P] over abstract monoidal adjunctions, in two variables: the comparison maps
agree via the base change maps.** For `K, L` downstairs, `Lg'` of the comparison map of
`(Lf ⊣ Rf, Rf ⊣ a)` at `(K, L)`, followed by `α` at `K ⊗ L` and `a'` of the oplax structure of
`Lg`, is the oplax structure of `Lg'` at `(Lf K, a L)`, followed by the identification of the two
composites around the square at `K` tensored with `α` at `L`, and the comparison map of
`(Lf' ⊣ Rf', Rf' ⊣ a')` at `(Lg K, Lg L)`. -/
theorem comparisonMap_baseChange (K L : S) :
    Lg'.map (adjf.comparisonMap adja K L) ≫
        (rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app (K ⊗ L) ≫
          a'.map (δ Lg K L) =
      δ Lg' (Lf.obj K) (a.obj L) ≫
        ((squareCompositeIso eg ef).inv.app K ⊗ₘ
          (rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app L) ≫
        adjf'.comparisonMap adja' (Lg.obj K) (Lg.obj L) := by
  set sq := squareCompositeIso eg ef
  set α := rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja'
  set βt := twoSquare adjf adjf' eg ef
  have hβ : ∀ W : T, Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef W =
      βt.app W := fun _ => rfl
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adja'
  have l₁ : Rf'.map (a'.map (δ Lg K L)) ≫ adja'.counit.app (Lg.obj K ⊗ Lg.obj L) =
      adja'.counit.app (Lg.obj (K ⊗ L)) ≫ δ Lg K L :=
    adja'.counit.naturality _
  have l₂ : Rf'.map (α.app (K ⊗ L)) ≫ adja'.counit.app (Lg.obj (K ⊗ L)) =
      (inv βt).app (a.obj (K ⊗ L)) ≫ Lg.map (adja.counit.app (K ⊗ L)) :=
    map_rightAdjointBaseChange_comp_counit adjf adjf' adjg adjg' eg ef adja adja' (K ⊗ L)
  have l₃ : Rf'.map (Lg'.map (adjf.comparisonMap adja K L)) ≫
      (inv βt).app (a.obj (K ⊗ L)) =
      (inv βt).app (Lf.obj K ⊗ a.obj L) ≫
        Lg.map (Rf.map (adjf.comparisonMap adja K L)) :=
    (inv βt).naturality _
  have l₄ : Lg.map (Rf.map (adjf.comparisonMap adja K L)) ≫ Lg.map (adja.counit.app (K ⊗ L)) =
      Lg.map (inv (adjf.projectionMap K (a.obj L))) ≫ Lg.map (K ◁ adja.counit.app L) := by
    rw [← Lg.map_comp, ← Lg.map_comp, Adjunction.map_comparisonMap_comp_counit]
  have r₁ : Rf'.map (adjf'.comparisonMap adja' (Lg.obj K) (Lg.obj L)) ≫
      adja'.counit.app (Lg.obj K ⊗ Lg.obj L) =
      inv (adjf'.projectionMap (Lg.obj K) (a'.obj (Lg.obj L))) ≫
        Lg.obj K ◁ adja'.counit.app (Lg.obj L) :=
    Adjunction.map_comparisonMap_comp_counit adjf' adja' _ _
  have r₂ : adjf'.projectionMap (Lg.obj K) (Lg'.obj (a.obj L)) ≫
      Rf'.map (Lf'.obj (Lg.obj K) ◁ α.app L) ≫
        inv (adjf'.projectionMap (Lg.obj K) (a'.obj (Lg.obj L))) =
      Lg.obj K ◁ Rf'.map (α.app L) := by
    rw [← Adjunction.whiskerLeft_projectionMap_assoc]
    simp only [Functor.comp_obj, IsIso.hom_inv_id, Category.comp_id]
  have r₃ : Lg.obj K ◁ βt.app (a.obj L) ≫ Lg.obj K ◁ Rf'.map (α.app L) ≫
      Lg.obj K ◁ adja'.counit.app (Lg.obj L) = Lg.obj K ◁ Lg.map (adja.counit.app L) := by
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ← map_counit_eq_twoSquare_comp_map_rightAdjointBaseChange]
  have r₄ : δ Lg K (Rf.obj (a.obj L)) ≫ Lg.obj K ◁ Lg.map (adja.counit.app L) =
      Lg.map (K ◁ adja.counit.app L) ≫ δ Lg K L :=
    δ_natural_right Lg _ _
  have hpb := projectionMap_baseChange adjf adjf' eg ef hsq K (a.obj L)
  rw [hβ, hβ] at hpb
  have hsplit : (sq.inv.app K ⊗ₘ α.app L) =
      sq.inv.app K ▷ Lg'.obj (a.obj L) ≫ Lf'.obj (Lg.obj K) ◁ α.app L :=
    MonoidalCategory.tensorHom_def _ _
  have key : Rf'.map (δ Lg' (Lf.obj K) (a.obj L)) ≫ Rf'.map (sq.inv.app K ▷ Lg'.obj (a.obj L)) =
      (inv βt).app (Lf.obj K ⊗ a.obj L) ≫
        Lg.map (inv (adjf.projectionMap K (a.obj L))) ≫
          δ Lg K (Rf.obj (a.obj L)) ≫ Lg.obj K ◁ βt.app (a.obj L) ≫
            adjf'.projectionMap (Lg.obj K) (Lg'.obj (a.obj L)) := by
    rw [hpb, ← Lg.map_comp_assoc, IsIso.inv_hom_id, Lg.map_id, Category.id_comp,
      ← NatTrans.comp_app_assoc, IsIso.inv_hom_id, NatTrans.id_app, Category.id_comp,
      Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [l₁, reassoc_of% l₂, reassoc_of% l₃, hsplit]
  simp only [Functor.map_comp, Category.assoc]
  rw [r₁, reassoc_of% key, reassoc_of% r₂, r₃, r₄, reassoc_of% l₄]

include hsq in
/-- **[Stacks, Tag 0B6P] over abstract monoidal adjunctions, in one variable.** For `U = 𝟙_ S`
and `U' = 𝟙_ S'` (up to equality), `Lg'` of the comparison map `Lf K ⊗ a U ⟶ a K` (the
comparison map at `(K, U)` followed by `a` of the right unitor), followed by `α` at `K`, is the
oplax structure of `Lg'` at `(Lf K, a U)`, followed by the identification of the two composites
around the square at `K` tensored with `α` at `U` and `a'` of the oplax unit of `Lg`, and the
comparison map `Lf' (Lg K) ⊗ a' U' ⟶ a' (Lg K)`. -/
theorem comparisonMap_unit_baseChange {U : S} {U' : S'} (hU : 𝟙_ S = U) (hU' : 𝟙_ S' = U')
    (K : S) :
    Lg'.map (adjf.comparisonMap adja K U ≫ a.map (K ◁ eqToHom hU.symm ≫ (ρ_ K).hom)) ≫
        (rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K =
      δ Lg' (Lf.obj K) (a.obj U) ≫
        ((squareCompositeIso eg ef).inv.app K ⊗ₘ
          ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app U ≫
            a'.map (Lg.map (eqToHom hU.symm) ≫ η Lg ≫ eqToHom hU'))) ≫
        adjf'.comparisonMap adja' (Lg.obj K) U' ≫
          a'.map (Lg.obj K ◁ eqToHom hU'.symm ≫ (ρ_ (Lg.obj K)).hom) := by
  subst hU hU'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, MonoidalCategory.whiskerLeft_id]
  set α := rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja'
  have n : Lg'.map (a.map (ρ_ K).hom) ≫ α.app K =
      α.app (K ⊗ 𝟙_ S) ≫ a'.map (Lg.map (ρ_ K).hom) :=
    α.naturality _
  have hb := comparisonMap_baseChange adjf adjf' adjg adjg' eg ef hsq adja adja' K (𝟙_ S)
  have hn := Adjunction.comparisonMap_naturality_right adjf' adja' (Lg.obj K) (η Lg)
  have ht : ((squareCompositeIso eg ef).inv.app K ⊗ₘ α.app (𝟙_ S)) ≫
      Lf'.obj (Lg.obj K) ◁ a'.map (η Lg) =
      ((squareCompositeIso eg ef).inv.app K ⊗ₘ (α.app (𝟙_ S) ≫ a'.map (η Lg))) := by
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rfl
  rw [Functor.map_comp, Category.assoc, n, ← right_unitality_hom Lg K]
  simp only [Functor.map_comp]
  rw [reassoc_of% hb, ← reassoc_of% hn, reassoc_of% ht]
  simp

include hsq in
/-- **Invertibility of the comparison map is compatible with base change** where `α` is invertible:
if the oplax structures of `Lg` and `Lg'` are invertible and `α` is invertible at `L` and at
`K ⊗ L`, then a functor `H` inverts `Lg'` of the comparison map of `f` at `(K, L)` exactly when it
inverts the comparison map of `f'` at `(Lg K, Lg L)`. -/
theorem isIso_map_comparisonMap_iff [∀ K N : S, IsIso (δ Lg K N)]
    [∀ M N : T, IsIso (δ Lg' M N)] {E : Type*} [Category E]
    (H : T' ⥤ E) (K L : S)
    [IsIso ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app L)]
    [IsIso ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app
      (K ⊗ L))] :
    IsIso (H.map (Lg'.map (adjf.comparisonMap adja K L))) ↔
      IsIso (H.map (adjf'.comparisonMap adja' (Lg.obj K) (Lg.obj L))) := by
  set α := rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja'
  have h := congrArg H.map (comparisonMap_baseChange adjf adjf' adjg adjg' eg ef hsq adja adja' K L)
  simp only [Functor.map_comp] at h
  rw [← isIso_comp_right_iff (H.map (Lg'.map (adjf.comparisonMap adja K L)))
      (H.map (α.app (K ⊗ L)) ≫ H.map (a'.map (δ Lg K L))), h,
    isIso_comp_left_iff, isIso_comp_left_iff]

end Stacks.CategoryTheory.BaseChange

end
