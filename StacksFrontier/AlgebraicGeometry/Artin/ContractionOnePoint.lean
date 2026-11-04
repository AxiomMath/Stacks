module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine

/-!
# Artin's contraction functor on a scheme with one point

In the situation of Stacks 0GH8, let `F` be the functor of Stacks 0GHA, recorded as
`AlgebraicGeometry.Artin.contractionFunctor`. The proofs of Stacks 0GI6, 0GI7 and 0GI8 start from
the observation that for a scheme `V` with a single point, for instance the spectrum of an
Artinian local ring, an element `(Z, u', x̂)` of `F(V)` has either `Z = ∅` or `Z = V`. In the first
case `x̂` is a morphism out of the empty formal algebraic space and the element is determined by
`u' : V ⟶ U'`; in the second case `u'` is a morphism out of the empty scheme and the element is
determined by `x̂ : V ⟶ W`. So `F(V) = U'(V) ⨿ W(V)`, compatibly with restriction along morphisms
of such schemes. This file proves the injectivity statements behind that decomposition, which is
the form in which the three proofs use it.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.Triple.uValue`: for a triple with `Z = ∅`, the
  element of `X'(V)` given by `u'`.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.xhatValue`: for a triple with `Z` all of
  `|V|`, the element of `W(V)` given by `x̂`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.Triple.Z_eq_empty_or_eq_univ`: on a scheme with one
  point, `Z = ∅` or `Z = |V|`.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.ext_of_Z_eq_empty` and
  `AlgebraicGeometry.Artin.ContractionSituation.Triple.ext_of_Z_eq_univ`: a triple with `Z = ∅` is
  determined by `u'`, and a triple with `Z = |V|` by `x̂`.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.uValue_mapTriple` and
  `AlgebraicGeometry.Artin.ContractionSituation.Triple.xhatValue_mapTriple`: both are compatible
  with restriction.

## References

* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GI6](https://stacks.math.columbia.edu/tag/0GI6)
* [Stacks Project, Tag 0GI7](https://stacks.math.columbia.edu/tag/0GI7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

namespace BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A sheaf on the big fppf site of `S` has at most one section over an object whose underlying
scheme is empty: the empty family covers it. -/
theorem subsingleton_obj_of_isEmpty {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P) {U : BigFppfOver B S hS}
    (hU : IsEmpty ((BigFppfOver.toScheme B S hS).obj U)) : Subsingleton (P.obj (op U)) := by
  let Z : PEmpty.{1} → BigFppfOver B S hS := fun j => j.elim
  let f : ∀ j, Z j ⟶ U := fun j => j.elim
  have hbot : Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj (Z j))
      (fun j => (BigFppfOver.toScheme B S hS).map (f j)) = ⊥ :=
    le_antisymm (Presieve.ofArrows_le_iff.2 fun j => j.elim) bot_le
  have hmem : Sieve.generate (Presieve.ofArrows Z f) ∈ BigFppfOver.topology B S hS U := by
    refine sieve_generate_ofArrows_mem_topology Z f ?_
    rw [hbot]
    exact Scheme.bot_mem_precoverage _ _
  refine ⟨fun x y => (((isSheaf_iff_isSheaf_of_type _ _).mp hP) _ hmem).isSeparatedFor.ext
    fun V g hg => ?_⟩
  obtain ⟨_, _, _, ⟨j⟩, _⟩ := hg
  exact j.elim

end BigFppfOver

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An object of the big fppf site over `S` whose represented presheaf has no points has an empty
underlying scheme. -/
theorem isEmpty_toScheme_of_isEmpty_points {U : BigFppfOver B S hS}
    (h : IsEmpty (points B S hS (yoneda.obj U))) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj U) :=
  ⟨fun y => h.false ((pointsEquivScheme B S hS U).symm y)⟩

/-- A section with point-set image in the empty set lives over an object with empty underlying
scheme. -/
theorem isEmpty_toScheme_of_hasImageIn_empty {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {f : X.obj (op U)} (hf : HasImageIn B S hS X ∅ U f) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj U) := by
  refine isEmpty_toScheme_of_isEmpty_points ⟨fun q => ?_⟩
  induction q using Quot.ind with
  | _ p => exact hf p

end Space

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}

/-- On an object of the site with a single point, the closed subset of a triple is empty or
everything. -/
theorem Triple.Z_eq_empty_or_eq_univ [Subsingleton ((BigFppfOver.toScheme B S hS).obj V)]
    (t : Triple c V) : t.Z = ∅ ∨ t.Z = Set.univ := by
  have : Subsingleton (Space.points B S hS (yoneda.obj V)) :=
    (Space.pointsEquivScheme B S hS V).injective.subsingleton
  rcases t.Z.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · exact Or.inr (Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx)

/-- The identity of `V` is a section of `V ∖ Z` when `Z` is empty. -/
private theorem id_mem_openSubspace_of_eq_empty {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hZ : Z = ∅) : 𝟙 V ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).obj (op V) := by
  rw [hZ, Set.compl_empty]
  exact Set.subset_univ _

/-- The identity of `V` is a section of `V ∖ Z` when `Z` is empty. -/
theorem Triple.id_mem_openSubspace (t : Triple c V) (h : t.Z = ∅) :
    𝟙 V ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op V) :=
  id_mem_openSubspace_of_eq_empty h

/-- The element of `X'(V)` given by the second component `u' : V ∖ Z ⟶ U'` of a triple with
`Z = ∅`. -/
def Triple.uValue (t : Triple c V) (h : t.Z = ∅) : c.X'.obj (op V) :=
  (t.u.app (op V) ⟨𝟙 V, t.id_mem_openSubspace h⟩).1

/-- The identity of `V` has point-set image in `Z` when `Z` is everything. -/
private theorem hasImageIn_id_of_eq_univ {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hZ : Z = Set.univ) : Space.HasImageIn B S hS (yoneda.obj V) Z V (𝟙 V) :=
  fun _ => hZ ▸ Set.mem_univ _

/-- The identity of `V` has point-set image in `Z` when `Z` is everything. -/
theorem Triple.hasImageIn_id (t : Triple c V) (h : t.Z = Set.univ) :
    Space.HasImageIn B S hS (yoneda.obj V) t.Z V (𝟙 V) := hasImageIn_id_of_eq_univ h

/-- The tautological section of the completion `V_{/Z}` when `Z` is everything. -/
noncomputable def Triple.tautological (t : Triple c V) (h : t.Z = Set.univ) :
    (Space.completionSheaf B S hS (yoneda.obj V) t.Z).obj.obj (op V) :=
  ((BigFppfOver.topology B S hS).toSheafify
    (Space.completionSubfunctor B S hS (yoneda.obj V) t.Z).toFunctor).app (op V)
      ⟨ULift.up (𝟙 V), t.hasImageIn_id h⟩

/-- The element of `W(V)` given by the third component `x̂ : V_{/Z} ⟶ W` of a triple whose
closed subset `Z` is everything. -/
noncomputable def Triple.xhatValue (t : Triple c V) (h : t.Z = Set.univ) : c.W.obj.obj (op V) :=
  t.xhat.hom.app (op V) (t.tautological h)

/-- A morphism out of `V ∖ ∅` is determined by its value at the identity of `V`. -/
theorem ext_openSubspace_compl_empty {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hZ : Z = ∅) {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α β : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ P)
    (hid : ∀ h, α.app (op V) ⟨𝟙 V, h⟩ = β.app (op V) ⟨𝟙 V, h⟩) : α = β := by
  have hmem := id_mem_openSubspace_of_eq_empty (V := V) hZ
  let G := (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor
  let e₀ : G.obj (op V) := ⟨𝟙 V, hmem⟩
  ext T ⟨g, hg⟩
  have e : (⟨g, hg⟩ : G.obj T) = G.map g.op e₀ := by
    apply Subtype.ext
    show g = g ≫ 𝟙 V
    rw [Category.comp_id]
  show α.app T ⟨g, hg⟩ = β.app T ⟨g, hg⟩
  rw [e, NatTrans.naturality_apply, NatTrans.naturality_apply]
  exact congrArg _ (hid hmem)

/-- A morphism of sheaves out of the completion `V_{/|V|}` is determined by its value on the
tautological section. -/
theorem ext_completionSheaf_univ {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hZ : Z = Set.univ) {P : FormalSpace.FppfSheaf B S hS}
    (α β : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ P)
    (hid : ∀ h, α.hom.app (op V) (((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor).app (op V)
          ⟨ULift.up (𝟙 V), h⟩) = β.hom.app (op V) (((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor).app (op V)
          ⟨ULift.up (𝟙 V), h⟩)) : α = β := by
  have hmem := hasImageIn_id_of_eq_univ (V := V) hZ
  let G := (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor
  let e₀ : G.obj (op V) := ⟨ULift.up (𝟙 V), hmem⟩
  let ι := (BigFppfOver.topology B S hS).toSheafify G
  refine Sheaf.hom_ext (GrothendieckTopology.sheafify_hom_ext _ _ _ P.cond ?_)
  show ι ≫ α.hom = ι ≫ β.hom
  ext T ⟨⟨g⟩, hg⟩
  have e : (⟨⟨g⟩, hg⟩ : G.obj T) = G.map g.op e₀ := by
    apply Subtype.ext
    apply ULift.ext
    show g = g ≫ 𝟙 V
    rw [Category.comp_id]
  show (ι ≫ α.hom).app T ⟨⟨g⟩, hg⟩ = (ι ≫ β.hom).app T ⟨⟨g⟩, hg⟩
  rw [e, NatTrans.naturality_apply, NatTrans.naturality_apply]
  exact congrArg _ (hid hmem)

/-- There is only one morphism out of the completion `V_{/∅}`: its sections live over empty
schemes, where `W` has a single section. -/
theorem subsingleton_completionSheaf_empty {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hZ : Z = ∅) (P : FormalSpace.FppfSheaf B S hS) :
    Subsingleton (Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ P) := by
  refine ⟨fun α β => Sheaf.hom_ext (GrothendieckTopology.sheafify_hom_ext _ _ _ P.cond ?_)⟩
  ext T x
  have hT := Space.isEmpty_toScheme_of_hasImageIn_empty (X := yoneda.obj V) (U := T.unop)
    (f := x.1.down) (hZ ▸ x.2)
  exact (BigFppfOver.subsingleton_obj_of_isEmpty P.cond hT).elim _ _

/-- There is only one morphism from `V ∖ |V|` to `U'`: its sections live over empty schemes, where
the algebraic space `X'` has a single section. -/
theorem subsingleton_openSubspace_compl_univ {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hZ : Z = Set.univ) :
    Subsingleton ((Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶
      c.U'.toFunctor) := by
  refine ⟨fun α β => ?_⟩
  ext T ⟨g, hg⟩
  show α.app T ⟨g, hg⟩ = β.app T ⟨g, hg⟩
  have hT : IsEmpty ((BigFppfOver.toScheme B S hS).obj T.unop) := by
    refine Space.isEmpty_toScheme_of_isEmpty_points ⟨fun q => ?_⟩
    have := hg ⟨q, rfl⟩
    rwa [hZ, Set.compl_univ] at this
  have := BigFppfOver.subsingleton_obj_of_isEmpty c.isAlgebraicSpace_X'.isSheaf hT
  exact Subtype.ext (Subsingleton.elim _ _)

/-- **A triple with `Z = ∅` is determined by `u'`.** -/
theorem Triple.ext_of_Z_eq_empty {t t' : Triple c V} (h : t.Z = ∅) (h' : t'.Z = ∅)
    (hu : t.uValue h = t'.uValue h') : t = t' := by
  obtain ⟨Z, hZ, u, x, a, w⟩ := t
  obtain ⟨Z', hZ', u', x', a', w'⟩ := t'
  obtain rfl : Z = ∅ := h
  obtain rfl : Z' = ∅ := h'
  refine Triple.mk_congr rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · exact ext_openSubspace_compl_empty rfl u u' fun _ => Subtype.ext hu
  · exact (subsingleton_completionSheaf_empty (V := V) (Z := ∅) rfl c.W).elim _ _

/-- **A triple with `Z = |V|` is determined by `x̂`.** -/
theorem Triple.ext_of_Z_eq_univ {t t' : Triple c V} (h : t.Z = Set.univ) (h' : t'.Z = Set.univ)
    (hx : t.xhatValue h = t'.xhatValue h') : t = t' := by
  obtain ⟨Z, hZ, u, x, a, w⟩ := t
  obtain ⟨Z', hZ', u', x', a', w'⟩ := t'
  obtain rfl : Z = Set.univ := h
  obtain rfl : Z' = Set.univ := h'
  refine Triple.mk_congr rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · exact (subsingleton_openSubspace_compl_univ (c := c) (V := V) (Z := Set.univ) rfl).elim _ _
  · exact ext_completionSheaf_univ rfl x x' fun _ => hx

variable (c) in
/-- Restriction preserves the empty closed subset. -/
theorem Triple.mapTriple_Z_eq_empty {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (h : t.Z = ∅) : (mapTriple c φ t).Z = ∅ := by
  show Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z = ∅
  rw [h, Set.preimage_empty]

variable (c) in
/-- Restriction preserves the full closed subset. -/
theorem Triple.mapTriple_Z_eq_univ {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (h : t.Z = Set.univ) : (mapTriple c φ t).Z = Set.univ := by
  show Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z = Set.univ
  rw [h, Set.preimage_univ]

/-- `u'` is compatible with restriction. -/
theorem Triple.uValue_mapTriple {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (h : t.Z = ∅) (h' : (mapTriple c φ t).Z = ∅) :
    (mapTriple c φ t).uValue h' = c.X'.map φ.op (t.uValue h) := by
  let G := (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁) t.Zᶜ).toFunctor
  let e₀ : G.obj (op V₁) := ⟨𝟙 V₁, t.id_mem_openSubspace h⟩
  have e : (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) _ t.Zᶜ
      (fun _ hz => hz)).app (op V₂) ⟨𝟙 V₂, (mapTriple c φ t).id_mem_openSubspace h'⟩ =
      G.map φ.op e₀ := by
    apply Subtype.ext
    show 𝟙 V₂ ≫ φ = φ ≫ 𝟙 V₁
    rw [Category.id_comp, Category.comp_id]
  show (t.u.app (op V₂) ((Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) _ t.Zᶜ
      (fun _ hz => hz)).app (op V₂) ⟨𝟙 V₂, _⟩)).1 = _
  rw [e, NatTrans.naturality_apply]
  rfl

/-- `x̂` is compatible with restriction. -/
theorem Triple.xhatValue_mapTriple {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (h : t.Z = Set.univ) (h' : (mapTriple c φ t).Z = Set.univ) :
    (mapTriple c φ t).xhatValue h' = c.W.obj.map φ.op (t.xhatValue h) := by
  let G₁ := (Space.completionSubfunctor B S hS (yoneda.obj V₁) t.Z).toFunctor
  let G₂ := (Space.completionSubfunctor B S hS (yoneda.obj V₂) (mapTriple c φ t).Z).toFunctor
  let e₁ : G₁.obj (op V₁) := ⟨ULift.up (𝟙 V₁), t.hasImageIn_id h⟩
  let e₂ : G₂.obj (op V₂) := ⟨ULift.up (𝟙 V₂), (mapTriple c φ t).hasImageIn_id h'⟩
  let ρ : G₂ ⟶ G₁ := Space.completionSubfunctorRestrict B S hS (yoneda.map φ) _ t.Z
    (fun _ hz => hz)
  have e : ρ.app (op V₂) e₂ = G₁.map φ.op e₁ := by
    apply Subtype.ext
    apply ULift.ext
    show 𝟙 V₂ ≫ φ = φ ≫ 𝟙 V₁
    rw [Category.id_comp, Category.comp_id]
  let ι₁ : G₁ ⟶ (Space.completionSheaf B S hS (yoneda.obj V₁) t.Z).obj :=
    (BigFppfOver.topology B S hS).toSheafify G₁
  let ι₂ : G₂ ⟶ (Space.completionSheaf B S hS (yoneda.obj V₂) (mapTriple c φ t).Z).obj :=
    (BigFppfOver.topology B S hS).toSheafify G₂
  let r : Space.completionSheaf B S hS (yoneda.obj V₂) (mapTriple c φ t).Z ⟶
      Space.completionSheaf B S hS (yoneda.obj V₁) t.Z :=
    Space.completionSheafRestrict B S hS (yoneda.map φ) _ t.Z (fun _ hz => hz)
  have hr : ι₂ ≫ r.hom = ρ ≫ ι₁ := (GrothendieckTopology.toSheafify_naturality _ ρ).symm
  let γ : G₁ ⟶ c.W.obj := ι₁ ≫ t.xhat.hom
  have h1 : ι₂ ≫ (r ≫ t.xhat).hom = ρ ≫ γ := by
    show ι₂ ≫ r.hom ≫ t.xhat.hom = _
    rw [← Category.assoc, hr, Category.assoc]
  refine (congrArg (fun η : G₂ ⟶ c.W.obj => η.app (op V₂) e₂) h1).trans ?_
  show γ.app (op V₂) (ρ.app (op V₂) e₂) = c.W.obj.map φ.op (γ.app (op V₁) e₁)
  rw [e, NatTrans.naturality_apply]

end Artin.ContractionSituation

end AlgebraicGeometry

end
