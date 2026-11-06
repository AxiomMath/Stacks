module

public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusInRelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubschemeDescent

/-!
# Base change of the functor of relative isomorphisms

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over `S`, and let `q : Q' ⟶ Q`
be a morphism of algebraic spaces. Let `Z' ⟶ Q'` and `X' ⟶ Q'` be base changes of `z` and `x`
along `q`, that is, the two squares

```text
Z' ⟶ Z        X' ⟶ X
|     |        |     |
v     v        v     v
Q' ⟶ Q        Q' ⟶ Q
```

are cartesian. Then

```text
Isom_{Q'}(Z', X') = Q' ×_Q Isom_Q(Z, X),
```

that is, the projection `Isom_{Q'}(Z', X') ⟶ Q'` is a base change of the projection
`Isom_Q(Z, X) ⟶ Q` along `q`. This is Stacks 05Y4 for the subfunctor of isomorphisms of
Stacks 0DPP: a pair of Stacks 05Y1 over the base change is a relative isomorphism exactly when
the pair it induces over `Q` is one, since the two morphisms of base changes agree up to the
canonical identifications `T ×_{Q'} Z' = T ×_Q Z` and `T ×_{Q'} X' = T ×_Q X`.

The base changes `Z'` and `X'` are given by arbitrary cartesian squares, not by the chosen fibre
products.

## Main results

* `AlgebraicGeometry.Space.RelativeMorphism.isRelativeIso_ofBaseChange_iff`: a pair over the
  chosen base changes is a relative isomorphism iff the pair it induces over `Q` is.
* `AlgebraicGeometry.Space.RelativeMorphism.transport`: the pair obtained by transporting a pair
  along isomorphisms of the source and target over the base; it is compatible with restriction
  and preserves relative isomorphisms.
* `AlgebraicGeometry.Space.exists_isPullback_isomSubfunctor_of_isPullback`: the projection of
  `Isom_{Q'}(Z', X')` is a base change of the projection of `Isom_Q(Z, X)`.

## References

* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_isomorphismLocusBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_isomorphismLocusBaseChange
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : P ⟶ R) (b : Q ⟶ R) :
    HasLimit (cospan a b) :=
  (hasPullbacks_presheaf_isomorphismLocusBaseChange (B := B) (S := S) (hS := hS)).has_limit _

/-! ### Relative isomorphisms over the chosen base changes -/

section ChosenBaseChange

variable {Z X Q Q' T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-- **The morphism of base changes of the pair underlying a pair over the base changes.** It is
the morphism of base changes of the given pair, read through the identifications
`T ×_{Q'} (Q' ×_Q Z) = T ×_Q Z` and `T ×_{Q'} (Q' ×_Q X) = T ×_Q X`. -/
theorem RelativeMorphism.baseChangeMap_ofBaseChange (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T) :
    (RelativeMorphism.ofBaseChange q p).baseChangeMap =
      (pullbackBaseChangeIso q z p.base).inv ≫ p.baseChangeMap ≫
        (pullbackBaseChangeIso q x p.base).hom := by
  refine pullback.hom_ext ?_ ?_
  · refine (RelativeMorphism.baseChangeMap_comp_fst (RelativeMorphism.ofBaseChange q p)).trans ?_
    show pullback.fst (p.base ≫ q) z = ((pullbackBaseChangeIso q z p.base).inv ≫
      p.baseChangeMap ≫ (pullbackBaseChangeIso q x p.base).hom) ≫ pullback.fst (p.base ≫ q) x
    rw [Category.assoc, Category.assoc, pullbackBaseChangeIso_hom_fst,
      RelativeMorphism.baseChangeMap_comp_fst, pullbackBaseChangeIso_inv_fst]
  · refine (RelativeMorphism.baseChangeMap_comp_snd (RelativeMorphism.ofBaseChange q p)).trans ?_
    show (pullbackBaseChangeIso q z p.base).inv ≫ p.morphism ≫ pullback.snd q x =
      ((pullbackBaseChangeIso q z p.base).inv ≫ p.baseChangeMap ≫
        (pullbackBaseChangeIso q x p.base).hom) ≫ pullback.snd (p.base ≫ q) x
    rw [Category.assoc, Category.assoc, pullbackBaseChangeIso_hom_snd,
      RelativeMorphism.baseChangeMap_comp_snd_assoc]

/-- **A pair over the base changes is a relative isomorphism iff the pair it induces over `Q`
is.** The two morphisms of base changes differ by the canonical identifications of fibre
products (`AlgebraicGeometry.Space.RelativeMorphism.baseChangeMap_ofBaseChange`). -/
theorem RelativeMorphism.isRelativeIso_ofBaseChange_iff (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T) :
    (RelativeMorphism.ofBaseChange q p).IsRelativeIso ↔ p.IsRelativeIso := by
  have key : IsIso ((pullbackBaseChangeIso q z p.base).inv ≫ p.baseChangeMap ≫
      (pullbackBaseChangeIso q x p.base).hom) ↔ IsIso p.baseChangeMap := by
    rw [isIso_comp_left_iff, isIso_comp_right_iff]
  exact (iff_of_eq (congrArg IsIso (RelativeMorphism.baseChangeMap_ofBaseChange q p))).trans key

end ChosenBaseChange

/-! ### Transport of pairs along isomorphisms of the source and target -/

section Transport

variable {Z₁ Z₂ X₁ X₂ Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z₁ : Z₁ ⟶ Q} {z₂ : Z₂ ⟶ Q}
  {x₁ : X₁ ⟶ Q} {x₂ : X₂ ⟶ Q}

/-- The comparison `T ×_{a, Q} Z₂ ⟶ T ×_{a, Q} Z₁` along an isomorphism `e : Z₁ ≅ Z₂` over `Q`. -/
noncomputable abbrev transportSourceMap (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁) (a : T ⟶ Q) :
    pullback a z₂ ⟶ pullback a z₁ :=
  pullback.map a z₂ a z₁ (𝟙 T) e.inv (𝟙 Q) (by simp)
    (by rw [Category.comp_id, ← he, Iso.inv_hom_id_assoc])

/-- **Transport of a pair of Stacks 05Y1 along isomorphisms `Z₁ ≅ Z₂` and `X₁ ≅ X₂` over `Q`.**
The first component is unchanged; the second is read through `T ×_Q Z₂ ≅ T ×_Q Z₁` and followed
by `X₁ ≅ X₂`. -/
noncomputable def RelativeMorphism.transport (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁)
    (ε : X₁ ≅ X₂) (hε : ε.hom ≫ x₂ = x₁) (p : RelativeMorphism B S hS Z₁ X₁ Q z₁ x₁ T) :
    RelativeMorphism B S hS Z₂ X₂ Q z₂ x₂ T where
  base := p.base
  morphism := transportSourceMap e he p.base ≫ p.morphism ≫ ε.hom
  commutes := by
    rw [Category.assoc, Category.assoc, hε, p.commutes, pullback.lift_snd_assoc, Category.assoc,
      show e.inv ≫ z₁ = z₂ by rw [← he, Iso.inv_hom_id_assoc]]

/-- Transport leaves the first component of a pair unchanged. -/
@[simp] theorem RelativeMorphism.transport_base (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁)
    (ε : X₁ ≅ X₂) (hε : ε.hom ≫ x₂ = x₁) (p : RelativeMorphism B S hS Z₁ X₁ Q z₁ x₁ T) :
    (RelativeMorphism.transport e he ε hε p).base = p.base := rfl

/-- Transport along two pairs of mutually inverse isomorphisms returns the pair. -/
theorem RelativeMorphism.transport_transport (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁)
    (ε : X₁ ≅ X₂) (hε : ε.hom ≫ x₂ = x₁) (p : RelativeMorphism B S hS Z₁ X₁ Q z₁ x₁ T) :
    RelativeMorphism.transport e.symm (by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc])
        ε.symm (by rw [Iso.symm_hom, ← hε, Iso.inv_hom_id_assoc])
        (RelativeMorphism.transport e he ε hε p) = p := by
  obtain ⟨a, b, hb⟩ := p
  show RelativeMorphism.mk _ _ _ = RelativeMorphism.mk _ _ _
  congr 1
  show transportSourceMap e.symm _ a ≫ (transportSourceMap e he a ≫ b ≫
    ε.hom) ≫ ε.inv = b
  have hcomp : transportSourceMap e.symm
      (by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]) a ≫
        transportSourceMap e he a = 𝟙 _ :=
    pullback.hom_ext (by simp) (by simp)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% hcomp]

/-- Transport commutes with restriction of pairs. -/
theorem RelativeMorphism.transport_restrict (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁)
    (ε : X₁ ≅ X₂) (hε : ε.hom ≫ x₂ = x₁) (t : T' ⟶ T)
    (p : RelativeMorphism B S hS Z₁ X₁ Q z₁ x₁ T) :
    RelativeMorphism.transport e he ε hε (RelativeMorphism.restrict t p) =
      RelativeMorphism.restrict t (RelativeMorphism.transport e he ε hε p) := by
  show RelativeMorphism.mk _ _ _ = RelativeMorphism.mk _ _ _
  congr 1
  show transportSourceMap e he (t ≫ p.base) ≫
      (pullback.map (t ≫ p.base) z₁ p.base z₁ t (𝟙 Z₁) (𝟙 Q) (by simp) (by simp) ≫
        p.morphism) ≫ ε.hom =
    pullback.map (t ≫ p.base) z₂ p.base z₂ t (𝟙 Z₂) (𝟙 Q) (by simp) (by simp) ≫
      transportSourceMap e he p.base ≫ p.morphism ≫ ε.hom
  have hsq : transportSourceMap e he (t ≫ p.base) ≫
      pullback.map (t ≫ p.base) z₁ p.base z₁ t (𝟙 Z₁) (𝟙 Q) (by simp) (by simp) =
      pullback.map (t ≫ p.base) z₂ p.base z₂ t (𝟙 Z₂) (𝟙 Q) (by simp) (by simp) ≫
        transportSourceMap e he p.base :=
    pullback.hom_ext (by simp) (by simp)
  simp only [Category.assoc]
  rw [reassoc_of% hsq]

/-- The morphism of base changes of a transported pair is that of the pair, conjugated by the
comparisons of base changes along the two isomorphisms. -/
theorem RelativeMorphism.baseChangeMap_transport (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁)
    (ε : X₁ ≅ X₂) (hε : ε.hom ≫ x₂ = x₁) (p : RelativeMorphism B S hS Z₁ X₁ Q z₁ x₁ T) :
    (RelativeMorphism.transport e he ε hε p).baseChangeMap =
      transportSourceMap e he p.base ≫ p.baseChangeMap ≫
        pullback.map p.base x₁ p.base x₂ (𝟙 T) ε.hom (𝟙 Q) (by simp) (by simp [hε]) := by
  refine pullback.hom_ext ?_ ?_
  · refine (RelativeMorphism.baseChangeMap_comp_fst
      (RelativeMorphism.transport e he ε hε p)).trans ?_
    show pullback.fst p.base z₂ = (transportSourceMap e he p.base ≫ p.baseChangeMap ≫
      pullback.map p.base x₁ p.base x₂ (𝟙 T) ε.hom (𝟙 Q) _ _) ≫ pullback.fst p.base x₂
    rw [Category.assoc, Category.assoc, pullback.map_fst, Category.comp_id,
      RelativeMorphism.baseChangeMap_comp_fst, pullback.map_fst, Category.comp_id]
  · refine (RelativeMorphism.baseChangeMap_comp_snd
      (RelativeMorphism.transport e he ε hε p)).trans ?_
    show transportSourceMap e he p.base ≫ p.morphism ≫ ε.hom =
      (transportSourceMap e he p.base ≫ p.baseChangeMap ≫
        pullback.map p.base x₁ p.base x₂ (𝟙 T) ε.hom (𝟙 Q) _ _) ≫ pullback.snd p.base x₂
    rw [Category.assoc, Category.assoc, pullback.map_snd,
      RelativeMorphism.baseChangeMap_comp_snd_assoc]

/-- **Transport preserves relative isomorphisms.** -/
theorem RelativeMorphism.isRelativeIso_transport_iff (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁)
    (ε : X₁ ≅ X₂) (hε : ε.hom ≫ x₂ = x₁) (p : RelativeMorphism B S hS Z₁ X₁ Q z₁ x₁ T) :
    (RelativeMorphism.transport e he ε hε p).IsRelativeIso ↔ p.IsRelativeIso := by
  have key : IsIso (transportSourceMap e he p.base ≫ p.baseChangeMap ≫
      pullback.map p.base x₁ p.base x₂ (𝟙 T) ε.hom (𝟙 Q) (by simp) (by simp [hε])) ↔
        IsIso p.baseChangeMap := by
    rw [isIso_comp_left_iff, isIso_comp_right_iff]
  exact (iff_of_eq (congrArg IsIso
    (RelativeMorphism.baseChangeMap_transport e he ε hε p))).trans key

/-- Transport of pairs along isomorphisms of the source and target over `Q`, as an
equivalence. -/
noncomputable def RelativeMorphism.transportEquiv (e : Z₁ ≅ Z₂) (he : e.hom ≫ z₂ = z₁)
    (ε : X₁ ≅ X₂) (hε : ε.hom ≫ x₂ = x₁) :
    RelativeMorphism B S hS Z₁ X₁ Q z₁ x₁ T ≃ RelativeMorphism B S hS Z₂ X₂ Q z₂ x₂ T where
  toFun := RelativeMorphism.transport e he ε hε
  invFun := RelativeMorphism.transport e.symm (by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc])
    ε.symm (by rw [Iso.symm_hom, ← hε, Iso.inv_hom_id_assoc])
  left_inv p := RelativeMorphism.transport_transport e he ε hε p
  right_inv p := by
    have he' : e.symm.hom ≫ z₁ = z₂ := by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]
    have hε' : ε.symm.hom ≫ x₁ = x₂ := by rw [Iso.symm_hom, ← hε, Iso.inv_hom_id_assoc]
    simpa only [Iso.symm_symm_eq] using
      RelativeMorphism.transport_transport e.symm he' ε.symm hε' p

end Transport

/-! ### Base change of `Isom` along a cartesian square -/

section IsomBaseChange

variable {Z X Q Z' X' Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05Y4 for the subfunctor of isomorphisms of Stacks 0DPP, along arbitrary cartesian
squares.** Let `z : Z ⟶ Q`, `x : X ⟶ Q` and `q : Q' ⟶ Q` be morphisms of algebraic spaces, and
let `z' : Z' ⟶ Q'` and `x' : X' ⟶ Q'` be base changes of `z` and `x` along `q`. Then the
projection `Isom_{Q'}(Z', X') ⟶ Q'` is a base change of the projection `Isom_Q(Z, X) ⟶ Q`
along `q`. -/
theorem exists_isPullback_isomSubfunctor_of_isPullback (z : Z ⟶ Q) (x : X ⟶ Q) (q : Q' ⟶ Q)
    (z' : Z' ⟶ Q') (x' : X' ⟶ Q') (a : Z' ⟶ Z) (c : X' ⟶ X)
    (ha : IsPullback a z' z q) (hc : IsPullback c x' x q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) (hZ' : IsAlgebraicSpace B S hS Z')
    (hX' : IsAlgebraicSpace B S hS X') (hQ' : IsAlgebraicSpace B S hS Q') :
    ∃ g : (isomSubfunctor B S hS Z' X' Q' z' x' hZ' hX' hQ').toFunctor ⟶
        (isomSubfunctor B S hS Z X Q z x hZ hX hQ).toFunctor,
      IsPullback g
        ((isomSubfunctor B S hS Z' X' Q' z' x' hZ' hX' hQ').ι ≫
          relativeHomProjection B S hS Z' X' Q' z' x' hZ' hX' hQ')
        ((isomSubfunctor B S hS Z X Q z x hZ hX hQ).ι ≫
          relativeHomProjection B S hS Z X Q z x hZ hX hQ) q := by
  let e : Z' ≅ pullback q z := ha.flip.isoPullback
  have he : e.hom ≫ pullback.fst q z = z' := ha.flip.isoPullback_hom_fst
  let ε : X' ≅ pullback q x := hc.flip.isoPullback
  have hε : ε.hom ≫ pullback.fst q x = x' := hc.flip.isoPullback_hom_fst
  let H := relativeHomData B S hS Z X Q z x hZ hX hQ
  let H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) :=
    { functor := relativeHom B S hS Z' X' Q' z' x' hZ' hX' hQ'
      projection := relativeHomProjection B S hS Z' X' Q' z' x' hZ' hX' hQ'
      sections T := (relativeHomSections B S hS Z' X' Q' z' x' hZ' hX' hQ' T).trans
        (RelativeMorphism.transportEquiv e he ε hε)
      projection_sections T p :=
        (relativeHomData B S hS Z' X' Q' z' x' hZ' hX' hQ').projection_sections T p
      sections_map {T U} f p := sections_map_of_eq_restrict f (by
        show RelativeMorphism.transport e he ε hε
            (relativeHomSections B S hS Z' X' Q' z' x' hZ' hX' hQ' U
              ((relativeHom B S hS Z' X' Q' z' x' hZ' hX' hQ').map f.op p)) =
          RelativeMorphism.restrict (yoneda.map f) (RelativeMorphism.transport e he ε hε
            (relativeHomSections B S hS Z' X' Q' z' x' hZ' hX' hQ' T p))
        rw [relativeHomSections_map, RelativeMorphism.transport_restrict]) }
  let f := relativeHomOfBaseChange q H H'
  have hsq : IsPullback H'.projection f q H.projection := isPullback_relativeHomOfBaseChange q H H'
  have heq : isomSubfunctor B S hS Z' X' Q' z' x' hZ' hX' hQ' =
      (isomSubfunctor B S hS Z X Q z x hZ hX hQ).preimage f := by
    ext T s
    show (relativeHomSections B S hS Z' X' Q' z' x' hZ' hX' hQ' T.unop s).IsRelativeIso ↔
      (H.sections T.unop (f.app T s)).IsRelativeIso
    rw [sections_relativeHomOfBaseChange, RelativeMorphism.isRelativeIso_ofBaseChange_iff]
    exact (RelativeMorphism.isRelativeIso_transport_iff e he ε hε _).symm
  have key : ∀ I' : Subfunctor (relativeHom B S hS Z' X' Q' z' x' hZ' hX' hQ'),
      I' = (isomSubfunctor B S hS Z X Q z x hZ hX hQ).preimage f →
      ∃ g : I'.toFunctor ⟶ (isomSubfunctor B S hS Z X Q z x hZ hX hQ).toFunctor,
        IsPullback g (I'.ι ≫ relativeHomProjection B S hS Z' X' Q' z' x' hZ' hX' hQ')
          ((isomSubfunctor B S hS Z X Q z x hZ hX hQ).ι ≫
            relativeHomProjection B S hS Z X Q z x hZ hX hQ) q := by
    rintro I' rfl
    exact ⟨_, (isPullback_subfunctor_preimage_base
      (isomSubfunctor B S hS Z X Q z x hZ hX hQ) f).flip.paste_vert hsq.flip⟩
  exact key _ heq

end IsomBaseChange

end AlgebraicGeometry.Space

end
