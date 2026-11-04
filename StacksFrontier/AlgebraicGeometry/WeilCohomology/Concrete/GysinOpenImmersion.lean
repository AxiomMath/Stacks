module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalPieces
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor

/-!
# The Gysin map of an open immersion is restriction

Let `j : U ⟶ X` be an open immersion of schemes smooth over a field `k`. Its Gysin map
`j^! : CH^i(X) ⟶ CH^i(U)` of Stacks 0FF3, graded by codimension (`Stacks.Chow.codimensionGysin`),
is restriction of cycle classes: for every `d`, the part of `j^!β` on the part
`U_d` of `U` of dimension `d` is the restriction of the part `β_d` of `β` along `U_d ⟶ X_d`. This
is the codimension-graded form of Stacks 0FF4 (`f^! = f^*` for flat `f`) for an open immersion,
which has relative dimension zero. In particular `j^!` kills the classes of `X` supported off `U`,
and for the coprojections `X ⟶ X ⨿ Y` it is the projection to the summand.

The proof does not go through the completed bivariant group. On each piece `U_{d,e}` the Gysin map
of `j` restricted to the piece commutes with every class of `A^*(X_e)` (Stacks 0FF6) and carries
`[X_e]_e` to `[U_{d,e}]_d` (Stacks 0FF7); writing `β_e = c ∩ [X_e]_e` (Stacks 0FC2) it therefore
carries `β_e` to `c|_{U_{d,e}} ∩ [U_{d,e}]`, and so does restriction.

## Main definitions

* `Stacks.WeilCohomology.dimPartMap`: the open immersion `U_d ⟶ X_d` induced by `j`.

## Main results

* `Stacks.WeilCohomology.mem_dimPart_of_isOpenImmersion`: `u ∈ U_d → j u ∈ X_d`.
* `Stacks.WeilCohomology.codimensionGysin_of_isOpenImmersion`: `(j^!β)_d = β_d|_{U_d}`.
* `Stacks.WeilCohomology.dimPartPieceGysin_self_of_isOpenImmersion`: the same on the pieces.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The cap action of a class restricted along the identity -/

section CapRestrictId

variable (C : ChowSituation.{u}) (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso)
  {Y V : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : ℤ)

/-- Restriction of a class of Chow cohomology depends on the morphism, not on how it is
written. -/
theorem chowCohomologyRestrictionOfEq_congr {W : Scheme.{u}} (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] {g g' : W ⟶ Y} [LocallyOfFiniteType g] [LocallyOfFiniteType g']
    (h : g = g') (hg : g ≫ sY = sW) (hg' : g' ≫ sY = sW)
    (c : chowCohomologyComponent C G sY p) :
    chowCohomologyRestrictionOfEq C sW sY hg G hgys p c =
      chowCohomologyRestrictionOfEq C sW sY hg' G hgys p c := by
  subst h
  rfl

/-- **The restriction of `c ∈ A^p(Y)` along the identity acts as `c`.** -/
theorem chowCohomologyCap_restrictionOfEq_id (c : chowCohomologyComponent C G sY p) (k : ℤ)
    (γ : chowGroup C sY k) :
    chowCohomologyCap C G sY p
        (chowCohomologyRestrictionOfEq C sY sY (Category.id_comp sY) G hgys p c) k γ =
      chowCohomologyCap C G sY p c k γ := by
  rw [chowCohomologyCap_restrictionOfEq]
  have hfs : pullback.fst (𝟙 Y) (𝟙 Y) = (identityBaseChangeIso (𝟙 Y)).hom := by
    rw [asIso_hom, ← Category.comp_id (pullback.fst (𝟙 Y) (𝟙 Y)), pullback.condition,
      Category.comp_id]
  show _ = chowPushforwardOfIso C (pullback.fst (𝟙 Y) (𝟙 Y) ≫ sY) sY
    (pullback.fst (𝟙 Y) (𝟙 Y)) rfl (k - p) _
  rw [chowPushforwardOfIso_congr_apply C _ _ _ _ hfs rfl (by rw [← hfs])]
  rfl

/-- **The map `c ↦ c ∩ [Y]_e` commutes with restriction along an open immersion**
`j : V ⟶ Y`, when `Y` has `δ`-dimension at most `e`. -/
theorem chowGroupRestrict_chowCohomologyCapFundamentalClass_of_isOpenImmersion
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (j : V ⟶ Y) [IsOpenImmersion j] (hj : j ≫ sY = sV)
    (e : ℤ) (hdim : schemeDeltaDimension C sY ≤ (e : EInt))
    (c : chowCohomologyComponent C G sY p) :
    chowGroupRestrict C sY sV j hj (e - p) (chowCohomologyCapFundamentalClass C G sY e p c) =
      chowCohomologyCapFundamentalClass C G sV e p
        (chowCohomologyRestrictionOfEq C sV sY hj G hgys p c) := by
  rw [← chowCohomologyCap_fundamentalChowClass, ← chowCohomologyCap_fundamentalChowClass,
    ← chowCohomologyCap_restrictionOfEq_id C G hgys sY p c e,
    chowGroupRestrict_chowCohomologyCap_restrictionOfEq C G hgys sY sY sV p (𝟙 Y)
      (Category.id_comp sY) j hj,
    chowGroupRestrict_fundamentalChowClass C sY sV j hj e hdim,
    chowCohomologyRestrictionOfEq_congr C G hgys sY p sV (Category.comp_id j)]

end CapRestrictId

/-! ### Parts of constant dimension along an open immersion -/

section Parts

variable {k : Type u} [Field k] {X U : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sU : U ⟶ (fieldChowSituation k).S) [Smooth sU] {j : U ⟶ X} [IsOpenImmersion j]
  (hj : j ≫ sX = sU)

/-- A relative dimension of a morphism with a point in its source is unique. -/
theorem relativeDimension_unique {V S : Scheme.{u}} {g : V ⟶ S} [LocallyOfFiniteType g]
    (v : V) {d e : ℕ} (hd : RelativeDimension g d) (he : RelativeDimension g e) : d = e := by
  exact_mod_cast (hd _ ⟨g.asFiber v⟩).2.symm.trans (he _ ⟨g.asFiber v⟩).2

include hj in
/-- **An open immersion preserves dimension**: a point of `U` in the part `U_d` of `U` of
dimension `d` maps into the part `X_d` of `X`. On the open neighbourhood
`V = U_d ∩ j⁻¹(X_e)` of the point, for `X_e` the part containing its image, the structure morphism
has relative dimension `d` (from `U_d`) and `e` (from `X_e`), so `d = e`. -/
theorem mem_dimPart_of_isOpenImmersion (d : ℕ) {u : U} (hu : u ∈ dimPart sU d) :
    j u ∈ dimPart sX d := by
  obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart sX).exists_mem (j u)
  let V : U.Opens := dimPart sU d ⊓ j ⁻¹ᵁ dimPart sX e
  have hV1 : RelativeDimension (V.ι ≫ sU) d := by
    have h := RelativeDimension.comp_isOpenImmersion (U.homOfLE (inf_le_left : V ≤ dimPart sU d))
      (partBase sU d) (relativeDimension_partBase sU d)
    exact relativeDimension_of_eq (Scheme.homOfLE_ι_assoc _ _ _) h
  let g : V.toScheme ⟶ (dimPart sX e).toScheme :=
    IsOpenImmersion.lift (dimPart sX e).ι (V.ι ≫ j) (by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact v.2.2)
  have hg : g ≫ (dimPart sX e).ι = V.ι ≫ j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion g := by
    have : IsOpenImmersion (g ≫ (dimPart sX e).ι) := by
      rw [hg]
      infer_instance
    exact IsOpenImmersion.of_comp _ (dimPart sX e).ι
  have hV2 : RelativeDimension (V.ι ≫ sU) e := by
    have h := RelativeDimension.comp_isOpenImmersion g (partBase sX e)
      (relativeDimension_partBase sX e)
    exact relativeDimension_of_eq (by rw [reassoc_of% hg, hj]) h
  rwa [relativeDimension_unique (⟨u, hu, he⟩ : V.toScheme) hV1 hV2]

/-- **The open immersion `U_d ⟶ X_d` induced by `j`** on the parts of dimension `d`. -/
def dimPartMap (d : ℕ) : (dimPart sU d).toScheme ⟶ (dimPart sX d).toScheme :=
  IsOpenImmersion.lift (dimPart sX d).ι ((dimPart sU d).ι ≫ j) (by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact mem_dimPart_of_isOpenImmersion sX sU hj d u.2)

/-- The map `U_d ⟶ X_d` followed by the inclusion `X_d ⟶ X` is the inclusion `U_d ⟶ U` followed
by `j`. -/
@[reassoc (attr := simp)]
theorem dimPartMap_ι (d : ℕ) :
    dimPartMap sX sU hj d ≫ (dimPart sX d).ι = (dimPart sU d).ι ≫ j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The map `U_d ⟶ X_d` induced by `j` is an open immersion. -/
instance (d : ℕ) : IsOpenImmersion (dimPartMap sX sU hj d) := by
  have : IsOpenImmersion (dimPartMap sX sU hj d ≫ (dimPart sX d).ι) := by
    rw [dimPartMap_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (dimPart sX d).ι

/-- The map `U_d ⟶ X_d` commutes with the structure morphisms of `U_d` and `X_d` to the base. -/
theorem dimPartMap_comp_partBase (d : ℕ) :
    dimPartMap sX sU hj d ≫ partBase sX d = partBase sU d := by
  show dimPartMap sX sU hj d ≫ (dimPart sX d).ι ≫ sX = (dimPart sU d).ι ≫ sU
  rw [dimPartMap_ι_assoc, hj]

/-- The restriction `j_{d,d} : U_{d,d} ⟶ X_d` of `j` to the piece of `U_d` over `X_d` is the
inclusion of the piece followed by `U_d ⟶ X_d`. -/
theorem dimPartPieceHom_eq_dimPartMap (d : ℕ) :
    dimPartPieceHom sU sX j d d = (dimPartPiece sU sX j d d).ι ≫ dimPartMap sX sU hj d := by
  rw [← cancel_mono (dimPart sX d).ι]
  simp only [dimPartPieceHom, dimPartPieceToPreimage, Category.assoc, morphismRestrict_ι,
    morphismRestrict_ι_assoc, dimPartMap_ι]

include hj in
/-- The piece `U_{d,e}` of `U_d` over `X_e` is empty for `e ≠ d`. -/
theorem isEmpty_dimPartPiece_of_ne {d e : ℕ} (he : e ≠ d) :
    IsEmpty (dimPartPiece sU sX j d e).toScheme := by
  refine ⟨fun w ↦ ?_⟩
  have hmem : j ((dimPart sU d).ι w.1) ∈ dimPart sX e ⊓ dimPart sX d :=
    ⟨w.2, mem_dimPart_of_isOpenImmersion sX sU hj d w.1.2⟩
  rw [((isClopenDecomposition_dimPart sX).disjoint e d he).eq_bot] at hmem
  exact hmem

/-- **On the piece `U_{d,d}`, the Gysin map of `j` is restriction.** Write `β = c ∩ [X_d]_d`
(Stacks 0FC2). The restriction of `j^!` to the piece commutes with `c` (Stacks 0FF6) and carries
`[X_d]_d` to the fundamental class of the piece (Stacks 0FF7), so it carries `β` to
`c|_{U_{d,d}} ∩ [U_{d,d}]_d`; and restriction of `c ∩ [X_d]_d` to the open piece is that class
too. -/
theorem dimPartPieceGysin_self_of_isOpenImmersion (d : ℕ) (i : ℤ)
    (β : chowGroup (fieldChowSituation k) (partBase sX d) (d - i)) :
    dimPartPieceGysin sU sX hj d d i β =
      chowGroupRestrict (fieldChowSituation k) (partBase sX d) (dimPartPieceBase sU sX j d d)
        (dimPartPieceHom sU sX j d d) (dimPartPieceHom_comp_partBase sU sX hj d d) (d - i) β := by
  obtain ⟨c, rfl⟩ := capFundamentalClassSurjective k (partBase sX d) d
    (relativeDimension_partBase sX d) i β
  refine eq_of_heq ?_
  simp only [dimPartPieceGysin, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ?_
  refine (BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq
    (fieldChowSituation k) (gysinSystemOfInvertible _)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) (partBase sX d)
    (dimPartPieceBase sU sX j d d) i (dimPartPieceHom_comp_partBase sU sX hj d d) ((d : ℤ) - d)
    (dimPartPieceGysinClass sU sX hj d d) c
    (dimPartPieceGysinClass_bivariantCommute sU sX hj d d i c)
    d (dimPartPieceGysinClass_capTargetHom_fundamentalChowClass sU sX hj d d)
    (by ring : (d : ℤ) - ((d : ℤ) - d) = d)).trans ?_
  rw [chowGroupRestrict_chowCohomologyCapFundamentalClass_of_isOpenImmersion _ _
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) _ _ _ _ _ _
    (schemeDeltaDimension_le_of_relativeDimension _ (relativeDimension_partBase sX d))]

/-- **The Gysin map of an open immersion is restriction.** For an open immersion `j : U ⟶ X` of
schemes smooth over `k` and `β ∈ CH^i(X)`, the part of `j^!β ∈ CH^i(U)` on the part `U_d` of
`U` of dimension `d` is the restriction of `β_d ∈ CH_{d-i}(X_d)` along `U_d ⟶ X_d`. This is the
codimension-graded form of Stacks 0FF4 for `j`, flat of relative dimension zero. -/
theorem codimensionGysin_of_isOpenImmersion (i : ℤ) (β : codimensionChowGroup k sX i) (d : ℕ) :
    codimensionGysin sU sX hj i β d =
      chowGroupRestrict (fieldChowSituation k) (partBase sX d) (partBase sU d)
        (dimPartMap sX sU hj d) (dimPartMap_comp_partBase sX sU hj d) (d - i) (β d) := by
  refine (chowGroupDimPartPieceEquiv sU sX (f := j) d (d - i)).injective (funext fun e ↦ ?_)
  obtain ⟨e⟩ := e
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  by_cases hde : e = d
  · subst hde
    rw [chowGroupRestrict_comp, dimPartPieceGysin_self_of_isOpenImmersion]
    exact DFunLike.congr_fun (chowGroupRestrict_congr _ _ _ _ _ _ _
      (dimPartPieceHom_eq_dimPartMap sX sU hj e) _) _
  · have := isEmpty_dimPartPiece_of_ne sX sU hj hde
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

end Parts

end Stacks.WeilCohomology

end
