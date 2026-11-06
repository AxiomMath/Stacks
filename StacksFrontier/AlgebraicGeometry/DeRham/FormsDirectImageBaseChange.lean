module

public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageSection
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Corner

/-!
# Flat base change of the comparison map `Ω^d_{X/S} ⟶ b_*Ω^d_{Y/S}`

For a morphism `b : Y ⟶ X` of schemes over `S`, the canonical map
`Ω^d_{X/S} ⟶ b_*Ω^d_{Y/S}` is `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`.  This file
proves that it is compatible with base change.  Take a commutative square `h ≫ b = b' ≫ g` and
bases with `g ≫ p = p' ≫ s`.  Then the inverse image along `g` of the comparison map of `b`,
followed by the base-change map `g^*b_* ⟶ b'_*h^*` and by `b'_*` of the canonical map on forms
along `h`, is the canonical map on forms along `g` followed by the comparison map of `b'`.

This is the compatibility the étale-local reductions of [Stacks, Tag 0FUU] use for all three of
its clauses: for `b` itself in clause (1), for `p : E ⟶ Z` in clause (2), and for the restriction
`Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}` in clause (3).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparisonOver`: the comparison map attached to
  a commutative square `f ≫ p = q ≫ s`, where the base of the source may move.  With
  `q = f ≫ p` and `s = 𝟙` it is `formsDirectImageComparison`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparisonOver_comp`: the composition law.
* `Stacks.DeRham.formsDirectImageComparison_baseChange`: the base-change square.
* `Stacks.DeRham.isIso_formsDirectImageComparison_of_isPullback` and
  `Stacks.DeRham.isIso_pullback_formsDirectImageComparison_of_isPullback`: for a cartesian square
  with `g` flat and `b` quasi-compact and quasi-separated, and with the two canonical maps on
  forms invertible (for instance by [Stacks, Tag 0FLV] when `g` and `s` are étale), invertibility
  transfers in both directions.  The second statement concludes only invertibility after inverse
  image along `g`.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y W S S' S'' : Scheme.{u}}

/-- The comparison `Ω^d_{X/S} ⟶ f_*Ω^d_{Y/S'}` attached to a commutative square
`f ≫ p = q ≫ s`. -/
def formsDirectImageComparisonOver (f : Y ⟶ X) (p : X ⟶ S) (q : Y ⟶ S') (s : S' ⟶ S)
    (w : f ≫ p = q ≫ s) (d : ℤ) :
    relativeDifferentialForms p d ⟶
      (Scheme.Modules.pushforward f).obj (relativeDifferentialForms q d) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (relativeDifferentialForms p d) ≫
    (Scheme.Modules.pushforward f).map (relativeDifferentialFormsMap f p q s w d)

/-- With the identity on the base, the comparison over a square is the plain comparison map. -/
theorem formsDirectImageComparisonOver_eq (f : Y ⟶ X) (p : X ⟶ S) (d : ℤ) :
    formsDirectImageComparisonOver f p (f ≫ p) (𝟙 S) (by simp) d =
      formsDirectImageComparison f p d := rfl

/-- **The composition law** for the comparison map over squares. -/
theorem formsDirectImageComparisonOver_comp (f : Y ⟶ X) (g : W ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S')
    (r : W ⟶ S'') (s : S' ⟶ S) (t : S'' ⟶ S') (u : S'' ⟶ S) (w : f ≫ p = q ≫ s)
    (w' : g ≫ q = r ≫ t) (w'' : (g ≫ f) ≫ p = r ≫ u) (d : ℤ) :
    formsDirectImageComparisonOver (g ≫ f) p r u w'' d =
      formsDirectImageComparisonOver f p q s w d ≫
        (Scheme.Modules.pushforward f).map (formsDirectImageComparisonOver g q r t w' d) ≫
        (Scheme.Modules.pushforwardComp g f).hom.app _ := by
  have hu := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)) (Scheme.Modules.pullbackComp g f).inv
    (relativeDifferentialForms p d)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at hu
  simp only [formsDirectImageComparisonOver]
  rw [relativeDifferentialFormsMap_comp f g p q r s t u w w' w'' d, Functor.map_comp,
    Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hu]
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
    (relativeDifferentialFormsMap f p q s w d)
  simp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← (Scheme.Modules.pushforwardComp g f).hom.naturality_assoc,
    ← (Scheme.Modules.pushforwardComp g f).hom.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [Functor.map_comp, reassoc_of% hn]
  rfl

/-- The comparison map along equal morphisms, read through `pushforwardCongr`. -/
theorem formsDirectImageComparisonOver_congr {f₁ f₂ : Y ⟶ X} (p : X ⟶ S) (q : Y ⟶ S')
    (s : S' ⟶ S) (w₁ : f₁ ≫ p = q ≫ s) (w₂ : f₂ ≫ p = q ≫ s) (hf : f₁ = f₂) (d : ℤ) :
    formsDirectImageComparisonOver f₁ p q s w₁ d ≫
        (Scheme.Modules.pushforwardCongr hf).hom.app _ =
      formsDirectImageComparisonOver f₂ p q s w₂ d := by
  subst hf
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRham

open _root_.AlgebraicGeometry.Scheme.Hom

variable {X X' Y Y' S S' : Scheme.{u}} (b : Y ⟶ X) (b' : Y' ⟶ X') (g : X' ⟶ X) (h : Y' ⟶ Y)
  (w : h ≫ b = b' ≫ g) (p : X ⟶ S) (p' : X' ⟶ S') (s : S' ⟶ S) (hs : g ≫ p = p' ≫ s)

include w hs in
/-- The square of structure morphisms induced on `Y' ⟶ Y`. -/
theorem forms_square_comm_aux : h ≫ b ≫ p = (b' ≫ p') ≫ s := by
  rw [reassoc_of% w, hs, Category.assoc]

/-- **Base change of the comparison map.**  For a commutative square `h ≫ b = b' ≫ g` and bases
with `g ≫ p = p' ≫ s`, the square
```
g^*Ω_{X/S} --g^*(cmp b)--> g^*b_*Ω_{Y/S} --bc--> b'_*h^*Ω_{Y/S} --b'_*φ_h--> b'_*Ω_{Y'/S'}
     ‖                                                                          ‖
g^*Ω_{X/S} --φ_g--> Ω_{X'/S'} ------------------cmp b'-------------------> b'_*Ω_{Y'/S'}
```
commutes.  Both sides are transposed along `g^* ⊣ g_*`.  The transposes are the two ways of
writing the comparison map of the diagonal `Y' ⟶ X` given by the composition law. -/
theorem formsDirectImageComparison_baseChange (d : ℤ) :
    (Scheme.Modules.pullback g).map (formsDirectImageComparison b p d) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app _ ≫
        (Scheme.Modules.pushforward b').map
          (relativeDifferentialFormsMap h (b ≫ p) (b' ≫ p') s
            (forms_square_comm_aux b b' g h w p p' s hs) d) =
      relativeDifferentialFormsMap g p p' s hs d ≫ formsDirectImageComparison b' p' d := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
    (formsDirectImageComparison b p d)
  simp only [Functor.id_map, Functor.comp_map] at hu
  have hsq :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pushforward_unit_comp_pushforwardSquareIso
    w (relativeDifferentialForms (b ≫ p) d)
  have hnat := (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.naturality
    (relativeDifferentialFormsMap h (b ≫ p) (b' ≫ p') s
      (forms_square_comm_aux b b' g h w p p' s hs) d)
  simp only [Functor.comp_map] at hnat
  have e0 : b ≫ p = (b ≫ p) ≫ 𝟙 S := by simp
  have e1 : h ≫ b ≫ p = (b' ≫ p') ≫ s := forms_square_comm_aux b b' g h w p p' s hs
  have e2 : (h ≫ b) ≫ p = (b' ≫ p') ≫ s := by rw [Category.assoc, e1]
  have e3 : b' ≫ p' = (b' ≫ p') ≫ 𝟙 S' := by simp
  have e4 : (b' ≫ g) ≫ p = (b' ≫ p') ≫ s := by rw [Category.assoc, hs, Category.assoc]
  rw [← reassoc_of% hu, ← reassoc_of% hsq, ← hnat]
  have hL : formsDirectImageComparison b p d ≫
      (Scheme.Modules.pushforward b).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
          (relativeDifferentialForms (b ≫ p) d)) ≫
      (Scheme.Modules.pushforward b).map ((Scheme.Modules.pushforward h).map
        (relativeDifferentialFormsMap h (b ≫ p) (b' ≫ p') s e1 d)) =
      formsDirectImageComparisonOver b p (b ≫ p) (𝟙 S) e0 d ≫
        (Scheme.Modules.pushforward b).map
          (formsDirectImageComparisonOver h (b ≫ p) (b' ≫ p') s e1 d) := by
    rw [← Functor.map_comp]
    rfl
  rw [reassoc_of% hL]
  have hR :
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (relativeDifferentialForms p d) ≫
      (Scheme.Modules.pushforward g).map (relativeDifferentialFormsMap g p p' s hs d) ≫
      (Scheme.Modules.pushforward g).map (formsDirectImageComparison b' p' d) =
      formsDirectImageComparisonOver g p p' s hs d ≫
        (Scheme.Modules.pushforward g).map
          (formsDirectImageComparisonOver b' p' (b' ≫ p') (𝟙 S') e3 d) :=
    rfl
  rw [hR, ← Iso.cancel_iso_hom_right _ _ ((Scheme.Modules.pushforwardComp b' g).app _)]
  simp only [Category.assoc, Iso.app_hom]
  rw [← formsDirectImageComparisonOver_comp g b' p p' (b' ≫ p') s (𝟙 S') s hs e3 e4 d,
    ← formsDirectImageComparisonOver_congr p (b' ≫ p') s e2 e4 w d,
    formsDirectImageComparisonOver_comp b h p (b ≫ p) (b' ≫ p') (𝟙 S) s s e0 e1 e2 d]
  simp only [Category.assoc, AlgebraicGeometry.AffinePushforward.pushforwardSquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.inv_hom_id_app, Category.comp_id]

variable {b b' g h}

/-- **Transfer of invertibility along a square with invertible base-change map.** -/
theorem isIso_formsDirectImageComparison_of_baseChange (w : h ≫ b = b' ≫ g) (d : ℤ)
    [IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      (relativeDifferentialForms (b ≫ p) d))]
    [IsIso (relativeDifferentialFormsMap g p p' s hs d)]
    [IsIso (relativeDifferentialFormsMap h (b ≫ p) (b' ≫ p') s
      (forms_square_comm_aux b b' g h w p p' s hs) d)] :
    IsIso ((Scheme.Modules.pullback g).map (formsDirectImageComparison b p d)) ↔
      IsIso (formsDirectImageComparison b' p' d) := by
  have hsq := formsDirectImageComparison_baseChange b b' g h w p p' s hs d
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : IsIso (relativeDifferentialFormsMap g p p' s hs d ≫
        formsDirectImageComparison b' p' d) := by
      rw [← hsq]
      infer_instance
    exact IsIso.of_isIso_comp_left (relativeDifferentialFormsMap g p p' s hs d) _
  · have : IsIso (relativeDifferentialFormsMap g p p' s hs d ≫
        formsDirectImageComparison b' p' d) := inferInstance
    rw [← hsq] at this
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this

/-- **Restriction to an open of the target.**  The comparison map of `b`, restricted to an open
`V` of `X`, is invertible as soon as the comparison map of `b ∣_ V` is.  No hypothesis on `b` is
needed: the base-change map of an open restriction square is always invertible. -/
theorem isIso_pullback_ι_formsDirectImageComparison (b : Y ⟶ X) (p : X ⟶ S) (V : X.Opens)
    (d : ℤ) (hV : IsIso (formsDirectImageComparison (b ∣_ V) (V.ι ≫ p) d)) :
    IsIso ((Scheme.Modules.pullback V.ι).map (formsDirectImageComparison b p d)) := by
  have w := Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare b V
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      (relativeDifferentialForms (b ≫ p) d)) :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare b V _
  have hs : V.ι ≫ p = (V.ι ≫ p) ≫ 𝟙 S := by simp
  have : IsIso (relativeDifferentialFormsMap V.ι p (V.ι ≫ p) (𝟙 S) hs d) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap (b ⁻¹ᵁ V).ι (b ≫ p) ((b ∣_ V) ≫ V.ι ≫ p) (𝟙 S)
      (forms_square_comm_aux b (b ∣_ V) V.ι (b ⁻¹ᵁ V).ι w p (V.ι ≫ p) (𝟙 S) hs) d) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  exact (isIso_formsDirectImageComparison_of_baseChange p (V.ι ≫ p) (𝟙 S) hs w d).2 hV

/-- **Changing the base along an étale morphism.**  For `b : Y ⟶ X`, `p₁ : X ⟶ S₁` and an étale
`s : S₁ ⟶ S`, the comparison map of `b` for forms over `S₁` is invertible exactly when the one for
forms over `S` is: `Ω_{X/S} = Ω_{X/S₁}` and `Ω_{Y/S} = Ω_{Y/S₁}` ([Stacks, Tag 0FLV]). -/
theorem isIso_formsDirectImageComparison_comp_etale (b : Y ⟶ X) (p₁ : X ⟶ S') (s : S' ⟶ S)
    [Etale s] (d : ℤ) (h : IsIso (formsDirectImageComparison b p₁ d)) :
    IsIso (formsDirectImageComparison b (p₁ ≫ s) d) := by
  have hs : 𝟙 X ≫ p₁ ≫ s = p₁ ≫ s := Category.id_comp _
  have w : 𝟙 Y ≫ b = b ≫ 𝟙 X := by simp
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      (relativeDifferentialForms (b ≫ p₁ ≫ s) d)) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isIso w _
  have : IsIso (relativeDifferentialFormsMap (𝟙 X) (p₁ ≫ s) p₁ s hs d) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap (𝟙 Y) (b ≫ p₁ ≫ s) (b ≫ p₁) s
      (forms_square_comm_aux b b (𝟙 X) (𝟙 Y) w (p₁ ≫ s) p₁ s hs) d) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackId _) _).1
    ((isIso_formsDirectImageComparison_of_baseChange (p₁ ≫ s) p₁ s hs w d).2 h)

/-- In a cartesian square with `g` flat and `b` quasi-compact and quasi-separated, and with the two
canonical maps on forms invertible, the inverse image along `g` of the comparison map of `b` is
invertible exactly when the comparison map of `b'` is. -/
private theorem isIso_pullback_formsDirectImageComparison_iff_of_isPullback
    (H : IsPullback h b' b g) [Flat g] [QuasiCompact b] [QuasiSeparated b] (d : ℕ)
    [IsIso (relativeDifferentialFormsMap g p p' s hs (d : ℤ))]
    [IsIso (relativeDifferentialFormsMap h (b ≫ p) (b' ≫ p') s
      (forms_square_comm_aux b b' g h H.w p p' s hs) (d : ℤ))] :
    IsIso ((Scheme.Modules.pullback g).map (formsDirectImageComparison b p (d : ℤ))) ↔
      IsIso (formsDirectImageComparison b' p' (d : ℤ)) := by
  have := AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms (b ≫ p) d
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H
    (relativeDifferentialForms (b ≫ p) (d : ℤ))
  exact isIso_formsDirectImageComparison_of_baseChange p p' s hs H.w (d : ℤ)

/-- **Flat base change of the comparison map, as an isomorphism of arrows.** In a cartesian square
with `g` flat and `b` quasi-compact and quasi-separated, and with the two canonical maps on forms
invertible, invertibility of `Ω^d_{X/S} ⟶ b_*Ω^d_{Y/S}` gives that of
`Ω^d_{X'/S'} ⟶ b'_*Ω^d_{Y'/S'}`. -/
theorem isIso_formsDirectImageComparison_of_isPullback (H : IsPullback h b' b g) [Flat g]
    [QuasiCompact b] [QuasiSeparated b] (d : ℕ)
    [IsIso (relativeDifferentialFormsMap g p p' s hs (d : ℤ))]
    [IsIso (relativeDifferentialFormsMap h (b ≫ p) (b' ≫ p') s
      (forms_square_comm_aux b b' g h H.w p p' s hs) (d : ℤ))]
    (hb : IsIso (formsDirectImageComparison b p (d : ℤ))) :
    IsIso (formsDirectImageComparison b' p' (d : ℤ)) := by
  exact (isIso_pullback_formsDirectImageComparison_iff_of_isPullback p p' s hs H d).1 inferInstance

/-- **Flat base change of the comparison map, the converse direction.** Under the hypotheses of
`isIso_formsDirectImageComparison_of_isPullback`, invertibility of the comparison map of `b'`
gives invertibility of the inverse image along `g` of the comparison map of `b`. -/
theorem isIso_pullback_formsDirectImageComparison_of_isPullback (H : IsPullback h b' b g)
    [Flat g] [QuasiCompact b] [QuasiSeparated b] (d : ℕ)
    [IsIso (relativeDifferentialFormsMap g p p' s hs (d : ℤ))]
    [IsIso (relativeDifferentialFormsMap h (b ≫ p) (b' ≫ p') s
      (forms_square_comm_aux b b' g h H.w p p' s hs) (d : ℤ))]
    (hb' : IsIso (formsDirectImageComparison b' p' (d : ℤ))) :
    IsIso ((Scheme.Modules.pullback g).map (formsDirectImageComparison b p (d : ℤ))) := by
  exact (isIso_pullback_formsDirectImageComparison_iff_of_isPullback p p' s hs H d).2 hb'

end Stacks.DeRham
