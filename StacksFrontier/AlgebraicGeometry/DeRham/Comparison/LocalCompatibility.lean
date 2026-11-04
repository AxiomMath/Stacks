module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.ExistenceBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Uniqueness

/-!
# Compatible maps `c^p` on opens of a base change square

Let `b ≫ f = f' ≫ a` be a commutative square of schemes inducing an isomorphism of `Y'` with an
open subscheme of `X' ×_X Y`, with `f` locally quasi-finite and syntomic. Around every point of
`Y'` there are opens `V' ⊆ Y'`, `V ⊆ Y`, `U' ⊆ X'`, `U ⊆ X` forming a square of the same kind,
and maps `c^p_{V/U}`, `c^p_{V'/U'}` satisfying (0H9C) and (0H9D) which are compatible in the sense
of Lemma 0H9G.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_garelMaps_isCompatible_resLE`: Lemma 0H9H. The opens may
  be taken to be the whole schemes, with the glued maps of Lemma 0FLA on both sides.
* `AlgebraicGeometry.Scheme.Hom.resLE_comp_resLE_eq`: the restrictions of a commutative square to
  opens commute.
* `AlgebraicGeometry.Scheme.Hom.isOpenImmersion_lift_resLE_resLE`: the restriction to opens of a
  square inducing an open immersion into the fibre product induces one too.

## References

* [Stacks Project, Tag 0H9H](https://stacks.math.columbia.edu/tag/0H9H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X X' Y Y' : Scheme.{u}} {f : Y ⟶ X} {a : X' ⟶ X} {f' : Y' ⟶ X'} {b : Y' ⟶ Y}
  {U : X.Opens} {U' : X'.Opens} {V : Y.Opens} {V' : Y'.Opens}

/-- The restriction to opens `V' ⊆ b⁻¹V ∩ f'⁻¹U'`, `V ⊆ f⁻¹U` and `U' ⊆ a⁻¹U` of a commutative
square `b ≫ f = f' ≫ a` commutes. -/
theorem resLE_comp_resLE_eq (w : b ≫ f = f' ≫ a) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f' ⁻¹ᵁ U')
    (hU : U' ≤ a ⁻¹ᵁ U) (hV : V' ≤ b ⁻¹ᵁ V) :
    b.resLE V V' hV ≫ f.resLE U V e = f'.resLE U' V' e' ≫ a.resLE U U' hU := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, resLE_comp_ι, resLE_comp_ι_assoc, w]

/-- If a commutative square `b ≫ f = f' ≫ a` induces an open immersion `Y' ⟶ X' ×_X Y`, then so
does its restriction to opens `V' ⊆ b⁻¹V ∩ f'⁻¹U'`, `V ⊆ f⁻¹U` and `U' ⊆ a⁻¹U`. -/
theorem isOpenImmersion_lift_resLE_resLE (w : b ≫ f = f' ≫ a)
    [IsOpenImmersion (pullback.lift b f' w)] (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f' ⁻¹ᵁ U')
    (hU : U' ≤ a ⁻¹ᵁ U) (hV : V' ≤ b ⁻¹ᵁ V) :
    IsOpenImmersion (pullback.lift (b.resLE V V' hV) (f'.resLE U' V' e')
      (resLE_comp_resLE_eq w e e' hU hV)) := by
  let m := pullback.map _ _ f a V.ι U'.ι U.ι (resLE_comp_ι f e) (resLE_comp_ι a hU)
  have h : pullback.lift (b.resLE V V' hV) (f'.resLE U' V' e')
      (resLE_comp_resLE_eq w e e' hU hV) ≫ m = V'.ι ≫ pullback.lift b f' w := by
    ext <;> simp only [m, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, resLE_comp_ι]
  have : IsOpenImmersion (V'.ι ≫ pullback.lift b f' w) := inferInstance
  rw [← h] at this
  exact IsOpenImmersion.of_comp _ m

/-- **Stacks Project, Lemma 0H9H.** Let `b ≫ f = f' ≫ a` be a commutative square of schemes
which induces an isomorphism of `Y'` with an open subscheme of `X' ×_X Y`, with `f` locally
quasi-finite and syntomic. Then for every `y' ∈ Y'` there are opens `V' ⊆ Y'`, `V ⊆ Y`,
`U' ⊆ X'`, `U ⊆ X` with `y' ∈ V'`, `f'(V') ⊆ U'`, `b(V') ⊆ V`, `a(U') ⊆ U` and `f(V) ⊆ U`, and
maps `c^p_{V/U}` and `c^p_{V'/U'}` satisfying (0H9C) and (0H9D) which are compatible with the
restricted square in the sense of Lemma 0H9G, through the identification
`b^*det(NL_{V/U}) = det(NL_{V'/U'})` of Lemma 0FKB. -/
@[stacks 0H9H "for every y' there are opens V' ∋ y', V, U', U of the square and maps c^p_{V/U}, \
c^p_{V'/U'} satisfying 0H9C and 0H9D compatible in the sense of 0H9G"]
theorem exists_garelMaps_isCompatible_resLE (w : b ≫ f = f' ≫ a)
    [IsOpenImmersion (pullback.lift b f' w)] (hf : Syntomic f) [LocallyQuasiFinite f] (y' : Y') :
    ∃ (V' : Y'.Opens) (V : Y.Opens) (U' : X'.Opens) (U : X.Opens) (e' : V' ≤ f' ⁻¹ᵁ U')
      (hV : V' ≤ b ⁻¹ᵁ V) (hU : U' ≤ a ⁻¹ᵁ U) (e : V ≤ f ⁻¹ᵁ U), y' ∈ V' ∧
      haveI := isOpenImmersion_lift_resLE_resLE w e e' hU hV
      haveI := locallyQuasiFinite_of_isOpenImmersion_lift (resLE_comp_resLE_eq w e e' hU hV)
      ∃ (c : (f.resLE U V e).GarelMaps
          ((f.resLE U V e).detNL (IsZariskiLocalAtSource.resLE (P := @Syntomic) e hf)))
        (c' : (f'.resLE U' V' e').GarelMaps ((f'.resLE U' V' e').detNL
          (syntomic_of_isOpenImmersion_lift (resLE_comp_resLE_eq w e e' hU hV)
            (IsZariskiLocalAtSource.resLE (P := @Syntomic) e hf)))),
        c.IsNormalized
            ((f.resLE U V e).deltaNL (IsZariskiLocalAtSource.resLE (P := @Syntomic) e hf)) ∧
          c.IsMultiplicative ∧
          c'.IsNormalized ((f'.resLE U' V' e').deltaNL
            (syntomic_of_isOpenImmersion_lift (resLE_comp_resLE_eq w e e' hU hV)
              (IsZariskiLocalAtSource.resLE (P := @Syntomic) e hf))) ∧
          c'.IsMultiplicative ∧
          GarelMaps.IsCompatible (resLE_comp_resLE_eq w e e' hU hV)
            (detNLPullbackIso (resLE_comp_resLE_eq w e e' hU hV)
              (IsZariskiLocalAtSource.resLE (P := @Syntomic) e hf)
              (syntomic_of_isOpenImmersion_lift (resLE_comp_resLE_eq w e e' hU hV)
                (IsZariskiLocalAtSource.resLE (P := @Syntomic) e hf))).hom c c' := by
  have e : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e' : (⊤ : Y'.Opens) ≤ f' ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hU : (⊤ : X'.Opens) ≤ a ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hV : (⊤ : Y'.Opens) ≤ b ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have wr := resLE_comp_resLE_eq w e e' hU hV
  have := isOpenImmersion_lift_resLE_resLE w e e' hU hV
  have := locallyQuasiFinite_of_isOpenImmersion_lift wr
  have hr := IsZariskiLocalAtSource.resLE (P := @Syntomic) e hf
  have hr' := syntomic_of_isOpenImmersion_lift wr hr
  exact ⟨⊤, ⊤, ⊤, ⊤, e', hV, hU, e, trivial, (f.resLE ⊤ ⊤ e).chartGarelMaps hr,
    (f'.resLE ⊤ ⊤ e').chartGarelMaps hr', chartGarelMaps_isNormalized _ hr,
    chartGarelMaps_isMultiplicative _ hr, chartGarelMaps_isNormalized _ hr',
    chartGarelMaps_isMultiplicative _ hr', chartGarelMaps_isCompatible _ hr wr hr'⟩

end AlgebraicGeometry.Scheme.Hom

end
