module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealizationBijection
public import StacksCore.Tactic.StacksAttribute

/-!
# Weil cohomology theories as realizations of Chow motives: condition (2)

Proposition 0GIJ of the Stacks Project: a Weil cohomology theory (Definition 0FI2) is the same
thing as a `ℚ`-linear symmetric monoidal functor `G : M_k ⥤ graded F-vector spaces` such that

1. `G(𝟏(1))` is nonzero only in degree `-2`, and
2. for every smooth projective `X` over `k` with `k' = Γ(X, 𝒪_X)` the map
   `G(h(Spec k')) → G(h(X))` is an isomorphism in degree `0`.

The source deduces it from Proposition 0FHM, the correspondence between data (D0)–(D3)
satisfying (A), (B), (C) and functors satisfying (1), by restricting both sides: a Weil
cohomology theory is such data satisfying in addition condition (2) of Lemma 0FI0,
`H^0(Spec k') → H^0(X)` is an isomorphism, and under `H^*(X) = G(h(X))` this is condition (2)
above. This file provides the pieces of that restriction:

* condition (2) on realizations (`Stacks.WeilCohomology.WeilRealization.GlobalSections`) and
  its invariance under isomorphism of realizations;
* the invariance of condition (2) of Lemma 0FI0 under isomorphism of data (D0)–(D3);
* the comparison of the two conditions for the data `H^*(X) = G(h(X))` of a realization
  (Stacks 0FHK);
* isomorphism classes of Weil cohomology theories as isomorphism classes of data satisfying
  (A), (B), (C) and condition (2) of Lemma 0FI0;
* the restriction of a bijection of isomorphism classes to subclasses that correspond.

## Main definitions

* `Stacks.WeilCohomology.WeilRealization.GlobalSections`: condition (2) of Stacks 0GIJ.
* `Stacks.WeilCohomology.WeilCohomologyTheory.isoSetoid`: isomorphism of Weil cohomology
  theories, the isomorphism of their data (D0)–(D3).
* `Stacks.WeilCohomology.WeilCohomologyTheory.equivWeilDataAxiomsSubtype`: a Weil cohomology
  theory is data satisfying (A), (B), (C) and condition (2) of Lemma 0FI0.

## Main results

* `Stacks.WeilCohomology.WeilRealization.exists_globalSections_isoClassEquiv`: **Stacks 0GIJ**.

* `Stacks.WeilCohomology.WeilRealization.globalSections_iff_of_iso`: condition (2) is invariant
  under isomorphism of realizations.
* `Stacks.WeilCohomology.WeilData.IsIsomorphic.globalSectionsCondition_iff`: condition (2) of
  Lemma 0FI0 is invariant under isomorphism of data (D0)–(D3).
* `Stacks.WeilCohomology.WeilRealization.toWeilDataAxioms_globalSectionsCondition_iff`: the data
  of a realization `G` satisfy condition (2) of Lemma 0FI0 exactly when `G` satisfies condition
  (2) of Stacks 0GIJ.
* `Stacks.WeilCohomology.exists_quotientEquiv_restrict`: a bijection of quotients restricts to
  subtypes whose predicates agree on corresponding classes.
* `Stacks.WeilCohomology.WeilRealization.exists_globalSections_isoClassEquiv_of`: a bijection
  between isomorphism classes of realizations and of data satisfying (A), (B), (C), induced by a
  construction carrying condition (2) to condition (2) of Lemma 0FI0, restricts to a bijection
  between isomorphism classes of realizations satisfying condition (2) and of Weil cohomology
  theories.

## References

* [Stacks Project, Tag 0GIJ](https://stacks.math.columbia.edu/tag/0GIJ)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
* [Stacks Project, Tag 0FHK](https://stacks.math.columbia.edu/tag/0FHK)
* [Stacks Project, Tag 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GradedCategory Opposite

universe u w

namespace Stacks.WeilCohomology

/-! ### Restricting a bijection of quotients -/

/-- Two elements of a subtype have the same class for the induced setoid exactly when their
values have the same class. -/
theorem quotient_mk_comap_val_eq_iff {δ : Type*} (r : Setoid δ) (R : δ → Prop)
    (x y : Subtype R) :
    Quotient.mk (r.comap Subtype.val) x = Quotient.mk _ y ↔
      Quotient.mk r x.1 = Quotient.mk r y.1 :=
  ⟨fun h ↦ @Quotient.sound _ r x.1 y.1 (@Quotient.exact _ (r.comap Subtype.val) x y h),
    fun h ↦ @Quotient.sound _ (r.comap Subtype.val) x y (@Quotient.exact _ r x.1 y.1 h)⟩

/-- **A bijection of quotients restricts to subtypes.** Let `e : α/s ≃ β/t` and let `P`, `Q` be
predicates such that `P a ↔ Q b` whenever `e` sends the class of `a` to the class of `b`. Then
`e` restricts to a bijection between the quotients of `{a // P a}` and `{b // Q b}`. -/
theorem exists_quotientEquiv_restrict {α β : Type*} {s : Setoid α} {t : Setoid β}
    (e : Quotient s ≃ Quotient t) (P : α → Prop) (Q : β → Prop)
    (hPQ : ∀ a b, e (Quotient.mk s a) = Quotient.mk t b → (P a ↔ Q b)) :
    ∃ e' : Quotient (s.comap (Subtype.val : Subtype P → α)) ≃
        Quotient (t.comap (Subtype.val : Subtype Q → β)),
      ∀ (a : Subtype P) (b : Subtype Q),
        e' (Quotient.mk _ a) = Quotient.mk _ b ↔ e (Quotient.mk s a.1) = Quotient.mk t b.1 := by
  let φ : Subtype P → Quotient (t.comap (Subtype.val : Subtype Q → β)) := fun a ↦
    Quotient.mk _ ⟨(e (Quotient.mk s a.1)).out,
      (hPQ a.1 _ (Quotient.out_eq _).symm).1 a.2⟩
  let ψ : Subtype Q → Quotient (s.comap (Subtype.val : Subtype P → α)) := fun b ↦
    Quotient.mk _ ⟨(e.symm (Quotient.mk t b.1)).out,
      (hPQ _ b.1 (by rw [Quotient.out_eq, Equiv.apply_symm_apply])).2 b.2⟩
  have hφ : ∀ a a', a ≈ a' → φ a = φ a' := fun a a' h ↦ by
    refine (quotient_mk_comap_val_eq_iff t Q _ _).2 ?_
    simp only [Quotient.out_eq]
    exact congrArg e (@Quotient.sound _ s a.1 a'.1 h)
  have hψ : ∀ b b', b ≈ b' → ψ b = ψ b' := fun b b' h ↦ by
    refine (quotient_mk_comap_val_eq_iff s P _ _).2 ?_
    simp only [Quotient.out_eq]
    exact congrArg e.symm (@Quotient.sound _ t b.1 b'.1 h)
  have hl : Function.LeftInverse (Quotient.lift ψ hψ) (Quotient.lift φ hφ) := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      refine (quotient_mk_comap_val_eq_iff s P _ _).2 ?_
      simp only [Quotient.out_eq, Equiv.symm_apply_apply]
  have hr : Function.RightInverse (Quotient.lift ψ hψ) (Quotient.lift φ hφ) := by
    intro q
    induction q using Quotient.inductionOn with
    | h b =>
      refine (quotient_mk_comap_val_eq_iff t Q _ _).2 ?_
      simp only [Quotient.out_eq, Equiv.apply_symm_apply]
  refine ⟨Equiv.mk (Quotient.lift φ hφ) (Quotient.lift ψ hψ) hl hr, fun a b ↦ ?_⟩
  change φ a = _ ↔ _
  rw [quotient_mk_comap_val_eq_iff, Quotient.out_eq]

/-- Two morphisms of a twisted Karoubi envelope between equal objects are equal (heterogeneously)
when their underlying morphisms are. -/
theorem _root_.CategoryTheory.GradedCategory.TwistedKaroubi.heq_of_heq_val {R C : Type*} [Ring R]
    [Category C] [Preadditive C] [GradedCategory R C] {M N M' N' : TwistedKaroubi R C}
    (f : M ⟶ N) (g : M' ⟶ N') (hM : M = M') (hN : N = N') (h : f.val ≍ g.val) : f ≍ g := by
  subst hM hN
  exact heq_of_eq (TwistedKaroubi.hom_ext (eq_of_heq h))

/-- A functor sends (heterogeneously) equal morphisms between equal objects to morphisms that are
isomorphisms together. -/
theorem isIso_map_iff_of_heq {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D) {M N M' N' : C}
    (f : M ⟶ N) (g : M' ⟶ N') (hM : M = M') (hN : N = N') (h : f ≍ g) :
    IsIso (Φ.map f) ↔ IsIso (Φ.map g) := by
  subst hM hN
  rw [eq_of_heq h]

/-- A map is bijective iff its conjugate by bijections is, when the square commutes. -/
private theorem bijective_iff_of_equiv_comp {α β γ δ E E' : Type*} [EquivLike E α γ]
    [EquivLike E' β δ] (a : E) (b : E') {f : α → β} {g : γ → δ} (h : ∀ x, b (f x) = g (a x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [← EquivLike.comp_bijective f b, ← EquivLike.bijective_comp a g]
  exact Iff.of_eq (congrArg _ (funext h))

variable {k : Type u} [Field k] {F : Type w} [Field F]

/-! ### Condition (2) of Lemma 0FI0 is invariant under isomorphism -/

namespace WeilData

/-- Isomorphic data (D0)–(D3) have bijective pullbacks `f^* : H^n(Y) → H^n(X)` at the same `f`
and `n`. -/
theorem Iso.bijective_pullDeg_iff {W W' : WeilData k F} (e : Iso W W')
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ) :
    Function.Bijective (W.pullDeg f n) ↔ Function.Bijective (W'.pullDeg f n) := by
  exact bijective_iff_of_equiv_comp (e.gradeEquiv Y n) (e.gradeEquiv X n)
    (e.gradeEquiv_pullDeg f n)

/-- **Condition (2) of Lemma 0FI0 is invariant under isomorphism of data (D0)–(D3).** -/
theorem IsIsomorphic.globalSectionsCondition_iff {W W' : WeilData k F} (h : W.IsIsomorphic W') :
    W.GlobalSectionsCondition ↔ W'.GlobalSectionsCondition := by
  obtain ⟨e, -, -⟩ := h
  exact forall_congr' fun X ↦ e.bijective_pullDeg_iff _ 0

end WeilData

/-! ### Isomorphism classes of Weil cohomology theories -/

namespace WeilCohomologyTheory

variable (k F) in
/-- **Isomorphism of Weil cohomology theories**, as a setoid: isomorphism of the underlying data
(D0)–(D3) (`Stacks.WeilCohomology.WeilData.IsIsomorphic`); the axioms are properties. -/
def isoSetoid : Setoid (WeilCohomologyTheory k F) :=
  (WeilDataAxioms.isoSetoid k F).comap toWeilDataAxioms

/-- Two Weil cohomology theories are related by `isoSetoid` exactly when their underlying data
(D0)–(D3) are isomorphic. -/
theorem isoSetoid_iff (T T' : WeilCohomologyTheory k F) :
    isoSetoid k F T T' ↔ T.toWeilData.IsIsomorphic T'.toWeilData :=
  Iff.rfl

variable (k F) in
/-- **A Weil cohomology theory is data (D0)–(D3) satisfying (A), (B), (C) and condition (2) of
Lemma 0FI0** (Definition 0FI2). -/
def equivWeilDataAxiomsSubtype :
    WeilCohomologyTheory k F ≃
      {W : WeilDataAxioms k F // W.toWeilData.GlobalSectionsCondition} where
  toFun T := ⟨T.toWeilDataAxioms, T.globalSections⟩
  invFun W := ofWeilDataAxioms W.1 W.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The data with axioms underlying the image of `T` under `equivWeilDataAxiomsSubtype` is
`T.toWeilDataAxioms`. -/
@[simp]
theorem equivWeilDataAxiomsSubtype_apply (T : WeilCohomologyTheory k F) :
    (equivWeilDataAxiomsSubtype k F T).1 = T.toWeilDataAxioms :=
  rfl

variable (k F) in
/-- Isomorphism classes of Weil cohomology theories are isomorphism classes of data satisfying
(A), (B), (C) and condition (2) of Lemma 0FI0. -/
def isoClassEquivWeilDataAxiomsSubtype :
    Quotient ((WeilDataAxioms.isoSetoid k F).comap
        (Subtype.val : {W : WeilDataAxioms k F // W.toWeilData.GlobalSectionsCondition} → _)) ≃
      Quotient (isoSetoid k F) :=
  Quotient.congr (equivWeilDataAxiomsSubtype k F).symm fun _ _ ↦ Iff.rfl

/-- `isoClassEquivWeilDataAxiomsSubtype` sends the class of `W` to the class of the Weil cohomology
theory `ofWeilDataAxioms W.1 W.2`. -/
@[simp]
theorem isoClassEquivWeilDataAxiomsSubtype_mk
    (W : {W : WeilDataAxioms k F // W.toWeilData.GlobalSectionsCondition}) :
    isoClassEquivWeilDataAxiomsSubtype k F (Quotient.mk _ W) =
      Quotient.mk _ (ofWeilDataAxioms W.1 W.2) :=
  rfl

end WeilCohomologyTheory

/-! ### Condition (2) on realizations -/

namespace WeilRealization

variable [CharZero F]

/-- **Condition (2) of Stacks 0GIJ**: for every smooth projective `X` over `k` with
`k' = Γ(X, 𝒪_X)`, the map `G(h(Spec k')) → G(h(X))` induced by `X ⟶ Spec(k')` is an
isomorphism in degree `0`. -/
def GlobalSections (G : WeilRealization k F) : Prop :=
  ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    IsIso ((G.functor.map ((ChowMotiveCat.h k).map
      (SmoothProjectiveScheme.toSpecGlobalSections X).op)) 0)

/-- **Condition (2) is invariant under isomorphism of realizations.** It only uses the
underlying natural isomorphism. -/
theorem globalSections_iff_of_iso {G G' : WeilRealization k F} (e : Iso G G') :
    G.GlobalSections ↔ G'.GlobalSections :=
  forall_congr' fun _ ↦
    NatIso.isIso_map_iff (Functor.isoWhiskerRight e.iso (GradedObject.eval (C := ModuleCat F) 0)) _

/-- If the realizations `G` and `G'` are isomorphic (related by `isoSetoid`), then condition (2)
holds for `G` if and only if it holds for `G'`. -/
theorem globalSections_iff_of_rel {G G' : WeilRealization k F} (h : isoSetoid k F G G') :
    G.GlobalSections ↔ G'.GlobalSections :=
  globalSections_iff_of_iso h.some

/-- **Restriction of a bijection of isomorphism classes to condition (2).** Let
`e : {realizations}/≅ ≃ {data satisfying (A), (B), (C)}/≅` send the class of `G` to the class of
`c G`, for a construction `c` such that `c G` satisfies condition (2) of Lemma 0FI0 exactly when
`G` satisfies condition (2) of Stacks 0GIJ. Then `e` restricts to a bijection between
isomorphism classes of realizations satisfying condition (2) and isomorphism classes of Weil
cohomology theories, sending the class of `G` to the class of `T` exactly when `c G` and the data
of `T` are isomorphic. -/
theorem exists_globalSections_isoClassEquiv_of
    (e : Quotient (isoSetoid k F) ≃ Quotient (WeilDataAxioms.isoSetoid k F))
    (c : WeilRealization k F → WeilDataAxioms k F)
    (hc : ∀ G, e (Quotient.mk _ G) = Quotient.mk _ (c G))
    (hcG : ∀ G, (c G).toWeilData.GlobalSectionsCondition ↔ G.GlobalSections) :
    ∃ e' : Quotient ((isoSetoid k F).comap
          (Subtype.val : {G : WeilRealization k F // G.GlobalSections} → _)) ≃
        Quotient (WeilCohomologyTheory.isoSetoid k F),
      ∀ (G : {G : WeilRealization k F // G.GlobalSections}) (T : WeilCohomologyTheory k F),
        e' (Quotient.mk _ G) = Quotient.mk _ T ↔
          (Quotient.mk (WeilDataAxioms.isoSetoid k F) (c G.1) =
            Quotient.mk _ T.toWeilDataAxioms) := by
  obtain ⟨e₁, he₁⟩ := exists_quotientEquiv_restrict e GlobalSections
    (fun W : WeilDataAxioms k F ↦ W.toWeilData.GlobalSectionsCondition) fun G W h ↦ by
      rw [hc] at h
      exact (hcG G).symm.trans (Quotient.exact h).globalSectionsCondition_iff
  refine ⟨e₁.trans (WeilCohomologyTheory.isoClassEquivWeilDataAxiomsSubtype k F), fun G T ↦ ?_⟩
  rw [Equiv.trans_apply, ← Equiv.eq_symm_apply]
  change e₁ _ = Quotient.mk _ (WeilCohomologyTheory.equivWeilDataAxiomsSubtype k F T) ↔ _
  rw [he₁, hc]
  rfl

/-! ### Condition (2) for the data of a realization -/

/-- **`G(h(f))` is an isomorphism in degree `0` exactly when `G(ChowMotiveCat.motMap f)` is.** The
data of a realization (Stacks 0FHK) are defined with `ChowMotiveCat.motMap f = [Γ_f]` between
the triples `(X, 1, 0)`, which are `h(X)` by definition; `h(f)` has the same underlying
correspondence `[Γ_f]`. -/
theorem isIso_map_h_map_iff (G : WeilRealization k F)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) :
    IsIso ((G.functor.map ((ChowMotiveCat.h k).map f.op)) 0) ↔
      IsIso ((G.functor.map (ChowMotiveCat.motMap f)) 0) :=
  isIso_map_iff_of_heq (G.functor ⋙ GradedObject.eval (C := ModuleCat F) 0) _ _ rfl rfl
    (TwistedKaroubi.heq_of_heq_val _ _ rfl rfl
      (heq_of_eq (by rw [ChowMotiveCat.motMap_val]; rfl)))

/-- **`H^0(Y) → H^0(X)` is `G(h(f))` in degree `0`** for the data (D0)–(D3) of a realization
(Stacks 0FHK, `H^*(X) = G(h(X))`): one is bijective exactly when the other is an isomorphism. -/
theorem bijective_pullDeg_zero_iff (G : WeilRealization k F)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) :
    Function.Bijective (G.toWeilDataAxioms.toWeilData.pullDeg f 0) ↔
      IsIso ((G.functor.map ((ChowMotiveCat.h k).map f.op)) 0) := by
  rw [isIso_map_h_map_iff, ConcreteCategory.isIso_iff_bijective]
  exact bijective_iff_of_equiv_comp ((G.cohAlg Y).gradeEquiv 0) ((G.cohAlg X).gradeEquiv 0)
    (G.gradeEquiv_pullDeg f 0)

/-- **The data of a realization satisfy condition (2) of Lemma 0FI0 exactly when the realization
satisfies condition (2) of Stacks 0GIJ**: `H^0(Spec k') → H^0(X)` is bijective for every `X` iff
`G(h(Spec k')) → G(h(X))` is an isomorphism in degree `0` for every `X`. -/
theorem toWeilDataAxioms_globalSectionsCondition_iff (G : WeilRealization k F) :
    G.toWeilDataAxioms.toWeilData.GlobalSectionsCondition ↔ G.GlobalSections :=
  forall_congr' fun _ ↦ G.bijective_pullDeg_zero_iff _

variable (k F) in
/-- **Stacks Project, Tag 0GIJ.** Let `k` be a field and `F` a field of characteristic `0`. A Weil
cohomology theory (Definition 0FI2) is the same thing as a `ℚ`-linear symmetric monoidal functor
`G : M_k ⥤ graded F-vector spaces` (`Stacks.WeilCohomology.WeilRealization`) such that

1. `G(𝟏(1))` is nonzero only in degree `-2`, and
2. for every smooth projective `X` over `k` with `k' = Γ(X, 𝒪_X)` the map
   `G(h(Spec k')) → G(h(X))` is an isomorphism in degree `0`
   (`Stacks.WeilCohomology.WeilRealization.GlobalSections`):

there is a bijection between isomorphism classes of such functors and isomorphism classes of
Weil cohomology theories, sending the class of `G` to the class of the Weil cohomology theory
`H^*(X) = G(h(X))` of Stacks 0FHK. -/
@[stacks 0GIJ "a Weil cohomology theory is the same thing as a Q-linear symmetric monoidal functor
G : M_k -> graded F-vector spaces with G(1(1)) nonzero only in degree -2 and
G(h(Spec k')) -> G(h(X)) an isomorphism in degree 0 for k' = Gamma(X, O_X): a bijection of
isomorphism classes, G corresponding to H^*(X) = G(h(X))"]
theorem exists_globalSections_isoClassEquiv :
    ∃ e : Quotient ((isoSetoid k F).comap
          (Subtype.val : {G : WeilRealization k F // G.GlobalSections} → _)) ≃
        Quotient (WeilCohomologyTheory.isoSetoid k F),
      ∀ (G : {G : WeilRealization k F // G.GlobalSections}) (T : WeilCohomologyTheory k F),
        e (Quotient.mk _ G) = Quotient.mk _ T ↔
          (Quotient.mk (WeilDataAxioms.isoSetoid k F) G.1.toWeilDataAxioms =
            Quotient.mk _ T.toWeilDataAxioms) := by
  obtain ⟨e, -, he⟩ := exists_isoClassEquiv k F
  exact exists_globalSections_isoClassEquiv_of e.symm toWeilDataAxioms he
    toWeilDataAxioms_globalSectionsCondition_iff

end WeilRealization

end Stacks.WeilCohomology

end
