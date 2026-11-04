module

public import StacksFrontier.CategoryTheory.Adjunction.PushedForwardTwistedBaseChange

/-!
# The base change map of right adjoints against units and counits

In the situation of `StacksFrontier/CategoryTheory/Adjunction/PushedForwardTwistedBaseChange.lean`
— a square of categories whose four "pullbacks" `Lf, Lf', Lg, Lg'` have right adjoints
`Rf, Rf', Rg, Rg'`, whose two "pushforwards" `Rf, Rf'` have right adjoints `a, a'`, and in which
the mate `ξ : a' ⋙ Rg' ⟶ Rg ⋙ a` of the comparison of the composite pushforwards is invertible —
the base change map `β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` of pushforward along pullback and the base change
map `α : a ⋙ Lg' ⟶ Lg ⋙ a'` of the right adjoints are compatible with the counits ("trace maps")
and with the units of `Rf ⊣ a` and `Rf' ⊣ a'`:

* `Lg(Tr_K) = Tr'_{Lg K} ∘ Rf'(α_K) ∘ β_{a K}`, the categorical content of [Stacks, Tag 0B6J];
* `a'(β_M) ∘ α_{Rf M} ∘ Lg'(η_M) = η'_{Lg' M}`, the categorical content of [Stacks, Tag 0B6K].

Only the invertibility of `ξ` is used, never that of `β`: the proofs are the source's, with the
isomorphism `β^∨` of the source replaced by `ξ` and the pentagon of [Stacks, Tag 0B65] replaced by
the defining property of `ξ` as the conjugate of `β` (`rightAdjointSquare_natTrans_eq`).

## Main results

* `Stacks.CategoryTheory.BaseChange.mateEquiv_symm_app_leftAdjointUniq` — the inverse mate of a
  square of right adjoints changes by conjugation with `Adjunction.leftAdjointUniq` when the left
  adjoints are replaced by other left adjoints of the same functors.

* `Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange_app_eq` — `α_K` through the unit of
  `Lg ⊣ Rg`, `ξ⁻¹` and the counit of `Lg' ⊣ Rg'`.
* `Stacks.CategoryTheory.BaseChange.map_counit_eq_twoSquare_comp_map_rightAdjointBaseChange` —
  the trace maps agree via `α` and `β`.
* `Stacks.CategoryTheory.BaseChange.map_unit_comp_rightAdjointBaseChange_comp_map_twoSquare` —
  the units agree via `α` and `β`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

/-- **The inverse mate under other choices of left adjoints.** For `x : R₁ ⋙ G ⟶ H ⋙ R₂` and two
pairs of left adjoints `L₁, L₁'` of `R₁` and `L₂, L₂'` of `R₂`, the inverse mate for the primed
adjunctions is the inverse mate for the unprimed ones, conjugated by the comparisons
`Adjunction.leftAdjointUniq` of the left adjoints. -/
theorem mateEquiv_symm_app_leftAdjointUniq {C D E F : Type*} [Category C] [Category D]
    [Category E] [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₂' : L₂' ⊣ R₂) (x : TwoSquare R₁ H G R₂) (K : C) :
    ((mateEquiv adj₁' adj₂').symm x).natTrans.app K =
      (Adjunction.leftAdjointUniq adj₂' adj₂).hom.app (G.obj K) ≫
        ((mateEquiv adj₁ adj₂).symm x).natTrans.app K ≫
          H.map ((Adjunction.leftAdjointUniq adj₁ adj₁').hom.app K) := by
  have e : ∀ {L₁ : C ⥤ D} {L₂ : E ⥤ F} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (K : C),
      ((mateEquiv adj₁ adj₂).symm x).natTrans.app K =
      L₂.map (G.map (adj₁.unit.app K)) ≫ L₂.map (x.natTrans.app (L₁.obj K)) ≫
        adj₂.counit.app (H.obj (L₁.obj K)) := fun _ _ K => by simp [mateEquiv]
  set u := Adjunction.leftAdjointUniq adj₁ adj₁'
  set u' := Adjunction.leftAdjointUniq adj₂' adj₂
  have n₁ : ∀ {P Q : E} (φ : P ⟶ Q), u'.hom.app P ≫ L₂.map φ = L₂'.map φ ≫ u'.hom.app Q :=
    fun φ => (u'.hom.naturality φ).symm
  have n₂ : x.natTrans.app (L₁.obj K) ≫ R₂.map (H.map (u.hom.app K)) =
      G.map (R₁.map (u.hom.app K)) ≫ x.natTrans.app (L₁'.obj K) :=
    (x.natTrans.naturality (u.hom.app K)).symm
  have n₃ : L₂'.map (R₂.map (H.map (u.hom.app K))) ≫ adj₂'.counit.app (H.obj (L₁'.obj K)) =
      adj₂'.counit.app (H.obj (L₁.obj K)) ≫ H.map (u.hom.app K) :=
    adj₂'.counit.naturality _
  have hu : adj₁.unit.app K ≫ R₁.map (u.hom.app K) = adj₁'.unit.app K :=
    Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₁' K
  have hc : u'.hom.app (R₂.obj (H.obj (L₁.obj K))) ≫ adj₂.counit.app (H.obj (L₁.obj K)) =
      adj₂'.counit.app (H.obj (L₁.obj K)) :=
    Adjunction.leftAdjointUniq_hom_app_counit adj₂' adj₂ _
  rw [e, e]
  simp only [Category.assoc]
  rw [reassoc_of% (n₁ _), reassoc_of% (n₁ _)]
  simp only [Functor.comp_obj]
  rw [reassoc_of% hc, ← n₃, ← L₂'.map_comp_assoc,
    ← L₂'.map_comp_assoc, ← L₂'.map_comp_assoc, Category.assoc, n₂, ← G.map_comp_assoc, hu]

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Rg : S' ⥤ S} {Lg' : T ⥤ T'} {Rg' : T' ⥤ T} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  {a : S ⥤ T} {a' : S' ⥤ T'} (adja : Rf ⊣ a) (adja' : Rf' ⊣ a')
  [IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans]

omit [IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans] in
/-- The conjugate identity of `ξ` and `β` on counits: `β` at `Rg'(a' N)` followed by the counit
of `Lg' ⋙ Rf' ⊣ a' ⋙ Rg'` is `Lg(Rf(ξ_N))` followed by the counit of `Rf ⋙ Lg ⊣ Rg ⋙ a`. -/
private lemma twoSquare_app_comp_counit_aux (N : S') :
    (twoSquare adjf adjf' eg ef).natTrans.app (Rg'.obj (a'.obj N)) ≫
        Rf'.map (adjg'.counit.app (a'.obj N)) ≫ adja'.counit.app N =
      Lg.map (Rf.map
          ((rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans.app N)) ≫
        Lg.map (adja.counit.app (Rg.obj N)) ≫ adjg.counit.app N := by
  have h := conjugateEquiv_counit (adjg'.comp adja') (adja.comp adjg)
    (twoSquare adjf adjf' eg ef).natTrans N
  rw [← rightAdjointSquare_natTrans_eq] at h
  simpa only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] using h.symm

/-- **The base change map of right adjoints at an object**: `α_K` is `Lg'` of `a` of the unit of
`Lg ⊣ Rg` at `K`, then `Lg'` of `ξ⁻¹` at `Lg K`, then the counit of `Lg' ⊣ Rg'`. -/
theorem rightAdjointBaseChange_app_eq (K : S) :
    (rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').natTrans.app K =
      Lg'.map (a.map (adjg.unit.app K)) ≫
        Lg'.map ((inv (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans).app
          (Lg.obj K)) ≫
        adjg'.counit.app (a'.obj (Lg.obj K)) := by
  set α := rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja'
  set ξ := rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja'
  have h₁ : Lg'.map ((inv ξ.natTrans).app (Lg.obj K)) ≫ adjg'.counit.app (a'.obj (Lg.obj K)) =
      α.natTrans.app (Rg.obj (Lg.obj K)) ≫ a'.map (adjg.counit.app (Lg.obj K)) :=
    mateEquiv_counit_symm adjg adjg' (TwoSquare.mk _ _ _ _ (inv ξ.natTrans)) (Lg.obj K)
  have h₂ : Lg'.map (a.map (adjg.unit.app K)) ≫ α.natTrans.app (Rg.obj (Lg.obj K)) =
      α.natTrans.app K ≫ a'.map (Lg.map (adjg.unit.app K)) :=
    α.natTrans.naturality (adjg.unit.app K)
  rw [h₁, reassoc_of% h₂, ← a'.map_comp, adjg.left_triangle_components, a'.map_id,
    Category.comp_id]

/-- **[Stacks, Tag 0B6J] over abstract adjunctions: the trace maps agree via the base change
maps.** `Lg` of the counit of `Rf ⊣ a` at `K` is the base change map `β` at `a K`, followed by
`Rf'` of the base change map `α` at `K` and the counit of `Rf' ⊣ a'` at `Lg K`. -/
theorem map_counit_eq_twoSquare_comp_map_rightAdjointBaseChange (K : S) :
    Lg.map (adja.counit.app K) =
      (twoSquare adjf adjf' eg ef).natTrans.app (a.obj K) ≫
        Rf'.map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').natTrans.app K) ≫
          adja'.counit.app (Lg.obj K) := by
  set ξ := rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja'
  set β := twoSquare adjf adjf' eg ef
  set N := Lg.obj K
  rw [rightAdjointBaseChange_app_eq, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have n₁ : Lg.map (Rf.map (a.map (adjg.unit.app K))) ≫ β.natTrans.app (a.obj (Rg.obj N)) =
      β.natTrans.app (a.obj K) ≫ Rf'.map (Lg'.map (a.map (adjg.unit.app K))) :=
    β.natTrans.naturality _
  have n₂ : Lg.map (Rf.map ((inv ξ.natTrans).app N)) ≫ β.natTrans.app (Rg'.obj (a'.obj N)) =
      β.natTrans.app (a.obj (Rg.obj N)) ≫ Rf'.map (Lg'.map ((inv ξ.natTrans).app N)) :=
    β.natTrans.naturality _
  have hinv : Lg.map (Rf.map ((inv ξ.natTrans).app N)) ≫ Lg.map (Rf.map (ξ.natTrans.app N)) =
      𝟙 _ := by
    rw [← Lg.map_comp, ← Rf.map_comp, ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app,
      Rf.map_id, Lg.map_id]
  have n₃ : Lg.map (Rf.map (a.map (adjg.unit.app K))) ≫ Lg.map (adja.counit.app (Rg.obj N)) =
      Lg.map (adja.counit.app K) ≫ Lg.map (adjg.unit.app K) := by
    rw [← Lg.map_comp, ← Lg.map_comp]
    exact congrArg Lg.map (adja.counit.naturality (adjg.unit.app K))
  rw [← reassoc_of% n₁, ← reassoc_of% n₂,
    twoSquare_app_comp_counit_aux adjf adjf' adjg adjg' eg ef adja adja' N, reassoc_of% hinv,
    reassoc_of% n₃, adjg.left_triangle_components, Category.comp_id]

/-- **[Stacks, Tag 0B6K] over abstract adjunctions: the units agree via the base change maps.**
`Lg'` of the unit of `Rf ⊣ a` at `M`, followed by the base change map `α` at `Rf M` and `a'` of
the base change map `β` at `M`, is the unit of `Rf' ⊣ a'` at `Lg' M`. -/
theorem map_unit_comp_rightAdjointBaseChange_comp_map_twoSquare (M : T) :
    Lg'.map (adja.unit.app M) ≫
        (rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').natTrans.app (Rf.obj M) ≫
          a'.map ((twoSquare adjf adjf' eg ef).natTrans.app M) =
      adja'.unit.app (Lg'.obj M) := by
  set ξ := rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja'
  set β := twoSquare adjf adjf' eg ef
  rw [rightAdjointBaseChange_app_eq]
  have n₁ : Lg'.map (Rg'.map (a'.map (β.natTrans.app M))) ≫
      adjg'.counit.app (a'.obj (Rf'.obj (Lg'.obj M))) =
      adjg'.counit.app (a'.obj (Lg.obj (Rf.obj M))) ≫ a'.map (β.natTrans.app M) :=
    adjg'.counit.naturality _
  have n₂ : a.map (Rg.map (β.natTrans.app M)) ≫ (inv ξ.natTrans).app (Rf'.obj (Lg'.obj M)) =
      (inv ξ.natTrans).app (Lg.obj (Rf.obj M)) ≫ Rg'.map (a'.map (β.natTrans.app M)) :=
    (inv ξ.natTrans).naturality (β.natTrans.app M)
  have hu : adjg'.unit.app M ≫ Rg'.map (adja'.unit.app (Lg'.obj M)) ≫
      ξ.natTrans.app (Rf'.obj (Lg'.obj M)) =
      adja.unit.app M ≫ a.map (adjg.unit.app (Rf.obj M)) ≫ a.map (Rg.map (β.natTrans.app M)) := by
    have h := unit_conjugateEquiv (adjg'.comp adja') (adja.comp adjg) β.natTrans M
    rw [← rightAdjointSquare_natTrans_eq] at h
    simpa only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
      Category.assoc] using h
  have key : adja.unit.app M ≫ a.map (adjg.unit.app (Rf.obj M)) ≫
      a.map (Rg.map (β.natTrans.app M)) ≫ (inv ξ.natTrans).app (Rf'.obj (Lg'.obj M)) =
      adjg'.unit.app M ≫ Rg'.map (adja'.unit.app (Lg'.obj M)) := by
    rw [← reassoc_of% hu, ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
    simp
  have n₃ : Lg'.map (Rg'.map (adja'.unit.app (Lg'.obj M))) ≫
      adjg'.counit.app (a'.obj (Rf'.obj (Lg'.obj M))) =
      adjg'.counit.app (Lg'.obj M) ≫ adja'.unit.app (Lg'.obj M) :=
    adjg'.counit.naturality _
  calc Lg'.map (adja.unit.app M) ≫ (Lg'.map (a.map (adjg.unit.app (Rf.obj M))) ≫
          Lg'.map ((inv ξ.natTrans).app (Lg.obj (Rf.obj M))) ≫
            adjg'.counit.app (a'.obj (Lg.obj (Rf.obj M)))) ≫ a'.map (β.natTrans.app M)
      = Lg'.map (adja.unit.app M ≫ a.map (adjg.unit.app (Rf.obj M)) ≫
          (inv ξ.natTrans).app (Lg.obj (Rf.obj M)) ≫ Rg'.map (a'.map (β.natTrans.app M))) ≫
            adjg'.counit.app (a'.obj (Rf'.obj (Lg'.obj M))) := by
        simp only [Functor.map_comp, Category.assoc]
        rw [n₁]
    _ = adja'.unit.app (Lg'.obj M) := by
        rw [← n₂, key, Lg'.map_comp_assoc, n₃]
        exact adjg'.left_triangle_components_assoc M _

end Stacks.CategoryTheory.BaseChange

end
