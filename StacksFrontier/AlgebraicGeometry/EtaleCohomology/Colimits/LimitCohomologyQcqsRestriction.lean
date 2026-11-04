module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitQcqsMayerVietoris

/-!
# Restriction on étale cohomology along a limit of quasi-compact quasi-separated schemes

Let `I` be a directed set, `(X_i)` an inverse system of quasi-compact and quasi-separated schemes
over `I` with affine transition morphisms and limit `X`, `i₀ ∈ I` and `G` an abelian sheaf on
`X_{i₀}`. Every class of `H^q(X, f_{i₀}⁻¹G)` comes from some `X_i`, and a class on `X_{i₀}` that
vanishes on `X` already vanishes on some `X_i`.

## Main results

* `exists_le_restriction_eq_zero_of_qcqs`: a class on `X_{i₀}` that restricts to zero on `X`
  restricts to zero on some `X_i`, `i ≥ i₀`.
* `exists_le_restriction_eq_of_qcqs`: every class of `H^q(X, f_{i₀}⁻¹G)` comes from some
  `H^q(X_i, f_{ii₀}⁻¹G)`, `i ≥ i₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section Bot

variable {J : Type u} [Preorder J] [OrderBot J] [IsDirected J (· ≤ ·)]
  {E : Jᵒᵖ ⥤ Scheme.{u}} {c : Cone E}

/-- For morphisms `a : Y ⟶ X`, `b : Z ⟶ Y` and `ba = b ≫ a`, a class `ξ ∈ H^q(X, G)` restricts
to zero along `a` and then `b` if and only if it restricts to zero along `ba`. -/
theorem restriction_restriction_eq_zero_iff {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (ba : Z ⟶ X) (hba : ba = b ≫ a) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (ξ : Sheaf.H.{u + 1} G q) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} b _ q
        (etaleCohomologyRestrictionMap.{u, 0, u + 1} a G q ξ) = 0 ↔
      etaleCohomologyRestrictionMap.{u, 0, u + 1} ba G q ξ = 0 := by
  rw [LimitSiteBridge.etaleCohomologyRestrictionMap_restrict a b ba hba]
  exact Stacks.ExtTransport.comp_mk₀_eq_zero_iff (Iso.app (K b a ba hba) G) _

/-- Injectivity from the least stage, for a system whose theory on `ℤ` is good. -/
theorem exists_restriction_eq_zero_of_goodZ (h : GoodZ E c)
    (G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H.{u + 1} G q)
    (hξ : etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op ⊥)) G q ξ = 0) :
    ∃ i : J, etaleCohomologyRestrictionMap.{u, 0, u + 1} (toBot E i) G q ξ = 0 := by
  obtain ⟨x, hx⟩ := (toH_bijective (toBot E ⊥) G q).2
    (etaleCohomologyRestrictionMap.{u, 0, u + 1} (toBot E ⊥) G q ξ)
  have h0 : resK (c.π.app (op ⊥)) (toBot E ⊥) (c.π.app (op ⊥)) (cone_toBot E c ⊥) (zSheaf _) G q
      x = 0 := by
    rw [toH_resK_eq_zero_iff, hx, restriction_restriction_eq_zero_iff _ _ _ (cone_toBot E c ⊥)]
    exact hξ
  obtain ⟨i, _, hi⟩ := ((h G q).2 ⊥ x h0)
  refine ⟨i, ?_⟩
  have := (toH_resK_eq_zero_iff (trans E bot_le) (toBot E ⊥) (toBot E i) (toBot_eq E bot_le) G q
    x).1 hi
  rwa [hx, restriction_restriction_eq_zero_iff _ _ _ (toBot_eq E (bot_le : ⊥ ≤ i))] at this

/-- Surjectivity from the least stage, for a system whose theory on `ℤ` is good. -/
theorem exists_restriction_eq_of_goodZ (h : GoodZ E c)
    (G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (c.π.app (op ⊥))).obj G) q) :
    ∃ (i : J) (y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (toBot E i)).obj G) q),
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i)) _ q y).comp
        (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0} (c.π.app (op i)) (toBot E i)
          (c.π.app (op ⊥)) (cone_toBot E c i)).inv.app G)) (add_zero q) = x := by
  obtain ⟨z, rfl⟩ := (toH_bijective (c.π.app (op ⊥)) G q).2 x
  obtain ⟨i, w, hw⟩ := (h G q).1 z
  exact ⟨i, toH (toBot E i) G q w, (toH_resK (c.π.app (op i)) (toBot E i) (c.π.app (op ⊥))
    (cone_toBot E c i) G q w).symm.trans (congrArg (toH (c.π.app (op ⊥)) G q) hw)⟩

end Bot

section Reindex

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- `{i ∈ I | i₀ ≤ i}` has a least element. -/
@[reducible]
def geIndexBot (i₀ : I) : OrderBot {i : I // i₀ ≤ i} :=
  { bot := ⟨i₀, le_rfl⟩, bot_le := fun a => a.2 }

/-- `{i ∈ I | i₀ ≤ i}` is directed. -/
instance geIndex_isDirected (i₀ : I) : IsDirected {i : I // i₀ ≤ i} (· ≤ ·) := ⟨fun a b => by
  obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
  exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩

/-- The inclusion of `{i ∈ I | i₀ ≤ i}`. -/
abbrev geIncl (i₀ : I) : {i : I // i₀ ≤ i} ⥤ I := (Subtype.mono_coe (fun i : I => i₀ ≤ i)).functor

/-- The inclusion of `{i ∈ I | i₀ ≤ i}` into the directed set `I` is final. -/
instance geIncl_final (i₀ : I) : (geIncl i₀).Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun a => ?_) (fun {d c} f g => ?_)
  · obtain ⟨b, hab, hb⟩ := directed_of (· ≤ ·) a i₀
    exact ⟨⟨b, hb⟩, ⟨homOfLE hab⟩⟩
  · exact ⟨c, 𝟙 _, Subsingleton.elim _ _⟩

/-- For a limit cone `c` over an inverse system `D` with affine transition morphisms and
`D(i₀)` quasi-compact and quasi-separated, the restriction of `D` and `c` to `{i ∈ I | i₀ ≤ i}`
satisfies `GoodZ`. -/
theorem goodZ_reindex (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))] :
    letI := geIndexBot i₀
    GoodZ ((geIncl i₀).op ⋙ D) (c.whisker (geIncl i₀).op) := by
  let := geIndexBot i₀
  have : Nonempty I := ⟨i₀⟩
  have : ∀ {i j : {i : I // i₀ ≤ i}ᵒᵖ} (a : i ⟶ j), IsAffineHom (((geIncl i₀).op ⋙ D).map a) :=
    fun a => inferInstanceAs (IsAffineHom (D.map _))
  have : CompactSpace ((((geIncl i₀).op ⋙ D)).obj (op ⊥)) :=
    inferInstanceAs (CompactSpace (D.obj (op i₀)))
  have : QuasiSeparatedSpace ((((geIncl i₀).op ⋙ D)).obj (op ⊥)) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (op i₀)))
  exact goodZ_of_qcqs ((Functor.Initial.isLimitWhiskerEquiv (geIncl i₀).op c).symm hc)

end Reindex

/-- **Stacks 09YQ, injectivity, for quasi-compact and quasi-separated levels.** Let `I` be a
directed set, `(X_i)` an inverse system of schemes over `I` with affine transition morphisms and
limit `X`, `i₀ ∈ I` with `X_{i₀}` quasi-compact and quasi-separated, `G` an abelian sheaf on
`X_{i₀}` and `ξ ∈ H^q(X_{i₀}, G)`. If `ξ` restricts to zero on `X`, it restricts to zero on some
`X_i` with `i ≥ i₀`. -/
theorem exists_le_restriction_eq_zero_of_qcqs {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (ξ : Sheaf.H.{u + 1} G q)
    (hξ : etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i₀)) G q ξ = 0) :
    ∃ (i : I) (h : i₀ ≤ i),
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (D.map (homOfLE h).op) G q ξ = 0 := by
  let := geIndexBot i₀
  obtain ⟨i, hi⟩ := exists_restriction_eq_zero_of_goodZ (goodZ_reindex D c hc i₀) G q ξ hξ
  exact ⟨i.1, i.2, hi⟩

/-- **Stacks 09YQ, surjectivity, for quasi-compact and quasi-separated levels.** Let `I` be a
directed set, `(X_i)` an inverse system of schemes over `I` with affine transition morphisms and
limit `X`, `i₀ ∈ I` with `X_{i₀}` quasi-compact and quasi-separated, and `G` an abelian sheaf on
`X_{i₀}`. Every class of `H^q(X, f_{i₀}⁻¹G)` is the restriction of a class of
`H^q(X_i, f_{ii₀}⁻¹G)` for some `i ≥ i₀`, read through the canonical comparison
`f_i⁻¹f_{ii₀}⁻¹G ≅ f_{i₀}⁻¹G`. -/
theorem exists_le_restriction_eq_of_qcqs {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (c.π.app (op i₀))).obj G) q) :
    ∃ (i : I) (h : i₀ ≤ i)
      (y : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (D.map (homOfLE h).op)).obj G) q),
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i)) _ q y).comp
        (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0} (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).inv.app G))
        (add_zero q) = x := by
  let := geIndexBot i₀
  obtain ⟨i, y, hy⟩ := exists_restriction_eq_of_goodZ (goodZ_reindex D c hc i₀) G q x
  exact ⟨i.1, i.2, y, hy⟩

end Stacks.EtaleCohomology.LimitExt
