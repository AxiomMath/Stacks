module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.QuasiFiniteAdjoinField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.QuasiFiniteLevelSchemes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ResidueFieldIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.StrictHenselizationField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg

/-!
# The strict henselization at a point of positive transcendence degree as a limit of schemes of
smaller dimension

Let `X` be a scheme locally of finite type over a field `K`, let `s` be a geometric point of `X`
over a point `x` with `trdeg_K κ(x) > 0`, and let `X' = Spec(𝒪^{sh}_{X,s})` be the strict
henselization. The proof of [Stacks, Tag 0F1H] uses that, by [Stacks, Tag 0F0U], there is a
separably closed field `L ⊇ K` such that `X' = lim X_i` with `X_i` affine of finite type over `L`
and `dim(X_i) < dim(X)`. This file proves that statement, with the `X_i` mapping compatibly to
`X`, the index a directed set in the universe of the schemes, and affine transition morphisms —
the form in which [Stacks, Tag 0EZT] consumes it.

## The proof

The presentation is the one of the proof of [Stacks, Tag 0F0X]. Choose an affine open `V ∋ x`.
The strict henselization contains a separable closure `L` of `K(t_1, …, t_a)`, `a = trdeg_K κ(x)`
(`AlgebraicGeometry.exists_sepClosed_field_strictHenselization`, [Stacks, Tag 0F0U]), and is the
filtered union of the finite type `L`-algebras `B_D = Γ(V)[D ∪ L]`, `D` running over the finitely
generated quasi-finite `Γ(V)`-subalgebras (`AlgebraicGeometry.isLimitLevelLimitCone`). The
residue field extensions of `Spec(B_D) ⟶ V` are algebraic
(`AlgebraicGeometry.isIntegral_residueFieldMap_levelSystem`), so a point `z` of `Spec(B_D)` over
`x' ∈ V` has `trdeg_K L + trdeg_L κ(z) ≤ trdeg_K κ(z) = trdeg_K κ(x') ≤ dim(X)`. Since
`trdeg_K L ≥ a ≥ 1`, every residue field of `Spec(B_D)` has transcendence degree over `L` less
than `dim(X)`, and so does `dim(Spec(B_D))`, which by [Stacks, Tag 0A21] is the largest of these
at the finitely many generic points.

This is a different presentation from the one of the proof of [Stacks, Tag 0F0U] (which tensors
étale algebras over `K[t_1, …, t_a]` with `K(t_1, …, t_a)^{sep}`); what [Stacks, Tag 0F1H] uses
is only the existence of some such presentation.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_lt_of_isIntegral_residueFieldMap` — the dimension bound:
  a quasi-compact scheme `Z` locally of finite type over a field `L ⊇ K` with `trdeg_K L > 0`,
  mapping to `X` over `K` with algebraic residue field extensions, has `dim(Z) < dim(X)`.
* `AlgebraicGeometry.exists_isLimit_strictHenselization_of_topologicalKrullDim_lt` — the
  presentation of the strict henselization.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F0U](https://stacks.math.columbia.edu/tag/0F0U)
* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

universe u

namespace AlgebraicGeometry

/-- **A residue field of a scheme over `L` has transcendence degree over `L` less than `dim(X)`.**
Let `L ⊇ K` be fields with `trdeg_K L > 0`, `X` locally of finite type over `K`, and `π : Z ⟶ X`
a morphism over `K` from a scheme `Z` over `L` whose residue field extensions are algebraic.
Then `trdeg_L κ(z) < dim(X)` for every `z ∈ Z`: in the tower `K ⊆ L ⊆ κ(z)` one has
`trdeg_K L + trdeg_L κ(z) ≤ trdeg_K κ(z) ≤ trdeg_K κ(π z) ≤ dim(X)`, the last two numbers being
finite. -/
theorem toENat_trdeg_residueField_lt_of_isIntegral (K L : Type u) [Field K] [Field L]
    [Algebra K L] {X Z : Scheme.{u}} (gX : X ⟶ Spec (.of K)) [LocallyOfFiniteType gX]
    (gZ : Z ⟶ Spec (.of L)) (π : Z ⟶ X)
    (hgZ : gZ ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = π ≫ gX)
    (hint : ∀ z, (π.residueFieldMap z).hom.IsIntegral) (hL : 0 < Algebra.trdeg K L) (z : Z) :
    letI : Algebra L (Z.residueField z) :=
      ((Scheme.ΓSpecIso (.of L)).inv ≫ gZ.appTop ≫ Z.Γevaluation z).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg L (Z.residueField z)) : WithBot ℕ∞) <
      topologicalKrullDim X := by
  let : Algebra L (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ gZ.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  let : Algebra K (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (π ≫ gX).appTop ≫ Z.Γevaluation z).hom.toAlgebra
  let : Algebra K (X.residueField (π z)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (π z)).hom.toAlgebra
  have : IsScalarTower K L (Z.residueField z) := by
    apply IsScalarTower.of_algebraMap_eq'
    show ((Scheme.ΓSpecIso (.of K)).inv ≫ (π ≫ gX).appTop ≫ Z.Γevaluation z).hom = _
    rw [← hgZ, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hX := toENat_trdeg_residueField_le_topologicalKrullDim K X gX (π z)
  have : FinTrdeg K (X.residueField (π z)) := residueField_finTrdeg K gX (π z)
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 (trdeg_lt_aleph0 K (X.residueField (π z)))
  have hc : 1 + Algebra.trdeg L (Z.residueField z) ≤ m :=
    (add_le_add_left (Cardinal.one_le_iff_pos.2 hL) _).trans
      ((trdeg_add_le (R := K) (S := L) (A := Z.residueField z)).trans
        ((trdeg_residueField_le_of_isIntegral K gX π z (hint z)).trans hm.le))
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1
    ((le_add_self.trans hc).trans_lt (Cardinal.natCast_lt_aleph0 (n := m)))
  rw [ht] at hc ⊢
  rw [hm] at hX
  have htm : t < m := by
    have : ((1 + t : ℕ) : Cardinal.{u}) ≤ m := by exact_mod_cast hc
    have := Nat.cast_le.1 this
    omega
  simp only [Cardinal.toENat_nat] at hX ⊢
  exact lt_of_lt_of_le (by exact_mod_cast htm) hX

/-- **The dimension bound of the proof of [Stacks, Tag 0F1H].** Let `L ⊇ K` be fields with
`trdeg_K L > 0`, `X` a nonempty scheme locally of finite type over `K`, and `Z` a quasi-compact
scheme locally of finite type over `L` with a morphism `π : Z ⟶ X` over `K` whose residue field
extensions are algebraic. Then `dim(Z) < dim(X)`.

By [Stacks, Tag 0A21] `dim(Z)` is the largest transcendence degree over `L` of a residue field at
one of the finitely many generic points of `Z`, and each of these is less than `dim(X)` by
`AlgebraicGeometry.toENat_trdeg_residueField_lt_of_isIntegral`. -/
theorem topologicalKrullDim_lt_of_isIntegral_residueFieldMap (K L : Type u) [Field K] [Field L]
    [Algebra K L] {X Z : Scheme.{u}} [Nonempty X] [CompactSpace Z] (gX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType gX] (gZ : Z ⟶ Spec (.of L)) [LocallyOfFiniteType gZ] (π : Z ⟶ X)
    (hgZ : gZ ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = π ≫ gX)
    (hint : ∀ z, (π.residueFieldMap z).hom.IsIntegral) (hL : 0 < Algebra.trdeg K L) :
    topologicalKrullDim Z < topologicalKrullDim X := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian gZ
  have : IsNoetherian Z := {}
  have : Finite (genericPoints Z) :=
    (genericPoints.finite
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Z))).to_subtype
  rw [topologicalKrullDim_eq_iSup_trdeg_residueField L Z gZ]
  rcases isEmpty_or_nonempty (genericPoints Z) with hE | hNE
  · rw [iSup_of_empty]
    obtain ⟨x⟩ := ‹Nonempty X›
    exact lt_of_lt_of_le (WithBot.bot_lt_coe _)
      (toENat_trdeg_residueField_le_topologicalKrullDim K X gX x)
  · obtain ⟨z₀, hz₀⟩ := exists_eq_ciSup_of_finite (ι := genericPoints Z)
      (f := fun z : genericPoints Z =>
        let : Algebra L (Z.residueField z.1) :=
          ((Scheme.ΓSpecIso (.of L)).inv ≫ gZ.appTop ≫ Z.Γevaluation z.1).hom.toAlgebra
        (Cardinal.toENat (Algebra.trdeg L (Z.residueField z.1)) : WithBot ℕ∞))
    rw [← hz₀]
    exact toENat_trdeg_residueField_lt_of_isIntegral K L gX gZ π hgZ hint hL z₀.1

variable (B : BigEtaleSite.{u})

/-- **The strict henselization at a point of positive transcendence degree is a limit of affine
schemes of finite type over a separably closed field, of smaller dimension** (the use of
[Stacks, Tag 0F0U] in the proof of [Stacks, Tag 0F1H]).

Let `X` be a scheme locally of finite type over a field `K` (structure morphism `gX`) and `s` a
geometric point of `X` over a point `x` with `trdeg_K κ(x) > 0`. Then there are a separably
closed field `L ⊇ K`, a directed nonempty index `I : Type u`, an inverse system `D` of schemes
over `I` with morphisms `π_i : D_i ⟶ X` and `D_i ⟶ Spec L`, and a limit cone with vertex the
strict henselization `X' = Spec(𝒪^{sh}_{X,s})`, such that

* every leg followed by `π_i` is the canonical morphism `X' ⟶ X`;
* every `D_i` is affine, and every transition morphism is affine;
* every `D_i` is locally of finite type over `L`, and `D_i ⟶ Spec L ⟶ Spec K` is
  `D_i ⟶ X ⟶ Spec K`;
* `dim(D_i) < dim(X)`. -/
theorem exists_isLimit_strictHenselization_of_topologicalKrullDim_lt {K : Type u} [Field K]
    {X : Scheme.{u}} (hS : B.Contains X) (gX : X ⟶ Spec (.of K)) [LocallyOfFiniteType gX]
    (s : GeometricPoint X)
    (ha : letI : Algebra K (X.residueField (s.hom (closedPoint s.residueField))) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫
          X.Γevaluation (s.hom (closedPoint s.residueField))).hom.toAlgebra
      0 < Algebra.trdeg K (X.residueField (s.hom (closedPoint s.residueField)))) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (_ : Algebra K L)
      (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ Scheme.{u}) (π : D ⟶ (Functor.const Iᵒᵖ).obj X)
      (gL : D ⟶ (Functor.const Iᵒᵖ).obj (Spec (.of L)))
      (p : (Functor.const Iᵒᵖ).obj (strictHenselization B X hS s) ⟶ D),
      Nonempty (IsLimit (Cone.mk _ p)) ∧
      (∀ i, p.app i ≫ π.app i = strictHenselizationToBase B X hS s) ∧
      (∀ i, IsAffine (D.obj i)) ∧
      (∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j), IsAffineHom (D.map a)) ∧
      (∀ i, LocallyOfFiniteType (gL.app i)) ∧
      (∀ i, gL.app i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = π.app i ≫ gX) ∧
      (∀ i, topologicalKrullDim (D.obj i) < topologicalKrullDim X) := by
  classical
  set y := s.hom (closedPoint s.residueField)
  -- an affine open around `y`, the map from the strict henselization, and the field `L`
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  set V : X.Opens := V₀
  obtain ⟨l, hl, hind⟩ := exists_lift_ind_etale_appTop_strictHenselizationToBase B hS s V hV hyV
  obtain ⟨L, _, _, _, ψ, T₀, hT₀, hψK, hbL, hL⟩ :=
    exists_sepClosed_field_strictHenselization B hS s gX
  have : IsAffine V.toScheme := hV
  let Tsch : Scheme.{u} := V.toScheme
  let O := ↥(etaleLocalRing B X hS s)
  let φR : Γ(Tsch, ⊤) ⟶ CommRingCat.of O := l.appTop ≫ (Scheme.ΓSpecIso _).hom
  let : Algebra Γ(Tsch, ⊤) O := φR.hom.toAlgebra
  -- `O` is covered by finitely generated quasi-finite subalgebras
  have hcov := exists_fg_quasiFinite_mem_of_ind_etale φR
    ((MorphismProperty.cancel_right_of_respectsIso _ _ _).2 hind)
  -- the `K`-structures
  let gT : Tsch ⟶ Spec (.of K) := V.ι ≫ gX
  let : Algebra K Γ(Tsch, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom.toAlgebra
  have hKO : ∀ k : K,
      ψ (algebraMap K L k) = algebraMap Γ(Tsch, ⊤) O (algebraMap K Γ(Tsch, ⊤) k) := by
    intro k
    have := congrArg (fun φ => φ k) hψK
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [this]
    show _ = (((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop) ≫ l.appTop ≫
      (Scheme.ΓSpecIso _).hom).hom k
    simp only [gT, Scheme.Hom.comp_appTop, Category.assoc, ← hl]
  have hL' : ∀ ℓ : L, ∃ p : Polynomial O, (∀ n, p.coeff n ∈ Algebra.adjoin Γ(Tsch, ⊤) T₀) ∧
      (∃ c : L, c ≠ 0 ∧ p.leadingCoeff = ψ c) ∧ p.eval (ψ ℓ) = 0 := by
    intro ℓ
    obtain ⟨p, hp, hc, hev⟩ := hL ℓ
    refine ⟨p, fun n => ?_, hc, hev⟩
    have hle : Subring.closure (T₀ ∪ Set.range (ψ.comp (algebraMap K L))) ≤
        (Algebra.adjoin Γ(Tsch, ⊤) T₀).toSubring := by
      rw [Subring.closure_le]
      rintro _ (h | ⟨k, rfl⟩)
      · exact Algebra.subset_adjoin h
      · show ψ (algebraMap K L k) ∈ Algebra.adjoin Γ(Tsch, ⊤) T₀
        rw [hKO]
        exact Subalgebra.algebraMap_mem _ _
    exact hle (hp n)
  -- `R = Γ(V)` is of finite type over `K`
  have : Algebra.FiniteType K Γ(Tsch, ⊤) := by
    show RingHom.FiniteType ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom
    exact RingHom.FiniteType.comp (HasRingHomProperty.appTop @LocallyOfFiniteType gT inferInstance)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  -- the system of levels and its limit
  have := QFSubalgebras.nonempty hT₀ hcov
  have : IsConnected (QFSubalgebras (R := Γ(Tsch, ⊤)) T₀)ᵒᵖ := IsCofiltered.isConnected _
  let Z := levelSystem Tsch T₀ ψ
  let cZ := levelLimitCone Tsch T₀ ψ
  let D : (QFSubalgebras (R := Γ(Tsch, ⊤)) T₀)ᵒᵖ ⥤ Scheme.{u} := levelSchemeDiagram Tsch T₀ ψ
  let π : D ⟶ (Functor.const _).obj X := levelStructure Tsch T₀ ψ ≫ (Functor.const _).map V.ι
  let gL : D ⟶ (Functor.const _).obj (Spec (.of L)) :=
    { app := fun i => Spec.map (CommRingCat.ofHom (levelAlgField ψ i.unop.1))
      naturality := fun i j a => by
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp]
        rfl }
  let p : (Functor.const _).obj (strictHenselization B X hS s) ⟶ D :=
    ((Over.forget Tsch).mapCone cZ).π
  have hp : IsLimit (Cone.mk _ p) := isLimitOfPreserves (Over.forget Tsch)
    (isLimitLevelLimitCone Tsch T₀ ψ hT₀ hcov)
  have hvert : cZ.pt.hom = l := by
    show Spec.map (l.appTop ≫ (Scheme.ΓSpecIso _).hom) ≫ Tsch.isoSpec.inv = l
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Category.assoc,
      Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have hπ : ∀ i, p.app i ≫ π.app i = strictHenselizationToBase B X hS s := by
    intro i
    show (cZ.π.app i).left ≫ (Z.obj i).hom ≫ V.ι = _
    have hw := Over.w (cZ.π.app i)
    simp only [Functor.const_obj_obj] at hw
    rw [← Category.assoc, hw, hvert]
    exact hl
  have hgL : ∀ i, gL.app i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = π.app i ≫ gX := by
    intro i
    show Spec.map (CommRingCat.ofHom (levelAlgField ψ i.unop.1)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Tsch, ⊤) (levelAlg ψ i.unop.1))) ≫
        Tsch.isoSpec.inv) ≫ V.ι) ≫ gX
    rw [Category.assoc, Category.assoc, ← Category.assoc Tsch.isoSpec.inv]
    show _ = _ ≫ Tsch.isoSpec.inv ≫ gT
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext k
    exact hKO k
  have hfin : ∀ i, LocallyOfFiniteType (gL.app i) := fun i =>
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (finiteType_levelAlg ψ K hKO i.unop.1 i.unop.2.1)
  have : Nonempty X := ⟨y⟩
  refine ⟨L, inferInstance, inferInstance, inferInstance, _, inferInstance, inferInstance,
    inferInstance, D, π, gL, p, ⟨hp⟩, hπ, fun i => inferInstanceAs (IsAffine (Spec _)),
    fun _ _ _ => inferInstance, hfin, hgL, fun i => ?_⟩
  have := hfin i
  have : CompactSpace (D.obj i) := inferInstanceAs (CompactSpace (Spec _))
  exact topologicalKrullDim_lt_of_isIntegral_residueFieldMap K L gX (gL.app i) (π.app i)
    (hgL i) (fun z => isIntegral_residueFieldMap_comp _ _ z
      (isIntegral_residueFieldMap_levelSystem Tsch T₀ ψ hL' i z)
      (isIntegral_residueFieldMap_of_isIso V.ι _)) (ha.trans_le hbL)

end AlgebraicGeometry

end
