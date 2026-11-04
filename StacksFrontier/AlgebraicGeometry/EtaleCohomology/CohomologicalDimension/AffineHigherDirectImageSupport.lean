module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.BaseChangeLimitVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.QuasiFiniteLevelSchemes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.StrictHenselizationField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.StrictHenselizationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SupportedSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TrdegSupportVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TrdegSupportVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of higher direct images along an affine morphism over a field

Let `f : X ⟶ Y` be an affine morphism of schemes of finite type over a field `K`, let `E_a(X)` be
the set of points `x ∈ X` with `trdeg_K κ(x) ≤ a`, and let `𝓕` be an abelian torsion sheaf on
`X_ét` whose support is contained in `E_a(X)`. Then `R^q f_* 𝓕` has support contained in
`E_{a - q}(Y)` ([Stacks, Tag 0F0X]).

## The proof

It is the source's. Let `s` be a geometric point of `Y` over a point `y` with
`b = trdeg_K κ(y)`. By [Stacks, Tag 03Q9] the stalk of `R^q f_* 𝓕` at `s` is
`H^q(X ×_Y Spec(𝒪^{sh}_{Y,s}), p⁻¹𝓕)`. Choose an affine open `V ∋ y`; the strict henselization
maps to `V` and contains a separably closed field `L ⊇ K` with `trdeg_K L ≥ b` ([Stacks, Tag
0F0U], `AlgebraicGeometry.exists_sepClosed_field_strictHenselization`). Write `𝒪^{sh}_{Y,s}` as
the filtered union of the finite type `L`-algebras `B_D` of
`AlgebraicGeometry.levelAlg`; then `X ×_Y Spec(𝒪^{sh}_{Y,s}) = lim_D X_V ×_V Spec(B_D)`, the
levels being affine of finite type over `L`. A point `z` of a level in the support of the inverse
image of `𝓕` maps to a point `x ∈ E_a(X)`, and `κ(z)/κ(x)` is algebraic
(`AlgebraicGeometry.isIntegral_residueFieldMap_levelSystem`), so `trdeg_L κ(z) ≤ a - b`. By
[Stacks, Tag 0F0W] over `L`, which has cohomological dimension `0`, the cohomology of the levels
vanishes in degrees `q > a - b`, and by [Stacks, Tag 03Q6] so does that of the limit.

## Main results

* `AlgebraicGeometry.smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset`:
  **Stacks 0F0X**.
* `AlgebraicGeometry.isZero_rightDerived_etaleAbelianDirectImage_of_lt`: `R^q f_* 𝓕 = 0` for
  `q > a`.
* `AlgebraicGeometry.subsingleton_H_strictHenselizationBaseChange_of_trdeg`: the vanishing on the
  base change to the strict henselization.
* `AlgebraicGeometry.subsingleton_H_level_of_trdeg`: the vanishing on one level, the step that
  applies Tag 0F0W.

## References

* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0F0U](https://stacks.math.columbia.edu/tag/0F0U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

-- In the import closure of Stacks 0F0W two global instances make unrelated searches time out:
-- every `IsIntegral Y` goal is sent through `IsVariety.toIsIntegral` over all fields and
-- morphisms, and `Stacks.Chow.isIso_stalkMap_of_isDominant_of_isPreimmersion` matches every
-- `IsIso` of a stalk map. Neither is used here.
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral
  Stacks.Chow.isIso_stalkMap_of_isDominant_of_isPreimmersion

/-- The `K`-algebra structure on a residue field through a morphism to `Spec K` depends only on
the morphism. -/
private theorem residueField_algebra_congr (K : Type u) [Field K] {W : Scheme.{u}}
    {g₁ g₂ : W ⟶ Spec (.of K)} (h : g₁ = g₂) (w : W) :
    ((Scheme.ΓSpecIso (.of K)).inv ≫ g₁.appTop ≫ W.Γevaluation w).hom =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ g₂.appTop ≫ W.Γevaluation w).hom := by
  subst h
  rfl

/-- Mathlib's sheaf pullback carries torsion abelian sheaves to torsion abelian sheaves:
`Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage` read through the
identification `Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage` of the two
inverse images. -/
theorem torsionSheafProperty_smallEtalePullbackAb {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((smallEtalePullbackAb f).obj F) :=
  Stacks.Torsion.torsionSheafProperty_of_iso Y.smallEtaleTopology
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage f).app F).symm
    (torsionSheafProperty_etaleAbelianInverseImage.{u, u + 1} f F hF)

/-- The support of the pullback of an abelian sheaf along `f` lies in the preimage under `f` of
any set containing the support of the sheaf. -/
private theorem smallEtaleSupport_smallEtalePullbackAb_subset {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {E : Set X}
    (hF : smallEtaleSupport F ⊆ E) :
    smallEtaleSupport ((smallEtalePullbackAb f).obj F) ⊆ ⇑f ⁻¹' E := by
  rw [smallEtaleSupport_subset_iff]
  intro s hs
  exact ((smallEtaleSupport_subset_iff F E).1 hF ⟨s.residueField, s.hom ≫ f⟩ hs).of_iso
    ((smallEtaleStalkPullbackAbIso f s.hom).app F)

/-- For `π : P ⟶ X` lying over `Spec L ⟶ Spec K`, with integral residue field extension at `w`,
`trdeg_K L + trdeg_L κ(w) ≤ trdeg_K κ(π w)`. -/
private theorem trdeg_add_trdeg_residueField_le_of_isIntegral (K L : Type u) [Field K] [Field L]
    [Algebra K L] {X P : Scheme.{u}} (gX : X ⟶ Spec (.of K)) (gP : P ⟶ Spec (.of L))
    (π : P ⟶ X) (hπ : gP ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = π ≫ gX) (w : P)
    (hw : (π.residueFieldMap w).hom.IsIntegral) :
    letI : Algebra L (P.residueField w) :=
      ((Scheme.ΓSpecIso (.of L)).inv ≫ gP.appTop ≫ P.Γevaluation w).hom.toAlgebra
    letI : Algebra K (X.residueField (π w)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (π w)).hom.toAlgebra
    Algebra.trdeg K L + Algebra.trdeg L (P.residueField w) ≤
      Algebra.trdeg K (X.residueField (π w)) := by
  have htr := trdeg_residueField_le_of_isIntegral K gX π w hw
  -- the tower `K → L → κ(w)`
  let : Algebra L (P.residueField w) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ gP.appTop ≫ P.Γevaluation w).hom.toAlgebra
  let : Algebra K (P.residueField w) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (π ≫ gX).appTop ≫ P.Γevaluation w).hom.toAlgebra
  have : IsScalarTower K L (P.residueField w) := by
    apply IsScalarTower.of_algebraMap_eq'
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ (π ≫ gX).appTop ≫ P.Γevaluation w).hom = _
    rw [← residueField_algebra_congr K hπ w, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  exact (trdeg_add_le (R := K) (S := L) (A := P.residueField w)).trans htr

/-- **The vanishing on one level, by Stacks 0F0W over a separably closed field.** Let `T`, `W`,
`Z` be affine schemes, `h : W ⟶ T` locally of finite type and `g : Z ⟶ T` with integral residue
field extensions, and `gZ : Z ⟶ Spec L` locally of finite type over a separably closed field `L`
over `K`, compatibly with `gT : T ⟶ Spec K`. Let `i : W ⟶ X` have integral residue field
extensions, compatibly with `gX : X ⟶ Spec K`, and let `𝓕` be a torsion sheaf on `X_ét` supported
in `E_a(X)`. If `b ≤ trdeg_K L` and `a < q + b`, then the degree `q` cohomology of the inverse
image of `𝓕` on the level `Z ×_T W` vanishes.

A point `w` of the level in the support of the inverse image maps to a point of `E_a(X)`, and
`trdeg_K L + trdeg_L κ(w) ≤ trdeg_K κ(w) ≤ a`, so `w ∈ E_{a - b}` over `L`; Stacks 0F0W over `L`
(`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_trdegLESet`), `L` having
cohomological dimension `0`, gives the vanishing above `a - b`. When `b > a` the support is empty
and the sheaf is zero. -/
@[sga "4 VIII 2.4" "special case"]
theorem subsingleton_H_level_of_trdeg (K : Type u) [Field K] {X T Z W : Scheme.{u}}
    [IsAffine Z] [IsAffine W] [IsAffine T]
    (gX : X ⟶ Spec (.of K)) (gT : T ⟶ Spec (.of K)) (i : W ⟶ X) (h : W ⟶ T)
    (hgi : i ≫ gX = h ≫ gT) [LocallyOfFiniteType h]
    (hi : ∀ w, (i.residueFieldMap w).hom.IsIntegral)
    (g : Z ⟶ T) (hg : ∀ z, (g.residueFieldMap z).hom.IsIntegral)
    (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] (gZ : Z ⟶ Spec (.of L))
    [LocallyOfFiniteType gZ]
    (hgZ : gZ ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = g ≫ gT)
    (a b q : ℕ) (hb : (b : Cardinal) ≤ Algebra.trdeg K L) (hq : a < q + b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : smallEtaleSupport F ⊆ Scheme.trdegLESet K gX a) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((smallEtalePullbackAb (pullback.snd g h)).obj ((smallEtalePullbackAb i).obj F)) q) := by
  let P := pullback g h
  let π : P ⟶ X := pullback.snd g h ≫ i
  let gP : P ⟶ Spec (.of L) := pullback.fst g h ≫ gZ
  let G := (smallEtalePullbackAb (pullback.snd g h)).obj ((smallEtalePullbackAb i).obj F)
  have hG : Stacks.Torsion.torsionSheafProperty P.smallEtaleTopology G :=
    torsionSheafProperty_smallEtalePullbackAb _ _
      (torsionSheafProperty_smallEtalePullbackAb _ _ hF)
  have hπ : gP ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = π ≫ gX := by
    simp only [gP, π, Category.assoc, hgZ, hgi]
    rw [pullback.condition_assoc]
  -- every point of the support of `G` lies in `E_{a - b}` over `L`
  have hpt : ∀ w : P, w ∈ smallEtaleSupport G →
      letI : Algebra L (P.residueField w) :=
        ((Scheme.ΓSpecIso (.of L)).inv ≫ gP.appTop ≫ P.Γevaluation w).hom.toAlgebra
      (b : Cardinal) + Algebra.trdeg L (P.residueField w) ≤ a := by
    intro w hw
    -- the image of `w` in `X` lies in the support of `𝓕`
    have hxw : π w ∈ Scheme.trdegLESet K gX a := by
      have := smallEtaleSupport_smallEtalePullbackAb_subset (pullback.snd g h) _
        (smallEtaleSupport_smallEtalePullbackAb_subset i F hsupp) hw
      rwa [Set.mem_preimage, Set.mem_preimage, ← Scheme.Hom.comp_apply] at this
    -- the residue field extension `κ(π w) → κ(w)` is integral
    exact (add_le_add hb le_rfl).trans
      ((trdeg_add_trdeg_residueField_le_of_isIntegral K L gX gP π hπ w
        (isIntegral_residueFieldMap_comp _ _ w
          (isIntegral_residueFieldMap_pullback_snd g h hg w) (hi _))).trans hxw)
  by_cases hba : b ≤ a
  · -- the case `b ≤ a`: Stacks 0F0W over `L`
    have hsuppG : smallEtaleSupport G ⊆ Scheme.trdegLESet L gP (a - b) := by
      intro w hw
      have h₁ := hpt w hw
      let : Algebra L (P.residueField w) :=
        ((Scheme.ΓSpecIso (.of L)).inv ≫ gP.appTop ≫ P.Γevaluation w).hom.toAlgebra
      change Algebra.trdeg L (P.residueField w) ≤ ((a - b : ℕ) : Cardinal)
      have hfin : Algebra.trdeg L (P.residueField w) < Cardinal.aleph0 :=
        (le_add_self.trans h₁).trans_lt (Cardinal.natCast_lt_aleph0)
      obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 hfin
      rw [hn] at h₁ ⊢
      norm_cast at h₁ ⊢
      omega
    refine subsingleton_H_of_smallEtaleSupport_subset_trdegLESet L gP (a - b) G hG hsuppG q ?_
    have : ((a - b : ℕ) : ℕ∞) < q := by
      norm_cast
      omega
    calc ((a - b : ℕ) : ℕ∞) + Scheme.etaleCohomologicalDimension (Spec (.of L))
        ≤ ((a - b : ℕ) : ℕ∞) + 0 :=
          add_le_add le_rfl (Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed L)
      _ < q := by simpa using this
  · -- the case `a < b`: the support is empty, so the sheaf is zero
    have hzero : IsZero G := by
      refine isZero_of_forall_isZero_smallEtaleStalkAb G fun s => ?_
      by_contra hn
      exact hba (by exact_mod_cast le_self_add.trans (hpt _ ⟨s, rfl, hn⟩))
    exact Sheaf.subsingleton_H_of_isZero hzero q

/-- The global sections of an affine scheme locally of finite type over a field `K` form a
finitely generated `K`-algebra. -/
private theorem finiteType_Γ_of_locallyOfFiniteType (K : Type u) [Field K] {T : Scheme.{u}}
    [IsAffine T] (gT : T ⟶ Spec (.of K)) [LocallyOfFiniteType gT] :
    letI : Algebra K Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom.toAlgebra
    Algebra.FiniteType K Γ(T, ⊤) := by
  let : Algebra K Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom.toAlgebra
  change RingHom.FiniteType ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom
  exact RingHom.FiniteType.comp (HasRingHomProperty.appTop @LocallyOfFiniteType gT inferInstance)
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)

/-- If a ring map `φ : K → O` factors through `R → O`, the subring generated by `T₀` and the
image of `φ` lies in the `R`-subalgebra generated by `T₀`. -/
private theorem closure_union_range_le_adjoin {K R O : Type*} [CommRing K] [CommRing R] [CommRing O]
    [Algebra K R] [Algebra R O] (T₀ : Set O) (φ : K →+* O)
    (hφ : ∀ k, φ k = algebraMap R O (algebraMap K R k)) :
    Subring.closure (T₀ ∪ Set.range φ) ≤ (Algebra.adjoin R T₀).toSubring := by
  rw [Subring.closure_le]
  rintro _ (h | ⟨k, rfl⟩)
  · exact Algebra.subset_adjoin h
  · rw [hφ]
    exact Subalgebra.algebraMap_mem _ _

/-- **The vanishing on the levels of the strict henselization.** Let `T` be affine of finite type
over `K`, `ψ : L → O` a separably closed field over `K` in a `Γ(T)`-algebra `O`, compatibly with
`K → Γ(T)`, such that every element of `L` is a root of a polynomial with coefficients in
`Γ(T)[T₀]` and leading coefficient in `ψ(L)ˣ`. Then, in the situation of
`AlgebraicGeometry.subsingleton_H_level_of_trdeg`, the cohomology of each level
`Spec B_D ×_T W` of `AlgebraicGeometry.levelSystem` vanishes. -/
private theorem subsingleton_H_levelSystem_of_trdeg (K : Type u) [Field K] {X T W : Scheme.{u}}
    [IsAffine T] [IsAffine W] {O : Type u} [CommRing O] [Algebra Γ(T, ⊤) O] (T₀ : Set O)
    (L : Type u) [Field L] [IsSepClosed L] [Algebra K L] (ψ : L →+* O)
    (gX : X ⟶ Spec (.of K)) (gT : T ⟶ Spec (.of K)) [LocallyOfFiniteType gT]
    (hK : letI : Algebra K Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom.toAlgebra
      ∀ k : K, ψ (algebraMap K L k) = algebraMap Γ(T, ⊤) O (algebraMap K Γ(T, ⊤) k))
    (hL : ∀ ℓ : L, ∃ p : Polynomial O, (∀ n, p.coeff n ∈ Algebra.adjoin Γ(T, ⊤) T₀) ∧
      (∃ c : L, c ≠ 0 ∧ p.leadingCoeff = ψ c) ∧ p.eval (ψ ℓ) = 0)
    (i : W ⟶ X) (h : W ⟶ T) (hgi : i ≫ gX = h ≫ gT) [LocallyOfFiniteType h]
    (hi : ∀ w, (i.residueFieldMap w).hom.IsIntegral) (D : (QFSubalgebras (R := Γ(T, ⊤)) T₀)ᵒᵖ)
    (a b q : ℕ) (hb : (b : Cardinal) ≤ Algebra.trdeg K L) (hq : a < q + b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : smallEtaleSupport F ⊆ Scheme.trdegLESet K gX a) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((smallEtalePullbackAb (pullback.snd ((levelSystem T T₀ ψ).obj D).hom h)).obj
        ((smallEtalePullbackAb i).obj F)) q) := by
  let : Algebra K Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom.toAlgebra
  -- `R = Γ(T)` is of finite type over `K`
  have : Algebra.FiniteType K Γ(T, ⊤) := finiteType_Γ_of_locallyOfFiniteType K gT
  let gZ : ((levelSystem T T₀ ψ).obj D).left ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (levelAlgField ψ D.unop.1))
  have : LocallyOfFiniteType gZ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (finiteType_levelAlg ψ K hK D.unop.1 D.unop.2.1)
  refine subsingleton_H_level_of_trdeg K gX gT i h hgi hi ((levelSystem T T₀ ψ).obj D).hom
    (fun z => isIntegral_residueFieldMap_levelSystem T T₀ ψ hL D z) L gZ ?_ a b q hb hq F hF hsupp
  change Spec.map (CommRingCat.ofHom (levelAlgField ψ D.unop.1)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) =
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (levelAlg ψ D.unop.1))) ≫
      T.isoSpec.inv) ≫ gT
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext k
  exact hK k

variable (B : BigEtaleSite.{u})

/-- The structure map of the vertex of the system of levels is the map from the strict
henselization to the affine open. -/
private theorem levelVertexHom_eq {T : Scheme.{u}} [IsAffine T] {A : CommRingCat.{u}}
    (l : Spec A ⟶ T) :
    letI : Algebra Γ(T, ⊤) A := (l.appTop ≫ (Scheme.ΓSpecIso A).hom).hom.toAlgebra
    levelVertexHom T (O := A) = l := by
  let : Algebra Γ(T, ⊤) A := (l.appTop ≫ (Scheme.ΓSpecIso A).hom).hom.toAlgebra
  change Spec.map (l.appTop ≫ (Scheme.ΓSpecIso A).hom) ≫ T.isoSpec.inv = l
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Category.assoc,
    Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Vanishing passes from the levels to the strict henselization.** Let `V ∋ y` be an affine
open, `l : Spec(𝒪^{sh}_{Y,s}) ⟶ V` the ind-étale lift of the structure map, and
`ψ : L → 𝒪^{sh}_{Y,s}` a field with `T₀` finite. If the degree `q` cohomology of the inverse image
of `𝓕` vanishes on every level `f⁻¹V ×_V Spec(B_D)`, then it vanishes on
`X ×_Y Spec(𝒪^{sh}_{Y,s})`: the latter is the limit of the levels
(`AlgebraicGeometry.isLimitLevelLimitCone`), and vanishing passes to the limit by the vanishing
form of Stacks 03Q6 (`AlgebraicGeometry.subsingleton_sheafH_limit_of_levels_of_isAffine`). -/
private theorem subsingleton_H_strictHenselizationBaseChange_of_levels {X Y : Scheme.{u}}
    (hS : B.Contains Y) (f : X ⟶ Y) [IsAffineHom f] (s : GeometricPoint Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (l : strictHenselization B Y hS s ⟶ V.toScheme)
    (hl : l ≫ V.ι = strictHenselizationToBase B Y hS s)
    (hind : MorphismProperty.ind.{u} CommRingCat.etale.{u} l.appTop)
    {T₀ : Set ↥(etaleLocalRing B Y hS s)} (hT₀ : T₀.Finite) {L : Type u} [Field L]
    (ψ : L →+* ↥(etaleLocalRing B Y hS s)) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hlevel : haveI : IsAffine V.toScheme := hV
      letI : Algebra Γ(V.toScheme, ⊤) ↥(etaleLocalRing B Y hS s) :=
        (l.appTop ≫ (Scheme.ΓSpecIso _).hom).hom.toAlgebra
      ∀ D, Subsingleton (Sheaf.H.{u + 1, u + 1}
        ((smallEtalePullbackAb (pullback.snd ((levelSystem V.toScheme T₀ ψ).obj D).hom
          (f ∣_ V))).obj ((smallEtalePullbackAb (f ⁻¹ᵁ V).ι).obj F)) q)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) q) := by
  have : IsAffine V.toScheme := hV
  let Tsch : Scheme.{u} := V.toScheme
  let O := ↥(etaleLocalRing B Y hS s)
  let φR : Γ(Tsch, ⊤) ⟶ CommRingCat.of O := l.appTop ≫ (Scheme.ΓSpecIso _).hom
  let : Algebra Γ(Tsch, ⊤) O := φR.hom.toAlgebra
  -- `O` is covered by finitely generated quasi-finite subalgebras
  have hcov := exists_fg_quasiFinite_mem_of_ind_etale φR
    ((MorphismProperty.cancel_right_of_respectsIso _ _ _).2 hind)
  let W : Scheme.{u} := (f ⁻¹ᵁ V).toScheme
  have : IsAffine W := hV.preimage f
  let fV : W ⟶ Tsch := f ∣_ V
  let Xo : Over Tsch := Over.mk fV
  have : IsAffine Xo.left := inferInstanceAs (IsAffine W)
  -- the system of levels and its limit
  have := QFSubalgebras.nonempty hT₀ hcov
  let Z := levelSystem Tsch T₀ ψ
  let cZ := levelLimitCone Tsch T₀ ψ
  let cY := BaseChangeAlgebraSystem.baseChangeCone Tsch Xo Z cZ
  have hcY : IsLimit cY := BaseChangeAlgebraSystem.isLimitBaseChangeCone Tsch Xo Z cZ
    (isLimitLevelLimitCone Tsch T₀ ψ hT₀ hcov)
  -- the base change to the strict henselization is the vertex of the limit
  have hvert : cZ.pt.hom = l := levelVertexHom_eq l
  have hsh : strictHenselizationToBase B Y hS s = cZ.pt.hom ≫ V.ι := by
    rw [hvert]
    exact hl.symm
  have h₃ : IsPullback (pullback.fst cZ.pt.hom fV) (pullback.snd cZ.pt.hom fV ≫ (f ⁻¹ᵁ V).ι)
      (cZ.pt.hom ≫ V.ι) f :=
    (IsPullback.of_hasPullback cZ.pt.hom fV).paste_vert (isPullback_morphismRestrict f V)
  rw [← hsh] at h₃
  have h₄ := (IsPullback.of_hasPullback f (strictHenselizationToBase B Y hS s)).flip
  let e : strictHenselizationBaseChange B hS f s ≅ cY.pt := h₄.isoIsPullback _ _ h₃
  have he : e.hom ≫ pullback.snd cZ.pt.hom fV ≫ (f ⁻¹ᵁ V).ι =
      strictHenselizationBaseChangeToSource B hS f s :=
    h₄.isoIsPullback_hom_snd _ _ h₃
  -- the limit cone with vertex `X ×_Y Spec(𝒪^{sh}_{Y,s})`
  let cY' := cY.extend e.hom
  have hcY' : IsLimit cY' := hcY.ofIsoLimit (Cone.extendIso cY e.symm)
  let p' : strictHenselizationBaseChange B hS f s ⟶ W := e.hom ≫ pullback.snd cZ.pt.hom fV
  have hpi : ∀ i, cY.π.app i ≫ pullback.snd (Z.obj i).hom Xo.hom =
      pullback.snd cZ.pt.hom fV := fun i => Over.w ((Over.pullback Xo.hom).map (cZ.π.app i))
  have hp' : ∀ i, p' = cY'.π.app i ≫ pullback.snd (Z.obj i).hom Xo.hom := by
    intro i
    change e.hom ≫ pullback.snd cZ.pt.hom fV = (e.hom ≫ cY.π.app i) ≫ _
    exact (congrArg (e.hom ≫ ·) (hpi i).symm).trans (Category.assoc _ _ _).symm
  -- vanishing passes to the limit (Stacks 03Q6)
  have hmain := subsingleton_sheafH_limit_of_levels_of_isAffine Tsch Xo Z
    ((smallEtalePullbackAb (f ⁻¹ᵁ V).ι).obj F) cY' hcY' p' hp' q hlevel
  -- and the inverse images agree
  let ε := (smallEtalePullbackAbCompIso' p' (f ⁻¹ᵁ V).ι
    (strictHenselizationBaseChangeToSource B hS f s) he.symm).app F
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}]
    at hmain ⊢
  exact hmain.of_iso (((Sheaf.Γ _ AddCommGrpCat.{u + 1}).rightDerived q).mapIso ε).symm

/-- **The cohomology of the base change to the strict henselization vanishes.** Let
`f : X ⟶ Y` be an affine morphism, `X` and `Y` locally of finite type over a field `K`, `s` a
geometric point of `Y` over `y`, and `𝓕` a torsion sheaf on `X_ét` supported in `E_a(X)`. If
`a < q + trdeg_K κ(y)`, then `H^q(X ×_Y Spec(𝒪^{sh}_{Y,s}), p⁻¹𝓕) = 0`.

This is the heart of the proof of Stacks 0F0X: `X ×_Y Spec(𝒪^{sh}_{Y,s})` is the limit of the
levels `f⁻¹V ×_V Spec(B_D)` (`AlgebraicGeometry.isLimitLevelLimitCone`), whose cohomology vanishes
by `AlgebraicGeometry.subsingleton_H_level_of_trdeg`, and vanishing passes to the limit by the
vanishing form of Stacks 03Q6
(`AlgebraicGeometry.subsingleton_sheafH_limit_of_levels_of_isAffine`). -/
theorem subsingleton_H_strictHenselizationBaseChange_of_trdeg
    {K : Type u} [Field K] {X Y : Scheme.{u}} (hS : B.Contains Y) (f : X ⟶ Y) [IsAffineHom f]
    (gX : X ⟶ Spec (.of K)) (gY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType gX]
    [LocallyOfFiniteType gY] (hfg : f ≫ gY = gX) (s : GeometricPoint Y) (a q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : smallEtaleSupport F ⊆ Scheme.trdegLESet K gX a)
    (hq : letI : Algebra K (Y.residueField (s.hom (closedPoint s.residueField))) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ gY.appTop ≫
          Y.Γevaluation (s.hom (closedPoint s.residueField))).hom.toAlgebra
      (a : Cardinal) < q + Algebra.trdeg K (Y.residueField (s.hom (closedPoint s.residueField)))) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) q) := by
  classical
  set y := s.hom (closedPoint s.residueField)
  let : Algebra K (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ gY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  -- `b = trdeg_K κ(y)` is finite
  have : FinTrdeg K (Y.residueField y) := residueField_finTrdeg K gY y
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.1 (trdeg_lt_aleph0 K (Y.residueField y))
  have hqb : a < q + b := by
    rw [hb] at hq
    exact_mod_cast hq
  -- an affine open around `y`, the map from the strict henselization, and the field `L`
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  set V : Y.Opens := V₀
  obtain ⟨l, hl, hind⟩ := exists_lift_ind_etale_appTop_strictHenselizationToBase B hS s V hV hyV
  obtain ⟨L, _, _, _, ψ, T₀, hT₀, hψK, hbL, hL⟩ :=
    exists_sepClosed_field_strictHenselization B hS s gY
  have : IsAffine V.toScheme := hV
  let Tsch : Scheme.{u} := V.toScheme
  let O := ↥(etaleLocalRing B Y hS s)
  let : Algebra Γ(Tsch, ⊤) O := (l.appTop ≫ (Scheme.ΓSpecIso _).hom).hom.toAlgebra
  -- the `K`-structures
  let gT : Tsch ⟶ Spec (.of K) := V.ι ≫ gY
  let : Algebra K Γ(Tsch, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop).hom.toAlgebra
  have hKO : ∀ k : K,
      ψ (algebraMap K L k) = algebraMap Γ(Tsch, ⊤) O (algebraMap K Γ(Tsch, ⊤) k) := by
    intro k
    have := congrArg (fun φ => φ k) hψK
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [this]
    change _ = (((Scheme.ΓSpecIso (.of K)).inv ≫ gT.appTop) ≫ l.appTop ≫
      (Scheme.ΓSpecIso _).hom).hom k
    simp only [gT, Scheme.Hom.comp_appTop, Category.assoc, ← hl]
  have hL' : ∀ ℓ : L, ∃ p : Polynomial O, (∀ n, p.coeff n ∈ Algebra.adjoin Γ(Tsch, ⊤) T₀) ∧
      (∃ c : L, c ≠ 0 ∧ p.leadingCoeff = ψ c) ∧ p.eval (ψ ℓ) = 0 := fun ℓ =>
    (hL ℓ).imp fun p ⟨hp, hc, hev⟩ => ⟨fun n => closure_union_range_le_adjoin (R := Γ(Tsch, ⊤))
      T₀ (ψ.comp (algebraMap K L)) hKO (hp n), hc, hev⟩
  -- the restriction of `f` over `V`
  have : IsAffine (f ⁻¹ᵁ V) := hV.preimage f
  have hfV : f ∣_ V ≫ V.ι = (f ⁻¹ᵁ V).ι ≫ f := morphismRestrict_ι f V
  have hgi : (f ⁻¹ᵁ V).ι ≫ gX = f ∣_ V ≫ gT := by
    change _ = f ∣_ V ≫ V.ι ≫ gY
    rw [← Category.assoc, hfV, Category.assoc, hfg]
  have : LocallyOfFiniteType (f ∣_ V ≫ gT) := hgi ▸ inferInstance
  have : LocallyOfFiniteType (f ∣_ V) := locallyOfFiniteType_of_comp _ gT
  -- vanishing passes from the levels to the limit (Stacks 03Q6)
  exact subsingleton_H_strictHenselizationBaseChange_of_levels B hS f s hV l hl hind hT₀ ψ q F
    fun D => subsingleton_H_levelSystem_of_trdeg K T₀ L ψ gX gT hKO hL' (f ⁻¹ᵁ V).ι (f ∣_ V) hgi
      (fun w => isIntegral_residueFieldMap_of_isIso _ w) D a b q (hb ▸ hbL) hqb F hF hsupp

/-- **Stacks Project, Tag 0F0X.** Let `f : X ⟶ Y` be an affine morphism of schemes locally of
finite type over a field `K` (the structure morphisms `gX`, `gY`, with `f ≫ gY = gX`), let
`E_a(X)` be the set of points `x ∈ X` with `trdeg_K κ(x) ≤ a`
(`AlgebraicGeometry.Scheme.trdegLESet`), and let `𝓕` be an abelian torsion sheaf on `X_ét` whose
support is contained in `E_a(X)`. Then `R^q f_* 𝓕` has support contained in `E_{a - q}(Y)`: every
point `y` of its support has `trdeg_K κ(y) + q ≤ a` (so the support is empty when `q > a`).

The proof is the source's: Stacks 03Q9
(`AlgebraicGeometry.isZero_stalk_rightDerived_iff_subsingleton_sheafH`) computes the stalk at a
geometric point over `y` as the cohomology of `X ×_Y Spec(𝒪^{sh}_{Y,y})`, which vanishes by
`AlgebraicGeometry.subsingleton_H_strictHenselizationBaseChange_of_trdeg` (Stacks 0F0U, 0F0W
over a separable closure of `K(t_1, …, t_b)`, and the vanishing form of Stacks 03Q6). -/
@[stacks 0F0X, sga "4 XIV 3.1" "more general"]
theorem smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset
    (K : Type u) [Field K] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of K)) (gY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType gX] [LocallyOfFiniteType gY] (f : X ⟶ Y) [IsAffineHom f]
    (hfg : f ≫ gY = gX) (a : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : smallEtaleSupport F ⊆ Scheme.trdegLESet K gX a) (q : ℕ) :
    smallEtaleSupport (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj F) ⊆
      {y | letI : Algebra K (Y.residueField y) :=
          ((Scheme.ΓSpecIso (.of K)).inv ≫ gY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
        Algebra.trdeg K (Y.residueField y) + q ≤ a} := by
  rintro y ⟨t, ht, hnz⟩
  obtain rfl : t.hom (closedPoint t.residueField) = y := by
    rw [← ht]
    exact congrArg t.hom (Subsingleton.elim _ _)
  by_contra hlt
  apply hnz
  let B := BigEtaleSite.containing Y
  have hS : B.Contains Y := BigEtaleSite.contains_containing Y
  refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS f t F q).2 ?_
  refine subsingleton_H_strictHenselizationBaseChange_of_trdeg B hS f gX gY hfg t a q
    F hF hsupp ?_
  rw [add_comm]
  exact lt_of_not_ge hlt

/-- **Higher direct images above the transcendence degree bound vanish.** In the situation of
`AlgebraicGeometry.smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset` (Stacks 0F0X),
for `q > a` the support of `R^q f_* 𝓕` is empty, and an abelian sheaf with vanishing stalks is
zero. -/
@[sga "4 XIV 3.1" "(d)", sga "4 XIX 6.1" "Uniform field-base case"]
theorem isZero_rightDerived_etaleAbelianDirectImage_of_lt
    (K : Type u) [Field K] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of K)) (gY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType gX] [LocallyOfFiniteType gY] (f : X ⟶ Y) [IsAffineHom f]
    (hfg : f ≫ gY = gX) (a : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : smallEtaleSupport F ⊆ Scheme.trdegLESet K gX a) (q : ℕ) (hq : a < q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj F) := by
  refine isZero_of_forall_isZero_smallEtaleStalkAb _ fun t => ?_
  by_contra hnz
  have h := smallEtaleSupport_rightDerived_etaleAbelianDirectImage_subset
    K gX gY f hfg a F hF hsupp q ⟨t, rfl, hnz⟩
  have : (q : Cardinal) ≤ a := le_add_self.trans h
  exact not_le.2 hq (by exact_mod_cast this)

end AlgebraicGeometry

end
