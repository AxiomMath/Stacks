module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleGaloisCohomologyComparison
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurveTorsionStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence

/-!
# The eight statements of Situation 0A52 over a decomposition into two clopen pieces

Let `X` be a separated scheme of finite type and dimension at most one over an algebraically
closed field `k`, and let `X = U ⊔ V` be a decomposition into two open and closed subschemes. An
abelian sheaf `F` on `X_étale` is the biproduct of the direct images of its restrictions to the
two pieces, so — granted that the eight statements of [Stacks, Tag 0A52] pass to the middle term
of a short exact sequence ([Stacks, Tag 0A5C]) and to a finite direct image
([Stacks, Tag 0A5D]) — they hold for `F` as soon as they hold for its restrictions to `U` and to
`V`. This is the step "we may assume `X` is connected" of the proof of [Stacks, Tag 0A5B].

## Main definitions

* `Stacks.EtaleCohomology.CurveTorsionExtensionStatement`: the statement of [Stacks, Tag 0A5C].
* `Stacks.EtaleCohomology.CurveTorsionFiniteDirectImageStatement`: the statement of
  [Stacks, Tag 0A5D].

## Main results

* `Stacks.EtaleCohomology.isClosedImmersion_ι_of_isClosed`: the inclusion of an open subscheme
  whose underlying set is closed is a closed immersion.
* `Stacks.EtaleCohomology.isIso_biprodLift_unit_of_isCompl`: for complementary open and closed
  subschemes `U` and `V`, the units of the two inverse image–direct image adjunctions together
  give an isomorphism `F ≅ (U → X)_* F|_U ⊞ (V → X)_* F|_V`.
* `Stacks.EtaleCohomology.curveTorsionStatements_of_isCompl`: the eight statements for `F` from
  those for `F|_U` and `F|_V`, given Tags 0A5C and 0A5D.

## Implementation notes

Tags 0A5C and 0A5D enter as the named arguments `h0A5C` and `h0A5D`, with the source's statements
in terms of `Stacks.EtaleCohomology.CurveTorsionStatementsGeneral`. The isomorphism of the
splitting is checked after inverse image to `U` and to `V`, which jointly reflect isomorphisms
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage`): over `U` the direct image from
`V` vanishes and the unit for `U` becomes invertible, and symmetrically over `V`.

The sheaf is assumed killed by a positive integer rather than merely torsion, which is the case of
the constant sheaf `𝐙/ℓ𝐙` of Tag 0A5B; this makes the torsion of every sheaf in the splitting
immediate.

## References

* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] _root_.AlgebraicGeometry.hasExt_smallEtaleSheaf_objectUniverse

/-- **The statement of [Stacks, Tag 0A5C]**, on Mathlib's small étale site with coefficients in
`AddCommGrpCat.{u + 1}`. Let `k` be an algebraically closed field and `X` a separated scheme of
finite type over `k` of dimension at most one. Let `0 → F₁ → F → F₂ → 0` be a short exact sequence
of torsion abelian sheaves on `X_étale`. If the eight statements of Situation 0A52 hold for `F₁`
and `F₂`, then they hold for `F`. This proposition is the statement only. -/
def CurveTorsionExtensionStatement : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π], topologicalKrullDim X ≤ 1 →
    ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), S.ShortExact →
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology S.X₁ →
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology S.X₂ →
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology S.X₃ →
      CurveTorsionStatementsGeneral.{u, 0} π S.X₁ → CurveTorsionStatementsGeneral.{u, 0} π S.X₃ →
      CurveTorsionStatementsGeneral.{u, 0} π S.X₂

/-- **The statement of [Stacks, Tag 0A5D]**, on Mathlib's small étale site with coefficients in
`AddCommGrpCat.{u + 1}`. Let `k` be an algebraically closed field and `f : X ⟶ Y` a finite
morphism of separated schemes of finite type over `k` of dimension at most one, the structure
morphism of `X` being `f ≫ π`. Let `F` be a torsion abelian sheaf on `X_étale`. If the eight
statements of Situation 0A52 hold for `F`, then they hold for `f_* F`. This proposition is the
statement only. -/
def CurveTorsionFiniteDirectImageStatement : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (π : Y ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π],
    topologicalKrullDim X ≤ 1 → topologicalKrullDim Y ≤ 1 →
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
      CurveTorsionStatementsGeneral.{u, 0} (f ≫ π) F →
      CurveTorsionStatementsGeneral.{u, 0} π ((etaleAbelianDirectImage.{u, 0} f).obj F)

/-- **An open subscheme whose underlying set is closed is a closed subscheme**: its inclusion is
an open embedding with closed range, hence a closed embedding, and it is an isomorphism on
stalks. -/
theorem isClosedImmersion_ι_of_isClosed {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.ι where
  isClosedEmbedding := ⟨U.ι.isOpenEmbedding.isEmbedding, by simpa using hU⟩

/-- A sheaf killed by a positive integer `n` is torsion. -/
theorem torsionSheafProperty_of_zsmul_id_eq_zero_general {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ} (hn : 0 < n)
    (hF : (n : ℤ) • 𝟙 F = 0) : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F :=
  fun U x => ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ => ⟨n, hn, by
    rw [← natCast_zsmul]
    exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F (n : ℤ)).1 hF _ _⟩⟩

/-- An additive functor sends the map into a biproduct to an isomorphism if it sends its first
component to an isomorphism and kills the second summand. -/
private theorem isIso_map_biprod_lift_of_isZero_right {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] (G : C ⥤ D) [G.Additive]
    {A B E : C} (f : A ⟶ B) (g : A ⟶ E) [IsIso (G.map f)] (hE : IsZero (G.obj E)) :
    IsIso (G.map (biprod.lift f g)) := by
  have hfst : IsIso (G.map (biprod.fst : B ⊞ E ⟶ B)) := by
    refine ⟨⟨G.map biprod.inl, ?_, by rw [← G.map_comp, biprod.inl_fst, G.map_id]⟩⟩
    have h0 : G.map (biprod.snd : B ⊞ E ⟶ E) ≫ G.map (biprod.inr : E ⟶ B ⊞ E) = 0 := by
      rw [hE.eq_of_src (G.map (biprod.inr : E ⟶ B ⊞ E)) 0, Limits.comp_zero]
    rw [← G.map_comp, ← sub_eq_iff_eq_add.mpr (biprod.total (X := B) (Y := E)).symm, G.map_sub,
      G.map_id, G.map_comp, h0, sub_zero]
  have : IsIso (G.map (biprod.lift f g) ≫ G.map biprod.fst) := by
    rw [← G.map_comp, biprod.lift_fst]; infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map biprod.fst)

/-- An additive functor sends the map into a biproduct to an isomorphism if it kills the first
summand and sends the second component to an isomorphism. -/
private theorem isIso_map_biprod_lift_of_isZero_left {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] (G : C ⥤ D) [G.Additive]
    {A B E : C} (f : A ⟶ B) (g : A ⟶ E) [IsIso (G.map g)] (hB : IsZero (G.obj B)) :
    IsIso (G.map (biprod.lift f g)) := by
  have hsnd : IsIso (G.map (biprod.snd : B ⊞ E ⟶ E)) := by
    refine ⟨⟨G.map biprod.inr, ?_, by rw [← G.map_comp, biprod.inr_snd, G.map_id]⟩⟩
    have h0 : G.map (biprod.fst : B ⊞ E ⟶ B) ≫ G.map (biprod.inl : B ⟶ B ⊞ E) = 0 := by
      rw [hB.eq_of_src (G.map (biprod.inl : B ⟶ B ⊞ E)) 0, Limits.comp_zero]
    rw [← G.map_comp, ← sub_eq_iff_eq_add'.mpr (biprod.total (X := B) (Y := E)).symm,
      G.map_sub, G.map_id, G.map_comp, h0, sub_zero]
  have : IsIso (G.map (biprod.lift f g) ≫ G.map biprod.snd) := by
    rw [← G.map_comp, biprod.lift_snd]; infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map biprod.snd)

/-- An additive functor preserves being killed by an integer `n`. -/
private theorem zsmul_id_map_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] {E : C} {n : ℕ} (h : (n : ℤ) • 𝟙 E = 0) :
    (n : ℤ) • 𝟙 (G.obj E) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, h, Functor.map_zero]

section Splitting

variable {X : Scheme.{u}} (U V : X.Opens) (hUV : IsCompl U V)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

include hUV

omit hUV in
/-- The underlying set of the complement of a clopen decomposition is the set complement. -/
private theorem range_ι_eq_compl_of_isCompl (W₁ W₂ : X.Opens) (h : IsCompl W₁ W₂) :
    Set.range W₂.ι.base = (Set.range W₁.ι.base)ᶜ := by
  simp only [Scheme.Opens.range_ι]
  have h1 : (W₁ : Set X) ∩ W₂ = ∅ := by
    have := congrArg (fun W : X.Opens => (W : Set X)) h.inf_eq_bot
    simpa using this
  have h2 : (W₁ : Set X) ∪ W₂ = Set.univ := by
    have := congrArg (fun W : X.Opens => (W : Set X)) h.sup_eq_top
    simpa using this
  ext x
  constructor
  · intro hx hxU
    exact (Set.eq_empty_iff_forall_notMem.1 h1) x ⟨hxU, hx⟩
  · intro hx
    have : x ∈ (W₁ : Set X) ∪ W₂ := h2 ▸ Set.mem_univ x
    exact this.resolve_left hx

/-- In a decomposition into complementary opens, each piece is closed. -/
private theorem isClosed_of_isCompl : IsClosed (U : Set X) := by
  have hVU : (V : Set X) = (U : Set X)ᶜ := by
    simpa using range_ι_eq_compl_of_isCompl U V hUV
  rw [← compl_compl (U : Set X), ← hVU]
  exact V.isOpen.isClosed_compl

/-- In a decomposition into complementary opens, the inclusion of each piece is a closed
immersion. -/
private theorem isClosedImmersion_ι_of_isCompl : IsClosedImmersion U.ι :=
  isClosedImmersion_ι_of_isClosed U (isClosed_of_isCompl U V hUV)

/-- For complementary open and closed subschemes, the direct image from one piece vanishes after
inverse image to the other. -/
private theorem isZero_etaleAbelianInverseImage_directImage_of_isCompl
    (G : Sheaf V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsZero ((etaleAbelianInverseImage.{u, 0} U.ι).obj
      ((etaleAbelianDirectImage.{u, 0} V.ι).obj G)) :=
  (isZero_etaleRestriction_etaleAbelianDirectImage.{u, 0} V.ι U.ι
    (range_ι_eq_compl_of_isCompl V U hUV.symm) G).of_iso
    ((etaleAbelianInverseImageRestrictionIso.{u, 0} U.ι).app _)

/-- **A sheaf on a clopen decomposition is the biproduct of its pieces.** For complementary open
and closed subschemes `U` and `V` of `X`, the units of the two adjunctions `i^{-1} ⊣ i_*` give an
isomorphism `F ⟶ (U → X)_* F|_U ⊞ (V → X)_* F|_V`. -/
theorem isIso_biprodLift_unit_of_isCompl :
    IsIso (biprod.lift ((etaleAbelianInverseImageDirectImageAdj.{u, 0} U.ι).unit.app F)
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} V.ι).unit.app F)) := by
  have := isClosedImmersion_ι_of_isCompl U V hUV
  have := isClosedImmersion_ι_of_isCompl V U hUV.symm
  let φ := biprod.lift ((etaleAbelianInverseImageDirectImageAdj.{u, 0} U.ι).unit.app F)
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} V.ι).unit.app F)
  have hU' : IsIso ((etaleAbelianInverseImage.{u, 0} U.ι).map φ) := by
    have := isIso_etaleAbelianInverseImage_map_unit.{u, 0} U.ι F
    exact isIso_map_biprod_lift_of_isZero_right _ _ _
      (isZero_etaleAbelianInverseImage_directImage_of_isCompl U V hUV _)
  have hV' : IsIso ((etaleAbelianInverseImage.{u, 0} V.ι).map φ) := by
    have := isIso_etaleAbelianInverseImage_map_unit.{u, 0} V.ι F
    exact isIso_map_biprod_lift_of_isZero_left _ _ _
      (isZero_etaleAbelianInverseImage_directImage_of_isCompl V U hUV.symm _)
  exact isIso_of_isIso_etaleAbelianInverseImage.{u, 0} U.ι V.ι
    (range_ι_eq_compl_of_isCompl U V hUV) φ

end Splitting

/-- **The eight statements of Situation 0A52 over a clopen decomposition**, given
[Stacks, Tag 0A5C] (`h0A5C`) and [Stacks, Tag 0A5D] (`h0A5D`). Let `X` be a separated scheme of
finite type and dimension at most one over an
algebraically closed field, `X = U ⊔ V` a decomposition into complementary open and closed
subschemes, and `F` an abelian sheaf on `X_étale` killed by a positive integer. If the eight
statements hold for `F|_U` and for `F|_V`, then they hold for `F`.

`F` is the biproduct of the two direct images (`isIso_biprodLift_unit_of_isCompl`); each direct
image is a finite direct image, the inclusions being closed immersions, so Tag 0A5D gives the
eight statements for it, and Tag 0A5C applied to the split short exact sequence of the biproduct
gives them for the biproduct. -/
theorem curveTorsionStatements_of_isCompl (h0A5C : CurveTorsionExtensionStatement.{u})
    (h0A5D : CurveTorsionFiniteDirectImageStatement.{u}) {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1) (U V : X.Opens) (hUV : IsCompl U V)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n)
    (hF : (n : ℤ) • 𝟙 F = 0)
    (hFU : CurveTorsionStatementsGeneral.{u, 0} (U.ι ≫ π)
      ((etaleAbelianInverseImage.{u, 0} U.ι).obj F))
    (hFV : CurveTorsionStatementsGeneral.{u, 0} (V.ι ≫ π)
      ((etaleAbelianInverseImage.{u, 0} V.ι).obj F)) :
    CurveTorsionStatementsGeneral.{u, 0} π F := by
  have := isClosedImmersion_ι_of_isCompl U V hUV
  have := isClosedImmersion_ι_of_isCompl V U hUV.symm
  have hdim : ∀ W : X.Opens, topologicalKrullDim (W : Scheme.{u}) ≤ 1 := fun W =>
    (W.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  let A := (etaleAbelianDirectImage.{u, 0} U.ι).obj ((etaleAbelianInverseImage.{u, 0} U.ι).obj F)
  let B := (etaleAbelianDirectImage.{u, 0} V.ι).obj ((etaleAbelianInverseImage.{u, 0} V.ι).obj F)
  have hkill : ∀ W : X.Opens, (n : ℤ) • 𝟙 ((etaleAbelianInverseImage.{u, 0} W.ι).obj F) = 0 :=
    fun W => zsmul_id_map_eq_zero _ hF
  have hkillA : (n : ℤ) • 𝟙 A = 0 := zsmul_id_map_eq_zero _ (hkill U)
  have hkillB : (n : ℤ) • 𝟙 B = 0 := zsmul_id_map_eq_zero _ (hkill V)
  have hstmt : ∀ (W : X.Opens) [IsClosedImmersion W.ι],
      CurveTorsionStatementsGeneral.{u, 0} (W.ι ≫ π) ((etaleAbelianInverseImage.{u, 0} W.ι).obj F) →
      CurveTorsionStatementsGeneral.{u, 0} π
        ((etaleAbelianDirectImage.{u, 0} W.ι).obj ((etaleAbelianInverseImage.{u, 0} W.ι).obj F)) :=
    fun W _ => h0A5D W.ι π (hdim W) hX _
      (torsionSheafProperty_of_zsmul_id_eq_zero_general hn (hkill W))
  have hA := hstmt U hFU
  have hB := hstmt V hFV
  have hAB : CurveTorsionStatementsGeneral.{u, 0} π (A ⊞ B) := by
    have hkillAB : (n : ℤ) • 𝟙 (A ⊞ B) = 0 := by
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Preadditive.zsmul_comp, Category.id_comp, ← Category.comp_id biprod.fst,
          ← Preadditive.comp_zsmul, hkillA, Limits.comp_zero, Limits.zero_comp]
      · rw [Preadditive.zsmul_comp, Category.id_comp, ← Category.comp_id biprod.snd,
          ← Preadditive.comp_zsmul, hkillB, Limits.comp_zero, Limits.zero_comp]
    exact h0A5C π hX _ (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
      (torsionSheafProperty_of_zsmul_id_eq_zero_general hn hkillA)
      (torsionSheafProperty_of_zsmul_id_eq_zero_general hn hkillAB)
      (torsionSheafProperty_of_zsmul_id_eq_zero_general hn hkillB) hA hB
  exact hAB.of_iso π (@asIso _ _ _ _ _ (isIso_biprodLift_unit_of_isCompl U V hUV F)).symm

end Stacks.EtaleCohomology

end
