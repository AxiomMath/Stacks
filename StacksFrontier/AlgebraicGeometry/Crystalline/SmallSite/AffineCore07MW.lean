module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechRowLevelProjection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamCechRows07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingBaseChange07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingCrisDeRhamAbelian07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelStabilization07MW

/-!
# `Γ(X, u_{X/S, *}J) ⟶ J(X, Y, γ)` is a quasi-isomorphism when `X`, `S`, `Y` are affine

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`) with `X` and `Y` affine, let
`A = (X, Y, γ)` be the object of part (1) of the remark, `F` a crystal in quasi-coherent modules
with de Rham complex `K = F ⊗ Ω^•_{X/S}` and `φ : K ⟶ J` an injective resolution concentrated in
nonnegative degrees.  This file proves that the restriction of sections

`Γ(X, u_{X/S, *}J^•) ⟶ J^•(A|_Y) = Γ(Y, J^•_T)`

(the transformation `u_{X/S, *} ⟶ h_*((-)_T)` of
`...SmallSite.CrystallineThickening.zariskiDirectImageToAmbient` on sections over `X`) is a
quasi-isomorphism of complexes of abelian groups
(`Situation07MW.quasiIso_sections_zariskiDirectImageToAmbient_top`).

## The argument

Let `T(n)_e` be the system of [Stacks, Tag 07JN] and `ψ : A ⟶ T(0)_e` the morphism of
`...SmallSite.Situation07MW.levelHom`, for a level `e` past the bound of that morphism, with
`p^{N + e} = 0` in the envelope, and past the level at which the tower `T(0)_•` is constant.  The
restriction factors as

`Γ(X, u_*J) ⟶ lim_e J(T(0)_e) ⟶ J(T(0)_e) ⟶ J(A|_Y)`

(restriction to the pro-object, projection to the level `e`, restriction along
`A|_Y ⟶ A ⟶ T(0)_e`), because the value at `A|_Y` of a section of `u_*J` is the restriction of
its value at `T(0)_e`.  The first map is a quasi-isomorphism (Tag 07LG in the form
`...SmallSite.quasiIso_openAugmentationNat_crystalDeRhamSheafData`).  The last two form a square
with the same maps for `K`:

`lim_e K(T(0)_e) ⟶ K(T(0)_e) ⟶ K(A|_Y)`
`      ↓ φ                              ↓ φ`
`lim_e J(T(0)_e) ⟶ J(T(0)_e) ⟶ J(A|_Y)`

whose left map is a quasi-isomorphism (the second half of the same lemma), right map is one
(`Γ(Y, K_T) ⟶ Γ(Y, J_T)`,
`...SmallSite.CrystalDeRhamSheafData.quasiIso_map_sections_abelianAmbientRestriction`),
and top row is one: the projection is an isomorphism past the stable level
(`...SmallSite.isIso_limit_π_wholeSpaceSystem`), restriction along `ψ` is a quasi-isomorphism by
[Stacks, Lemma 60.21.4, Tag 07LH]
(`...SmallSite.Situation07MW.quasiIso_affineDeRhamSectionsMap_levelAffineHom`),
and `A|_Y ⟶ A` is an isomorphism.  Two out of three finishes.

## What is and is not proved

Everything stated is proved, with no hypothesis beyond the affineness of `X` and `Y` (that of `S`
is part of `Situation07MW`).  The resolution is required to be concentrated in nonnegative
degrees, which is how it is produced
(`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective` at `n = 0`).
This is a step towards part (3) of [Stacks, Tag 07MW]; no tag attribute is placed.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

/-! ### Quasi-isomorphisms and the extension of complexes by zero -/

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroObject C]
  [Preadditive D] [HasZeroObject D] [CategoryWithHomology D] {ι ι' : Type*}
  {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')

/-- **A natural transformation applied to an extended complex is a quasi-isomorphism exactly when
it is one on the complex**: applying functors degreewise commutes with the extension by zero. -/
theorem quasiIso_natTrans_app_extend_iff {G H : C ⥤ D} [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] (α : G ⟶ H) (K : HomologicalComplex C c) :
    QuasiIso ((NatTrans.mapHomologicalComplex α c').app (K.extend e)) ↔
      QuasiIso ((NatTrans.mapHomologicalComplex α c).app K) :=
  (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (G.mapHomologicalComplexExtendIso K e) (H.mapHomologicalComplexExtendIso K e)
    (Functor.mapHomologicalComplexExtendIso_hom_naturality K α e).symm)).trans
    (quasiIso_extendMap_iff _ _)

/-- **A functor applied to the extension of a morphism is a quasi-isomorphism exactly when it is
one on the morphism.** -/
theorem quasiIso_map_extendMap_iff (G : C ⥤ D) [G.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    QuasiIso ((G.mapHomologicalComplex c').map (extendMap f e)) ↔
      QuasiIso ((G.mapHomologicalComplex c).map f) :=
  (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (mapHomologicalComplexExtendIso G K e).symm (mapHomologicalComplexExtendIso G L e).symm
    (mapHomologicalComplexExtendIso_inv_naturality G K f e).symm)).trans
    (quasiIso_extendMap_iff _ _)

end HomologicalComplex

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Restriction of sections -/

/-- Restricting sections along a composite is restricting along the second map, then the first. -/
theorem sectionsComplexRestrict_comp
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    {B B' B'' : CrystallineThickening S} (g : B ⟶ B') (h : B' ⟶ B'') :
    sectionsComplexRestrict K (g ≫ h) =
      sectionsComplexRestrict K h ≫ sectionsComplexRestrict K g := by
  ext a : 1
  exact (K.X a).obj.map_comp h.op g.op

/-- Restricting sections along an isomorphism is an isomorphism. -/
instance isIso_sectionsComplexRestrict
    (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)
    {B B' : CrystallineThickening S} (g : B ⟶ B') [IsIso g] :
    IsIso (sectionsComplexRestrict K g) := by
  have : ∀ a, IsIso ((sectionsComplexRestrict K g).f a) := fun a =>
    inferInstanceAs (IsIso ((K.X a).obj.map g.op))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The projection of a Čech row onto a level carries the map of rows induced by `φ` to the map of
sections over that level. -/
theorem cosimplicialRowMap_comp_cechRowLevelProjection
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    {K L : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ L)
    (b e : ℕ) :
    cosimplicialRowMap ((cechCosimplicialComplex T).map φ) b ≫ cechRowLevelProjection T L b e =
      cechRowLevelProjection T K b e ≫
        ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
          (evaluation _ _).obj (op ((T.obj (op ⦋b⦌)).obj e))).mapHomologicalComplex _).map φ := by
  ext a : 1
  exact levelLimitFunctor_map_π (T.obj (op ⦋b⦌)) (φ.f a).hom (op e)

/-- Restriction of sections is natural in the complex. -/
theorem sectionsComplexRestrict_naturality
    {K L : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ L)
    {B B' : CrystallineThickening S} (g : B ⟶ B') :
    ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
          (evaluation _ _).obj (op B')).mapHomologicalComplex _).map φ ≫
        sectionsComplexRestrict L g =
      sectionsComplexRestrict K g ≫
        ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
          (evaluation _ _).obj (op B)).mapHomologicalComplex _).map φ := by
  ext a : 1
  exact ((φ.f a).hom.naturality g.op).symm

/-- The extension by zero of a complex of injective objects is termwise injective. -/
theorem injective_extend_X
    {Jn : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ}
    [∀ a, Injective (Jn.X a)] (n : ℤ) :
    Injective ((Jn.extend ComplexShape.embeddingUpNat).X n) := by
  by_cases hn : ∃ a : ℕ, ComplexShape.embeddingUpNat.f a = n
  · obtain ⟨a, ha⟩ := hn
    exact Injective.of_iso (Jn.extendXIso ComplexShape.embeddingUpNat ha).symm inferInstance
  · simp only [not_exists] at hn
    exact (Jn.isZero_extend_X ComplexShape.embeddingUpNat n hn).injective

namespace Situation07MW

variable [IsAffine S.X] [IsAffine S.S.scheme] (T : Situation07MW S) [IsAffine T.Y]
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

/-- The object `A|_Y` of `Cris(X/S)`: the restriction of `A = (X, Y, γ)` to the preimage `h⁻¹(X)`
of the whole of `X`, which is the whole of `Y`. -/
abbrev ambientTopObject : CrystallineThickening S :=
  T.crystallineThickening.restrictOpen
    (CrystallineThickening.ambientToXPreimage T.crystallineThickening ⊤)

/-- `A|_Y ⟶ A` is an isomorphism, `h⁻¹(X)` being the whole of `Y`. -/
instance isIso_restrictOpenHom_ambientToXPreimage_top :
    IsIso (T.crystallineThickening.restrictOpenHom
      (CrystallineThickening.ambientToXPreimage T.crystallineThickening ⊤)) :=
  CrystallineThickening.isIso_restrictOpenHom_top T.crystallineThickening

/-- **The composite `A|_Y ⟶ A ⟶ T(0)_e`** of the restriction with `ψ`. -/
abbrev ambientLevelHom (e : ℕ) (he : T.levelBound ≤ e) :
    T.ambientTopObject ⟶ levelObj T.primeNilpotentX 0 e :=
  T.crystallineThickening.restrictOpenHom _ ≫ T.levelHom e he

/-- **A level at which everything works**: past the bound of `ψ`, with `p^{N + e} = 0` in the
envelope, and past the level at which the tower of [Stacks, Tag 07JN] is constant. -/
theorem exists_good_level : ∃ e, T.levelBound ≤ e ∧
    ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) : ℕ) :
      wsEnvelope T.primeNilpotentX 0) = 0 ∧
    wholeSpaceStableLevel T.prime_nilpotent ≤ e := by
  obtain ⟨e₀, h⟩ := T.exists_levelBound_pow_eq_zero
  exact ⟨max e₀ (wholeSpaceStableLevel T.prime_nilpotent), (h _ (le_max_left _ _)).1,
    (h _ (le_max_left _ _)).2, le_max_right _ _⟩

/-- **The `K`-side of the square**: projecting `lim_e K(T(0)_e)` to the level `e` and restricting
along `A|_Y ⟶ A ⟶ T(0)_e` is a quasi-isomorphism, for the `ℕ`-indexed de Rham complex `K` of a
crystal in quasi-coherent modules. -/
theorem quasiIso_cechRowLevelProjection_comp_restrict_natComplex (e : ℕ) (he : T.levelBound ≤ e)
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) :
      ℕ) : wsEnvelope T.primeNilpotentX 0) = 0)
    (hs : wholeSpaceStableLevel T.prime_nilpotent ≤ e) :
    QuasiIso (cechRowLevelProjection (wholeSpaceSystem S T.primeNilpotentX)
        (crystalDeRhamSheafData hF).natComplex 0 e ≫
      sectionsComplexRestrict (crystalDeRhamSheafData hF).natComplex (T.ambientLevelHom e he)) := by
  have : IsIso (cechRowLevelProjection (wholeSpaceSystem S T.primeNilpotentX)
      (crystalDeRhamSheafData hF).natComplex 0 e) :=
    isIso_cechRowLevelProjection _ _ 0 e fun a =>
      isIso_limit_π_wholeSpaceSystem T.prime_nilpotent T.primeNilpotentX _ 0 e hs
  have hψ : QuasiIso (sectionsComplexRestrict (crystalDeRhamSheafData hF).natComplex
      (T.levelHom e he)) :=
    quasiIso_natComplex_restriction hF (T.levelAffineHom e he)
      (T.quasiIso_affineDeRhamSectionsMap_levelAffineHom
        ⟨F, hF, isSheafCrystal_of_isQuasicoherentOnSite F hF⟩ e he hpe)
  rw [sectionsComplexRestrict_comp]
  infer_instance

/-- **The `J`-side of the square**: for an injective resolution `φ : K ⟶ J` of the `ℕ`-indexed
de Rham complex, projecting `lim_e J(T(0)_e)` to the level `e` and restricting along
`A|_Y ⟶ A ⟶ T(0)_e` is a quasi-isomorphism. -/
theorem quasiIso_cechRowLevelProjection_comp_restrict
    {Jn : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ}
    (φn : (crystalDeRhamSheafData hF).natComplex ⟶ Jn) [QuasiIso φn] [∀ a, Injective (Jn.X a)]
    (e : ℕ) (he : T.levelBound ≤ e)
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) :
      ℕ) : wsEnvelope T.primeNilpotentX 0) = 0)
    (hs : wholeSpaceStableLevel T.prime_nilpotent ≤ e) :
    QuasiIso (cechRowLevelProjection (wholeSpaceSystem S T.primeNilpotentX) Jn 0 e ≫
      sectionsComplexRestrict Jn (T.ambientLevelHom e he)) := by
  have hrow := (quasiIso_openAugmentationNat_crystalDeRhamSheafData T.prime_nilpotent
    T.primeNilpotentX hF φn).2
  have hK := T.quasiIso_cechRowLevelProjection_comp_restrict_natComplex hF e he hpe hs
  -- `Γ(Y, K_T) ⟶ Γ(Y, J_T)`, from the `ℤ`-indexed statement at the extensions by zero.
  have : ∀ n, Injective ((Jn.extend ComplexShape.embeddingUpNat).X n) := injective_extend_X
  let φ : (crystalDeRhamSheafData hF).complex ⟶ Jn.extend ComplexShape.embeddingUpNat :=
    HomologicalComplex.extendMap φn ComplexShape.embeddingUpNat
  have : QuasiIso φ := (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
  have h2c : QuasiIso ((((sheafSections
      (Opens.grothendieckTopology T.crystallineThickening.obj.thickening.target.scheme)
        AddCommGrpCat.{u + 1}).obj (op (CrystallineThickening.ambientToXPreimage
          T.crystallineThickening ⊤))).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((CrystallineThickening.abelianAmbientRestriction
        T.crystallineThickening).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φn ComplexShape.embeddingUpNat))) :=
    (crystalDeRhamSheafData hF).quasiIso_map_sections_abelianAmbientRestriction
      T.crystallineThickening (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF)
      φ ⟨0, inferInstance⟩ _
      (isAffineOpen_top _)
  have h2c' : QuasiIso (((CrystallineThickening.abelianAmbientRestriction
      T.crystallineThickening ⋙ (sheafSections
        (Opens.grothendieckTopology T.crystallineThickening.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1}).obj (op (CrystallineThickening.ambientToXPreimage
            T.crystallineThickening ⊤))).mapHomologicalComplex (ComplexShape.up ℕ)).map φn) :=
    (HomologicalComplex.quasiIso_map_extendMap_iff ComplexShape.embeddingUpNat _ φn).1 h2c
  have h2c'' : QuasiIso (((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op T.ambientTopObject)).mapHomologicalComplex _).map φn) := h2c'
  have hsq := (cosimplicialRowMap_comp_cechRowLevelProjection _ φn 0 e =≫
      sectionsComplexRestrict Jn (T.ambientLevelHom e he)).trans
    ((Category.assoc _ _ _).trans ((cechRowLevelProjection _ _ 0 e) ≫=
      sectionsComplexRestrict_naturality φn (T.ambientLevelHom e he)))
  rw [Category.assoc] at hsq
  have : QuasiIso (cosimplicialRowMap
      ((cechCosimplicialComplex (wholeSpaceSystem S T.primeNilpotentX)).map φn) 0 ≫
        cechRowLevelProjection (wholeSpaceSystem S T.primeNilpotentX) Jn 0 e ≫
          sectionsComplexRestrict Jn (T.ambientLevelHom e he)) := by
    rw [hsq, ← Category.assoc]
    infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

/-- **The affine core, for `ℕ`-indexed resolutions**: for `X` and `Y` affine and an injective
resolution `φ : K ⟶ J` of the `ℕ`-indexed de Rham complex of a crystal in quasi-coherent modules,
the restriction `Γ(X, u_{X/S, *}J) ⟶ Γ(Y, J_T)` is a quasi-isomorphism. -/
theorem quasiIso_sections_zariskiDirectImageToAmbient_top_nat
    {Jn : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ}
    (φn : (crystalDeRhamSheafData hF).natComplex ⟶ Jn) [QuasiIso φn] [∀ a, Injective (Jn.X a)] :
    QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((NatTrans.mapHomologicalComplex
          (CrystallineThickening.zariskiDirectImageToAmbient T.crystallineThickening)
          (ComplexShape.up ℕ)).app Jn)) := by
  obtain ⟨e, he, hpe, hs⟩ := T.exists_good_level
  have hρ := (quasiIso_openAugmentationNat_crystalDeRhamSheafData T.prime_nilpotent
    T.primeNilpotentX hF φn).1
  have hJ := T.quasiIso_cechRowLevelProjection_comp_restrict hF φn e he hpe hs
  have hfac : ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((NatTrans.mapHomologicalComplex
          (CrystallineThickening.zariskiDirectImageToAmbient T.crystallineThickening)
          (ComplexShape.up ℕ)).app Jn)) =
      (openAugmentationNat (isOpenProCovering_wholeSpaceSystem T.primeNilpotentX) Jn ≫
        cechRowLevelProjection (wholeSpaceSystem S T.primeNilpotentX) Jn 0 e ≫
          sectionsComplexRestrict Jn (T.ambientLevelHom e he) :) := by
    ext a : 1
    change zariskiDirectImageEval S _ (Jn.X a) =
      openAugmentation (isOpenProCovering_wholeSpaceSystem T.primeNilpotentX) (Jn.X a) ≫
        limit.π (((wholeSpaceSystem S T.primeNilpotentX).obj (op ⦋0⦌)).op ⋙ (Jn.X a).obj)
          (op e) ≫ (Jn.X a).obj.map (T.ambientLevelHom e he).op
    rw [← Category.assoc, openAugmentation_π, zariskiDirectImageEval_comp]
  rw [hfac]
  exact quasiIso_comp _ _ (hφ := hρ) (hφ' := hJ)

/-- **The affine core**: for `X` and `Y` affine, a crystal `F` in quasi-coherent modules and an
injective resolution `φ : F ⊗ Ω^•_{X/S} ⟶ J` concentrated in nonnegative degrees, the restriction
`Γ(X, u_{X/S, *}J) ⟶ Γ(h⁻¹(X), J_T) = Γ(Y, J_T)` given by
`...SmallSite.CrystallineThickening.zariskiDirectImageToAmbient` is a quasi-isomorphism.  This is
the hypothesis of `...SmallSite.isIso_crystallineToAmbientDeRham_of_quasiIso` at `W = X`. -/
theorem quasiIso_sections_zariskiDirectImageToAmbient_top
    {J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (φ : (crystalDeRhamSheafData hF).complex ⟶ J) [QuasiIso φ] [J.IsStrictlyGE 0]
    [∀ n, Injective (J.X n)] :
    QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op ⊤)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (CrystallineThickening.zariskiDirectImageToAmbient T.crystallineThickening)
          (ComplexShape.up ℤ)).app J)) := by
  let Γ := (sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj (op ⊤)
  let α := Functor.whiskerRight
    (CrystallineThickening.zariskiDirectImageToAmbient T.crystallineThickening) Γ
  let Jn := J.restriction ComplexShape.embeddingUpNat
  let ε := J.extendRestrictionUpNatIso
  obtain ⟨φn, hφn⟩ := (ComplexShape.embeddingUpNat.extendFunctor _).map_surjective (φ ≫ ε.hom)
  have : QuasiIso (HomologicalComplex.extendMap φn ComplexShape.embeddingUpNat) := by
    change QuasiIso ((ComplexShape.embeddingUpNat.extendFunctor _).map φn)
    rw [hφn]
    exact quasiIso_comp φ ε.hom
  have : QuasiIso φn := (HomologicalComplex.quasiIso_extendMap_iff _ _).1 this
  have : ∀ a, Injective (Jn.X a) := fun a => inferInstanceAs (Injective (J.X _))
  have hn : QuasiIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app Jn) :=
    T.quasiIso_sections_zariskiDirectImageToAmbient_top_nat hF φn
  have hz : QuasiIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
      (Jn.extend ComplexShape.embeddingUpNat)) :=
    (HomologicalComplex.quasiIso_natTrans_app_extend_iff _ α Jn).2 hn
  change QuasiIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app J)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (((zariskiDirectImage S ⋙ Γ).mapHomologicalComplex _).mapIso ε)
    ((((CrystallineThickening.abelianAmbientRestriction T.crystallineThickening ⋙
      CrystallineThickening.ambientPushforward T.crystallineThickening) ⋙ Γ).mapHomologicalComplex
        _).mapIso ε)
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).naturality ε.hom))).2 hz

end Situation07MW

end Crystalline.GlobalCrystallineSituation.SmallSite

end
