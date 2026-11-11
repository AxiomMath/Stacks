module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCore07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictCrystalDeRham07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictedSiteEvaluation07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SituationRestrict07MW

/-!
# `RΓ(Cris(X/S), F) ≅ RΓ(Y, F_Y ⊗ Ω^•_{Y/S})` in `D⁺(Ab)` in the situation of Tag 07MW

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`): `S` affine, `p` nilpotent
in `Γ(S, 𝒪_S)`, `Y` smooth over `S` with closed fibre `X`, and `A = (X, Y, γ)` the object of part
(1) of the remark.  For a crystal `F` in quasi-coherent modules this file proves that the map of
[Stacks, Equation 07LP]

`RΓ(Cris(X/S), F) ⟶ RΓ(Y, F_Y ⊗ Ω^•_{Y/S, γ})`

(`...SmallSite.crystallineToAmbientDeRham`) is an isomorphism in `D⁺(Ab)`
(`Situation07MW.isIso_crystallineToAmbientDeRham`), with no hypothesis on `X` or `Y` beyond those
of the situation.

## The argument

By `...SmallSite.isIso_crystallineToAmbientDeRham_of_quasiIso` it suffices, for one injective
resolution `φ : F ⊗ Ω^•_{X/S} ⟶ J`, that over every open `W ⊆ X` whose preimage `V ⊆ Y` is
affine the restriction `Γ(W, u_{X/S, *}J) ⟶ Γ(V, J_T)` be a quasi-isomorphism
(`Situation07MW.quasiIso_sections_zariskiDirectImageToAmbient`).  That is reduced to the case
`W = X`, `V = Y` of the affine core
(`...Situation07MW.quasiIso_sections_zariskiDirectImageToAmbient_top`)
for the restricted situation `(p, S|_⊤, W)` with the smooth lifting `V`
(`...Situation07MW.restrictToOpen`):

* the restriction `j⁻¹J` of `J` to `Cris(W/S)` is an injective resolution of the restriction of the
  de Rham complex, which is the de Rham complex of the restricted crystal
  (`...SmallSite.smallExtendCrystalDeRhamIso`), restriction being exact and preserving injectives;
* `Γ(W, u_{X/S, *}J) ≅ Γ(W, u_{W/S, *}j⁻¹J)` compatibly with evaluations, and the object
  `(W, V, γ)` of the restricted situation extends to `A|_V`
  (`...SmallSite.quasiIso_sections_zariskiDirectImageToAmbient_of_restrict`,
  `...Situation07MW.restrictToOpenCrystallineThickeningIso`).

## Main results

* `CochainComplex.exists_homotopyEquiv_of_quasiIso` — two quasi-isomorphisms out of one complex
  into K-injective complexes are related by a homotopy equivalence.
* `...CrystallineThickening.quasiIso_sections_zariskiDirectImageToAmbient_of_homotopyEquiv` — the
  sectionwise condition is invariant under homotopy equivalence of the complex.
* `Situation07MW.quasiIso_sections_zariskiDirectImageToAmbient` and
  `Situation07MW.quasiIso_sections_zariskiDirectImageToAmbient_of_plus` — the sectionwise
  hypothesis of `...SmallSite.isIso_crystallineToAmbientDeRham_of_quasiIso`, for resolutions in
  nonnegative degrees and for all bounded below injective resolutions.
* **`Situation07MW.isIso_crystallineToAmbientDeRham`** — the map of [Stacks, Equation 07LP] is an
  isomorphism.

## What is and is not proved

Everything stated is proved.  The comparison is the map of [Stacks, Equation 07LP] in `D⁺(Ab)`;
its `Γ(S, 𝒪_S)`-linear form, which part (3) of [Stacks, Tag 07MW] asserts, is not treated here.
No tag attribute is placed.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' w'' w''' u

noncomputable section

/-! ### Independence of the injective resolution -/

namespace CochainComplex

/-- **Two quasi-isomorphisms out of one complex into K-injective complexes are related by a
homotopy equivalence** `J ⟶ J₀`: the derived-category map `φ₀ ∘ φ⁻¹` comes from the homotopy
category, `J₀` being K-injective, and a quasi-isomorphism between K-injective complexes is a
homotopy equivalence. -/
theorem exists_homotopyEquiv_of_quasiIso {C : Type*} [Category* C] [Abelian C]
    {K J J₀ : CochainComplex C ℤ} (φ : K ⟶ J) (φ₀ : K ⟶ J₀) [QuasiIso φ] [QuasiIso φ₀]
    [J.IsKInjective] [J₀.IsKInjective] : Nonempty (HomotopyEquiv J J₀) := by
  let := HasDerivedCategory.standard C
  obtain ⟨g', hg'⟩ := (IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj J) J₀).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app J ≫ inv (DerivedCategory.Q.map φ) ≫
        DerivedCategory.Q.map φ₀ ≫ (DerivedCategory.quotientCompQhIso C).inv.app J₀)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g'
  have h1 : IsIso ((HomotopyCategory.quotient C _ ⋙ DerivedCategory.Qh).map g) := by
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g))
    rw [hg']
    infer_instance
  have h2 : IsIso ((HomotopyCategory.quotient C _ ⋙ DerivedCategory.Qh).map g ≫
      (DerivedCategory.quotientCompQhIso C).hom.app J₀) := inferInstance
  rw [(DerivedCategory.quotientCompQhIso C).hom.naturality g] at h2
  have : IsIso (DerivedCategory.Q.map g) :=
    IsIso.of_isIso_comp_left ((DerivedCategory.quotientCompQhIso C).hom.app J) _
  obtain ⟨e, he⟩ := (IsKInjective.quasiIso_iff g).1
    ((DerivedCategory.isIso_Q_map_iff_quasiIso C g).1 this)
  exact ⟨e⟩

end CochainComplex

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

/-- **The sectionwise condition does not depend on the complex up to homotopy equivalence**: if
`J ≃ J₀` and `Γ(W, u_{X/S, *}J₀) ⟶ Γ(h⁻¹(W), (J₀)_T)` is a quasi-isomorphism, so is the same map
for `J`, by naturality and since additive functors preserve homotopy equivalences. -/
theorem quasiIso_sections_zariskiDirectImageToAmbient_of_homotopyEquiv
    {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S) (W : S.X.Opens)
    {J J₀ : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (e : HomotopyEquiv J J₀)
    (h₀ : QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (zariskiDirectImageToAmbient A)
          (ComplexShape.up ℤ)).app J₀))) :
    QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (zariskiDirectImageToAmbient A)
          (ComplexShape.up ℤ)).app J)) := by
  let Γ := (sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj (op W)
  let α := Functor.whiskerRight (zariskiDirectImageToAmbient A) Γ
  change QuasiIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app J₀) at h₀
  change QuasiIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app J)
  have h₁ : QuasiIso (((zariskiDirectImage S ⋙ Γ).mapHomologicalComplex _).map e.hom) :=
    inferInstanceAs (QuasiIso (Γ.mapHomotopyEquiv ((zariskiDirectImage S).mapHomotopyEquiv e)).hom)
  have h₂ : QuasiIso ((Γ.mapHomologicalComplex _).map
      (((ambientPushforward A).mapHomologicalComplex _).map
        (((abelianAmbientRestriction A).mapHomologicalComplex _).map e.hom))) :=
    inferInstanceAs (QuasiIso (Γ.mapHomotopyEquiv ((ambientPushforward A).mapHomotopyEquiv
      ((abelianAmbientRestriction A).mapHomotopyEquiv e))).hom)
  have hsq := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).naturality e.hom
  have h₂' : QuasiIso ((((abelianAmbientRestriction A ⋙ ambientPushforward A) ⋙
      Γ).mapHomologicalComplex _).map e.hom) := h₂
  have : QuasiIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app J ≫
      (((abelianAmbientRestriction A ⋙ ambientPushforward A) ⋙ Γ).mapHomologicalComplex
        _).map e.hom) := by
    rw [← hsq]
    exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₀)
  exact (quasiIso_iff_comp_right _ _).1 this

end Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

/-- **The sectionwise hypothesis of Step 3**: for an injective resolution `φ : F ⊗ Ω^•_{X/S} ⟶ J`
concentrated in nonnegative degrees and an open `W ⊆ X` whose preimage `V = h⁻¹(W)` in `Y` is
affine, the restriction `Γ(W, u_{X/S, *}J) ⟶ Γ(V, J_T)` is a quasi-isomorphism. -/
theorem quasiIso_sections_zariskiDirectImageToAmbient
    {J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (φ : (crystalDeRhamSheafData hF).complex ⟶ J) [QuasiIso φ] [J.IsStrictlyGE 0]
    [∀ n, Injective (J.X n)] (W : S.X.Opens)
    (hV : IsAffineOpen (CrystallineThickening.ambientToXPreimage T.crystallineThickening W)) :
    QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (CrystallineThickening.zariskiDirectImageToAmbient T.crystallineThickening)
          (ComplexShape.up ℤ)).app J)) := by
  let hW := le_sourceToBase_preimage_top W
  let T' := T.restrictToOpen W
  have : IsAffine (restrict S ⊤ W hW).X := T.isAffine_restrict_X W hV
  have : IsAffine (restrict S ⊤ W hW).S.scheme := T'.isAffine
  have : IsAffine T'.Y := T.isAffine_restrictToOpen_Y W hV
  let R := smallExtendAbelianRestriction S ⊤ W hW
  let J' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  have : CochainComplex.IsStrictlyGE J' 0 := (CochainComplex.isStrictlyGE_iff J' 0).2 fun i hi =>
    R.map_isZero ((CochainComplex.isStrictlyGE_iff J 0).1 inferInstance i hi)
  have : ∀ n, Injective (J'.X n) := fun n => inferInstanceAs (Injective (R.obj (J.X n)))
  let hF' := isQuasicoherentOnSite_smallExtendSheafRestriction ⊤ W hW hF
  let ι : (crystalDeRhamSheafData hF').complex ≅
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj (crystalDeRhamSheafData hF).complex :=
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
        (smallExtendCrystalDeRhamIso ⊤ W hW hF).symm ≪≫
      (R.mapHomologicalComplexExtendIso (crystalDeRhamSheafData hF).natComplex
        ComplexShape.embeddingUpNat).symm
  have : R.PreservesHomology := Functor.preservesHomologyOfExact _
  let φ' : (crystalDeRhamSheafData hF').complex ⟶ J' :=
    ι.hom ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  have : QuasiIso φ' := quasiIso_comp _ _
  exact quasiIso_sections_zariskiDirectImageToAmbient_of_restrict S ⊤ W hW
    T.crystallineThickening T'.crystallineThickening
    ((smallExtend S ⊤ W hW).mapIso
        (asIso (T'.crystallineThickening.restrictOpenHom _)) ≪≫
      T.restrictToOpenCrystallineThickeningIso W) J
    (T'.quasiIso_sections_zariskiDirectImageToAmbient_top hF' φ')

/-- **The sectionwise hypothesis of Step 3, for every resolution**: for every quasi-isomorphism
`φ : F ⊗ Ω^•_{X/S} ⟶ J` into a bounded below complex of injective abelian sheaves and every open
`W ⊆ X` whose preimage `V = h⁻¹(W)` in `Y` is affine, the restriction
`Γ(W, u_{X/S, *}J) ⟶ Γ(V, J_T)` is a quasi-isomorphism.  It holds for a resolution concentrated
in nonnegative degrees (`quasiIso_sections_zariskiDirectImageToAmbient`), and any two bounded
below injective resolutions are homotopy equivalent. -/
theorem quasiIso_sections_zariskiDirectImageToAmbient_of_plus
    {J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (φ : (crystalDeRhamSheafData hF).complex ⟶ J) [QuasiIso φ] (hJ : CochainComplex.plus _ J)
    [∀ n, Injective (J.X n)] (W : S.X.Opens)
    (hV : IsAffineOpen (CrystallineThickening.ambientToXPreimage T.crystallineThickening W)) :
    QuasiIso ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (CrystallineThickening.zariskiDirectImageToAmbient T.crystallineThickening)
          (ComplexShape.up ℤ)).app J)) := by
  obtain ⟨J₀, φ₀, hφ₀, hJ₀inj, hJ₀⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (crystalDeRhamSheafData hF).complex 0
  obtain ⟨d, hd⟩ := hJ
  have := hd
  have := hφ₀
  have := hJ₀inj
  have := hJ₀
  have := CochainComplex.isKInjective_of_injective J d
  have := CochainComplex.isKInjective_of_injective J₀ 0
  obtain ⟨e⟩ := CochainComplex.exists_homotopyEquiv_of_quasiIso φ φ₀
  exact CrystallineThickening.quasiIso_sections_zariskiDirectImageToAmbient_of_homotopyEquiv
    _ W e (T.quasiIso_sections_zariskiDirectImageToAmbient hF φ₀ W hV)

/-- The map `X ⟶ X` of the object `(X, Y, γ)` is surjective: it is the identity. -/
theorem surjective_crystallineThickening_toX :
    Function.Surjective T.crystallineThickening.obj.toX :=
  fun x => ⟨x, rfl⟩

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (Opens.grothendieckTopology T.crystallineThickening.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'''} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- **`RΓ(Cris(X/S), F) ≅ RΓ(Y, F_Y ⊗ Ω^•_{Y/S, γ})` in `D⁺(Ab)`.**  In the situation of
[Stacks, Tag 07MW], for a crystal `F` in quasi-coherent modules, the map of
[Stacks, Equation 07LP] from the crystalline cohomology of `F` to the cohomology of the de Rham
complex of `F` on the smooth lifting `Y` is an isomorphism. -/
theorem isIso_crystallineToAmbientDeRham :
    IsIso (crystallineToAmbientDeRham hF T.crystallineThickening) := by
  obtain ⟨J, φ, hφ, hJinj, hJ⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (crystalDeRhamSheafData hF).complex 0
  have := hφ
  have := hJinj
  have := hJ
  exact isIso_crystallineToAmbientDeRham_of_quasiIso hF T.crystallineThickening φ ⟨0, hJ⟩
    T.surjective_crystallineThickening_toX
    fun W hV => T.quasiIso_sections_zariskiDirectImageToAmbient hF φ W hV

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end
