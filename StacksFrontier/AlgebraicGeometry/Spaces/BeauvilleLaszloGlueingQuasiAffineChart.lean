module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlueingTriple
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineAffineSpaceBundleInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineGlueingBundleChain

/-!
# An affine chart of a quasi-affine glueing triple (Stacks 0F9U, steps 1–3)

A glueing triple `(V, V', Y')` with quasi-affine components receives a morphism of triples from
the image of an affine glueable algebraic space `T` over `X` (Stacks 0F9Q), each of whose three
components is, up to isomorphisms of source and target, the algebraic space of a flat, surjective
morphism locally of finite presentation from an affine object of the site to a separated one.

## Main definitions

* `BeauvilleLaszlo.Space.IsSeparatedAffineChart`: a morphism of algebraic spaces which, up to
  isomorphisms of source and target, is the algebraic space of a flat, surjective morphism locally
  of finite presentation from an affine object of the site to a separated one.

## Main results

* `BeauvilleLaszlo.Space.exists_affineGlueable_chart`: a glueing triple with quasi-affine
  components receives a morphism of triples from an affine glueable algebraic space whose three
  components are separated affine charts (Stacks 0F9U, steps 1–3).

## References

* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-! ### Separated affine charts -/

section Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism `φ : X ⟶ Y` of algebraic spaces over `S` is a *separated affine chart* when, up to
isomorphisms of source and target, it is the algebraic space of a morphism `h : E ⟶ V` of the big
fppf site over `S` with `E` affine and `V` separated, whose underlying morphism of schemes is flat,
locally of finite presentation and surjective. -/
def IsSeparatedAffineChart {X Y : AlgebraicSpaces B S hS} (φ : X ⟶ Y) : Prop :=
  ∃ (E V : BigFppfOver B S hS) (eE : X ≅ schemeSpace E) (eV : Y ≅ schemeSpace V) (h : E ⟶ V),
    φ = eE.hom ≫ schemeSpaceMap h ≫ eV.inv ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj E) ∧
        ((BigFppfOver.toScheme B S hS).obj V).IsSeparated ∧
          Flat ((BigFppfOver.toScheme B S hS).map h) ∧
            LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h) ∧
              Surjective ((BigFppfOver.toScheme B S hS).map h)

/-- A separated affine chart stays one after precomposing with an isomorphism. -/
theorem IsSeparatedAffineChart.iso_comp {X X' Y : AlgebraicSpaces B S hS} (i : X' ≅ X)
    {φ : X ⟶ Y} (hφ : IsSeparatedAffineChart φ) : IsSeparatedAffineChart (i.hom ≫ φ) := by
  obtain ⟨E, V, eE, eV, h, rfl, h₁, h₂, h₃, h₄, h₅⟩ := hφ
  exact ⟨E, V, i ≪≫ eE, eV, h, by simp, h₁, h₂, h₃, h₄, h₅⟩

/-- The algebraic space of a composite of morphisms of the site is the composite. -/
theorem schemeSpaceMap_comp {E F G : BigFppfOver B S hS} (a : E ⟶ F) (b : F ⟶ G) :
    schemeSpaceMap (a ≫ b) = schemeSpaceMap a ≫ schemeSpaceMap b :=
  ObjectProperty.hom_ext _ (yoneda.map_comp a b)

end Chart

/-- **Naturality of the comparison between the restriction of a representable algebraic space and
the algebraic space of the base change.** -/
theorem restrictSchemeSpaceIso_hom_naturality {B : BigFppfSite.{u}} {U' U : Scheme.{u}}
    {hU' : B.Contains U'} {hU : B.Contains U} (gU : B.obj hU' ⟶ B.obj hU)
    {A A' : BigFppfOver B U hU} (k : A ⟶ A') :
    schemeSpaceMap ((Over.pullback gU).map k) ≫ (restrictSchemeSpaceIso (gU := gU) A').hom =
      (restrictSchemeSpaceIso (gU := gU) A).hom ≫
        (baseChange B U' U hU' hU gU).map (schemeSpaceMap k) :=
  ObjectProperty.hom_ext _ (OverShriek.restrictYonedaIso_naturality gU k)

/-- The base change of an object of the site with separated underlying scheme, to a separated
base, has separated underlying scheme. -/
theorem isSeparated_toScheme_obj_pullback {B : BigFppfSite.{u}} {S S' : Scheme.{u}}
    {hS : B.Contains S} {hS' : B.Contains S'} (g : B.obj hS' ⟶ B.obj hS)
    (V : BigFppfOver B S hS) [hV : ((BigFppfOver.toScheme B S hS).obj V).IsSeparated]
    [S'.IsSeparated] :
    ((BigFppfOver.toScheme B S' hS').obj ((Over.pullback g).obj V)).IsSeparated := by
  have hpb := AlgebraicGeometry.BigFppfOver.isPullback_toScheme_pullback B S hS g V
  have h0 : IsSeparated (B.inclusion.map V.hom ≫ terminal.from _) := by
    rw [terminal.comp_from]
    exact hV.1
  have h1 : IsSeparated (B.inclusion.map V.hom) :=
    IsSeparated.of_comp (B.inclusion.map V.hom) (terminal.from _)
  have h2 : IsSeparated (B.inclusion.map (pullback.snd V.hom g)) :=
    MorphismProperty.of_isPullback hpb h1
  have h4 : IsSeparated (terminal.from (B.inclusion.obj (B.obj hS'))) := ‹S'.IsSeparated›.1
  have h3 : IsSeparated (B.inclusion.map (pullback.snd V.hom g) ≫
      terminal.from (B.inclusion.obj (B.obj hS'))) := inferInstance
  rw [terminal.comp_from] at h3
  exact ⟨h3⟩

/-- Affine space over the total space of an affine-space bundle is flat, locally of finite
presentation and surjective over the base of the bundle. -/
theorem affineSpace_comp_isAffineSpaceBundle {n m : ℕ} {T V : Scheme.{u}} (p : T ⟶ V)
    (hp : IsAffineSpaceBundle m p) :
    Flat ((𝔸(ULift.{u} (Fin n); T) ↘ T) ≫ p) ∧
      LocallyOfFinitePresentation ((𝔸(ULift.{u} (Fin n); T) ↘ T) ≫ p) ∧
        Surjective ((𝔸(ULift.{u} (Fin n); T) ↘ T) ≫ p) := by
  have : Flat p := hp.flat
  have : LocallyOfFinitePresentation p := hp.locallyOfFinitePresentation
  have : Surjective p := hp.surjective
  have : Flat (𝔸(ULift.{u} (Fin n); T) ↘ T) := flat_affineSpace _ _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### A morphism from the assembled affine triple -/

section Morphism

variable {B : BigFppfSite.{u}} {U' U X' : Scheme.{u}} {hU' : B.Contains U'}
  {hU : B.Contains U} {hX' : B.Contains X'}
  {gU : B.obj hU' ⟶ B.obj hU} {gX' : B.obj hU' ⟶ B.obj hX'}

/-- The identification of the two base changes to `U'` of the representing objects of the outer
components of a triple, read off the triple's structure arrows. -/
noncomputable def outerRestrictionIso (Z : GlueingData B U' U X' hU' hU hX' gU gX')
    {TV : BigFppfOver B U hU} {TY : BigFppfOver B X' hX'}
    (eVs : (overU B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TV)
    (eYs : (overX' B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TY) :
    schemeSpace ((Over.pullback gU).obj TV) ≅ schemeSpace ((Over.pullback gX').obj TY) :=
  have : IsIso Z.obj.left.hom := Z.property.1
  have : IsIso Z.obj.hom := Z.property.2
  restrictSchemeSpaceIso (gU := gU) TV ≪≫ (baseChange B U' U hU' hU gU).mapIso eVs.symm ≪≫
    (asIso Z.obj.left.hom).symm ≪≫ asIso Z.obj.hom ≪≫ (baseChange B U' X' hU' hX' gX').mapIso eYs ≪≫
    (restrictSchemeSpaceIso (gU := gX') TY).symm

/-- **A morphism from the affine triple assembled along a chain to a triple** whose outer
components are represented, given morphisms of the site into the representing objects whose base
changes to `U'` are intertwined by the chain and the identification read off the triple. -/
theorem exists_hom_glueingDataOfRestrictionIso (Z : GlueingData B U' U X' hU' hU hX' gU gX')
    {TV : BigFppfOver B U hU} {TY : BigFppfOver B X' hX'}
    (eVs : (overU B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TV)
    (eYs : (overX' B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TY)
    {A₀ : BigFppfOver B U hU} {A₀' : BigFppfOver B X' hX'}
    (chain : (Over.pullback gU).obj A₀ ≅ (Over.pullback gX').obj A₀')
    (k : A₀ ⟶ TV) (k' : A₀' ⟶ TY)
    (hchain : schemeSpaceMap ((Over.pullback gU).map k) ≫ (outerRestrictionIso Z eVs eYs).hom =
      schemeSpaceMap chain.hom ≫ schemeSpaceMap ((Over.pullback gX').map k')) :
    ∃ c : glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A₀ A₀' chain ⟶ Z,
      (overU B U' U X' hU' hU hX' gU gX').map c =
          eqToHom (overU_glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A₀ A₀' chain) ≫
            schemeSpaceMap k ≫ eVs.inv ∧
        (overX' B U' U X' hU' hU hX' gU gX').map c =
          eqToHom (overX'_glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A₀ A₀' chain) ≫
            schemeSpaceMap k' ≫ eYs.inv ∧
          ∃ _ : IsIso Z.obj.left.hom,
            (overU' B U' U X' hU' hU hX' gU gX').map c =
              eqToHom (overU'_glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A₀ A₀'
                chain) ≫ schemeSpaceMap ((Over.pullback gU).map k) ≫
                ((restrictSchemeSpaceIso (gU := gU) TV).hom ≫
                  (baseChange B U' U hU' hU gU).map eVs.inv ≫ inv Z.obj.left.hom) := by
  have hZl : IsIso Z.obj.left.hom := Z.property.1
  have : IsIso Z.obj.hom := Z.property.2
  let cU : schemeSpace A₀ ⟶ (overU B U' U X' hU' hU hX' gU gX').obj Z := schemeSpaceMap k ≫ eVs.inv
  let cX : schemeSpace A₀' ⟶ (overX' B U' U X' hU' hU hX' gU gX').obj Z :=
    schemeSpaceMap k' ≫ eYs.inv
  let cM : schemeSpace ((Over.pullback gU).obj A₀) ⟶
      (overU' B U' U X' hU' hU hX' gU gX').obj Z :=
    schemeSpaceMap ((Over.pullback gU).map k) ≫
      ((restrictSchemeSpaceIso (gU := gU) TV).hom ≫ (baseChange B U' U hU' hU gU).map eVs.inv ≫
        inv Z.obj.left.hom)
  have hwU : cM ≫ Z.obj.left.hom =
      (restrictSchemeSpaceIso (gU := gU) A₀).hom ≫ (baseChange B U' U hU' hU gU).map cU := by
    simp only [cM, cU, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Functor.map_comp]
    rw [← Category.assoc, restrictSchemeSpaceIso_hom_naturality, Category.assoc]
  have hwX : cM ≫ Z.obj.hom = (schemeSpaceMap chain.hom ≫
      (restrictSchemeSpaceIso (gU := gX') A₀').hom) ≫ (baseChange B U' X' hU' hX' gX').map cX := by
    have h1 : (restrictSchemeSpaceIso (gU := gU) TV).hom ≫
        (baseChange B U' U hU' hU gU).map eVs.inv ≫ inv Z.obj.left.hom ≫ Z.obj.hom =
          (outerRestrictionIso Z eVs eYs).hom ≫ (restrictSchemeSpaceIso (gU := gX') TY).hom ≫
            (baseChange B U' X' hU' hX' gX').map eYs.inv := by
      simp only [outerRestrictionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        asIso_hom, asIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
    calc cM ≫ Z.obj.hom
        = schemeSpaceMap ((Over.pullback gU).map k) ≫ ((restrictSchemeSpaceIso (gU := gU) TV).hom ≫
            (baseChange B U' U hU' hU gU).map eVs.inv ≫ inv Z.obj.left.hom ≫ Z.obj.hom) := by
          simp only [cM, Category.assoc]
      _ = (schemeSpaceMap ((Over.pullback gU).map k) ≫ (outerRestrictionIso Z eVs eYs).hom) ≫
            (restrictSchemeSpaceIso (gU := gX') TY).hom ≫
              (baseChange B U' X' hU' hX' gX').map eYs.inv := by
          rw [h1, Category.assoc]
      _ = schemeSpaceMap chain.hom ≫ (schemeSpaceMap ((Over.pullback gX').map k') ≫
            (restrictSchemeSpaceIso (gU := gX') TY).hom) ≫
              (baseChange B U' X' hU' hX' gX').map eYs.inv := by
          rw [hchain, Category.assoc, Category.assoc]
      _ = _ := by
          rw [restrictSchemeSpaceIso_hom_naturality gX' k']
          simp only [cX, Functor.map_comp, Category.assoc]
  exact ⟨ObjectProperty.homMk
    { left := { left := cM, right := cU, w := hwU }
      right := cX
      w := hwX },
    (Category.id_comp _).symm, (Category.id_comp _).symm, hZl, (Category.id_comp _).symm⟩

end Morphism

/-- A separated affine chart, recognised from an explicit description of the morphism. -/
theorem isSeparatedAffineChart_of_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} {E V : BigFppfOver B S hS} (φ : X ⟶ Y)
    (hX : X = schemeSpace E) (eV : Y ≅ schemeSpace V) (k : E ⟶ V)
    (hφ : φ = eqToHom hX ≫ schemeSpaceMap k ≫ eV.inv)
    (hE : IsAffine ((BigFppfOver.toScheme B S hS).obj E))
    (hV : ((BigFppfOver.toScheme B S hS).obj V).IsSeparated)
    (hk : Flat ((BigFppfOver.toScheme B S hS).map k) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map k)) :
    IsSeparatedAffineChart φ :=
  ⟨E, V, eqToIso hX, eV, k, hφ, hE, hV, hk.1, hk.2.1, hk.2.2⟩

/-! ### The data of the chart -/

section Data

variable {B : BigFppfSite.{u}} {U' U X' : Scheme.{u}} {hU' : B.Contains U'}
  {hU : B.Contains U} {hX' : B.Contains X'}
  {gU : B.obj hU' ⟶ B.obj hU} {gX' : B.obj hU' ⟶ B.obj hX'}

/-- **Stacks 0F9U, steps 1–2.** For a cartesian glueing triple `Z` with quasi-affine components
over a square whose two arrows out of `U'` are affine, with `U'` separated: the two outer
components are represented by separated objects `TV`, `TY`, and there are affine objects `A₀` over
`U` and `A₀'` over `X'` (the affine spaces over the bundles of Stacks 0F82), flat surjective
morphisms `k : A₀ ⟶ TV` and `k' : A₀' ⟶ TY` locally of finite presentation, and an identification
`chain` of the base changes of `A₀` and `A₀'` to `U'` intertwining `k` and `k'` with the
identification of the base changes of `TV` and `TY` read off the triple. -/
theorem exists_chart_data (Z : GlueingData B U' U X' hU' hU hX' gU gX')
    (hZ : quasiAffineComponents B U' U X' hU' hU hX' gU gX' Z)
    (hgU : IsAffineHom (B.inclusion.map gU)) (hgX' : IsAffineHom (B.inclusion.map gX')) :
    ∃ (TV : BigFppfOver B U hU) (TY : BigFppfOver B X' hX')
      (eVs : (overU B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TV)
      (eYs : (overX' B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TY)
      (A₀ : BigFppfOver B U hU) (A₀' : BigFppfOver B X' hX')
      (chain : (Over.pullback gU).obj A₀ ≅ (Over.pullback gX').obj A₀')
      (k : A₀ ⟶ TV) (k' : A₀' ⟶ TY),
      schemeSpaceMap ((Over.pullback gU).map k) ≫ (outerRestrictionIso Z eVs eYs).hom =
          schemeSpaceMap chain.hom ≫ schemeSpaceMap ((Over.pullback gX').map k') ∧
        IsAffine ((BigFppfOver.toScheme B U hU).obj A₀) ∧
        IsAffine ((BigFppfOver.toScheme B X' hX').obj A₀') ∧
        ((BigFppfOver.toScheme B U hU).obj TV).IsSeparated ∧
        ((BigFppfOver.toScheme B X' hX').obj TY).IsSeparated ∧
        (Flat ((BigFppfOver.toScheme B U hU).map k) ∧
          LocallyOfFinitePresentation ((BigFppfOver.toScheme B U hU).map k) ∧
            Surjective ((BigFppfOver.toScheme B U hU).map k)) ∧
        (Flat ((BigFppfOver.toScheme B X' hX').map k') ∧
          LocallyOfFinitePresentation ((BigFppfOver.toScheme B X' hX').map k') ∧
            Surjective ((BigFppfOver.toScheme B X' hX').map k')) := by
  let TsU := BigFppfOver.toScheme B U hU
  let TsX := BigFppfOver.toScheme B X' hX'
  let TsM := BigFppfOver.toScheme B U' hU'
  obtain ⟨TV, hTVqa, ⟨eV⟩⟩ := hZ.1
  obtain ⟨TY, hTYqa, ⟨eY⟩⟩ := hZ.2.2
  have : (TsU.obj TV).IsQuasiAffine := hTVqa
  have : (TsX.obj TY).IsQuasiAffine := hTYqa
  obtain ⟨n₁, T₁s, hT₁aff, hT₁c, p₁s, -, hp₁s⟩ :=
    exists_contains_affine_pullback_iso_affineSpace B (TsU.obj TV) TV.left.2
  obtain ⟨n', T's, hT'aff, hT'c, q's, -, hq's⟩ :=
    exists_contains_affine_pullback_iso_affineSpace B (TsX.obj TY) TY.left.2
  let T₁ : BigFppfOver B U hU := BigFppfOver.mk B U hU hT₁c (p₁s ≫ B.inclusion.map TV.hom)
  let T' : BigFppfOver B X' hX' := BigFppfOver.mk B X' hX' hT'c (q's ≫ B.inclusion.map TY.hom)
  let p₁ : T₁ ⟶ TV := BigFppfOver.homOfCompEq B U hU (T := T₁) (W := TV) p₁s rfl
  let q' : T' ⟶ TY := BigFppfOver.homOfCompEq B X' hX' (T := T') (W := TY) q's rfl
  have hp₁ : TsU.map p₁ = p₁s := BigFppfOver.toScheme_map_homOfCompEq B U hU _ _
  have hq' : TsX.map q' = q's := BigFppfOver.toScheme_map_homOfCompEq B X' hX' _ _
  have hT₁ : IsAffine (TsU.obj T₁) := hT₁aff
  have hT' : IsAffine (TsX.obj T') := hT'aff
  have hp₁b : IsAffineSpaceBundle n₁ (TsU.map p₁) := by rwa [hp₁]
  have hq'b : IsAffineSpaceBundle n' (TsX.map q') := by rwa [hq']
  let eVs : (overU B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TV :=
    ObjectProperty.isoMk _ eV
  let eYs : (overX' B U' U X' hU' hU hX' gU gX').obj Z ≅ schemeSpace TY :=
    ObjectProperty.isoMk _ eY
  let Ψ := outerRestrictionIso Z eVs eYs
  let ψ : (Over.pullback gU).obj TV ≅ (Over.pullback gX').obj TY :=
    Yoneda.fullyFaithful.preimageIso ((ObjectProperty.ι _).mapIso Ψ)
  have hΨ : Ψ.hom = schemeSpaceMap ψ.hom :=
    ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _).symm
  clear_value ψ
  have hL : IsAffine (TsM.obj ((Over.pullback gU).obj T₁)) :=
    BigFppfOver.isAffine_toScheme_obj_pullback B U U' hU hU' gU hgU T₁ hT₁
  have hR : IsAffine (TsM.obj ((Over.pullback gX').obj T')) :=
    BigFppfOver.isAffine_toScheme_obj_pullback B X' U' hX' hU' gX' hgX' T' hT'
  obtain ⟨chain, hchain⟩ := BigFppfOver.exists_affineSpace_chain B gU gX' ψ p₁ q' hL hR
    hp₁b hq'b
  let k := BigFppfOver.affineSpaceProj B U hU n' T₁ ≫ p₁
  let k' := BigFppfOver.affineSpaceProj B X' hX' n₁ T' ≫ q'
  have hk : TsU.map k = (𝔸(ULift.{u} (Fin n'); TsU.obj T₁) ↘ TsU.obj T₁) ≫ p₁s := by
    rw [Functor.map_comp, hp₁]
    rfl
  have hk' : TsX.map k' = (𝔸(ULift.{u} (Fin n₁); TsX.obj T') ↘ TsX.obj T') ≫ q's := by
    rw [Functor.map_comp, hq']
    rfl
  refine ⟨TV, TY, eVs, eYs, _, _, chain, k, k', ?_,
    BigFppfOver.isAffine_affineSpace B U hU n' T₁ hT₁,
    BigFppfOver.isAffine_affineSpace B X' hX' n₁ T' hT', inferInstance, inferInstance,
    by rw [hk]; exact affineSpace_comp_isAffineSpaceBundle (n := n') p₁s hp₁s,
    by rw [hk']; exact affineSpace_comp_isAffineSpaceBundle (n := n₁) q's hq's⟩
  change schemeSpaceMap ((Over.pullback gU).map k) ≫ Ψ.hom = _
  rw [hΨ, ← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hchain]

end Data

/-! ### The chart -/

section Canonical

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R')))
  (hX : B.Contains (Spec (.of R)))
  (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)

/-- **Stacks 0F9U, steps 1–3: an affine chart of a quasi-affine triple.** Let `(g : R → R', f)`
be a glueing pair and `Z` a cartesian glueing triple over the canonical square whose three
components are quasi-affine. Then there are an affine algebraic space `T` over `X = Spec R`,
glueable for `(g, f)`, and a morphism of triples from the image of `T` under the gluing functor
of Stacks 0F9N to `Z`, each of whose three components is a separated affine chart. -/
theorem exists_affineGlueable_chart (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (Z : GlueingData B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (canGU g f B hU' hU) (canGX' g f B hU' hX'))
    (hZ : quasiAffineComponents B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (canGU g f B hU' hU) (canGX' g f B hU' hX') Z) :
    ∃ (T : AlgebraicSpaces B (Spec (.of R)) hX)
      (q : (canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.obj T ⟶ Z),
      AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1 ∧
        AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX T ∧
          IsSeparatedAffineChart ((overU B _ _ _ hU' hU hX' _ _).map q) ∧
            IsSeparatedAffineChart ((overU' B _ _ _ hU' hU hX' _ _).map q) ∧
              IsSeparatedAffineChart ((overX' B _ _ _ hU' hU hX' _ _).map q) := by
  have : IsAffine (B.inclusion.obj (B.obj hU')) :=
    inferInstanceAs (IsAffine (Spec (.of (Localization.Away (g f)))))
  have : IsAffine (B.inclusion.obj (B.obj hU)) :=
    inferInstanceAs (IsAffine (Spec (.of (Localization.Away f))))
  have : IsAffine (B.inclusion.obj (B.obj hX')) := inferInstanceAs (IsAffine (Spec (.of R')))
  have hgU : IsAffineHom (B.inclusion.map (canGU g f B hU' hU)) := inferInstance
  have hgX' : IsAffineHom (B.inclusion.map (canGX' g f B hU' hX')) := inferInstance
  obtain ⟨TV, TY, eVs, eYs, A₀, A₀', chain, k, k', hchain, hA₀, hA₀', hTV, hTY, hk, hk'⟩ :=
    exists_chart_data Z hZ hgU hgX'
  obtain ⟨c, hcU, hcX, hZl, hcM⟩ := exists_hom_glueingDataOfRestrictionIso Z eVs eYs chain k k'
    hchain
  have hD := affineComponents_glueingDataOfRestrictionIso_of_isAffineHom B _ _ _ hU' hU hX'
    _ _ A₀ A₀' chain hgU hA₀ hA₀'
  obtain ⟨T, hTa, hTg, ⟨e⟩⟩ := exists_affineGlueable_iso_of_affineComponents g f B hU' hU hX'
    hX hcomm hglue _ hD
  refine ⟨T, e.hom ≫ c, hTa, hTg, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]
    exact IsSeparatedAffineChart.iso_comp (Functor.mapIso _ e)
      (isSeparatedAffineChart_of_eq _ _ eVs k hcU hA₀ hTV hk)
  · rw [Functor.map_comp]
    have : (Spec (.of (Localization.Away (g f)))).IsSeparated := inferInstance
    exact IsSeparatedAffineChart.iso_comp (Functor.mapIso _ e)
      (isSeparatedAffineChart_of_eq _ _ (((restrictSchemeSpaceIso (gU := canGU g f B hU' hU) TV) ≪≫
        (baseChange _ _ _ hU' hU _).mapIso eVs.symm ≪≫ (asIso Z.obj.left.hom).symm).symm)
        ((Over.pullback (canGU g f B hU' hU)).map k) hcM
        (BigFppfOver.isAffine_toScheme_obj_pullback B _ _ hU hU' _ hgU A₀ hA₀)
        (isSeparated_toScheme_obj_pullback _ TV)
        (have hsq := AlgebraicGeometry.BigFppfOver.isPullback_toScheme_pullback_map B _ hU
          (canGU g f B hU' hU) k
        ⟨MorphismProperty.of_isPullback hsq.flip hk.1,
          MorphismProperty.of_isPullback hsq.flip hk.2.1,
          MorphismProperty.of_isPullback hsq.flip hk.2.2⟩))
  · rw [Functor.map_comp]
    exact IsSeparatedAffineChart.iso_comp (Functor.mapIso _ e)
      (isSeparatedAffineChart_of_eq _ _ eYs k' hcX hA₀' hTY hk')

end Canonical

end BeauvilleLaszlo.Space

end
