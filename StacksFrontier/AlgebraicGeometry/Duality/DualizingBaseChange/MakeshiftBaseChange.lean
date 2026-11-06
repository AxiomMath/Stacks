module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.FibreDualizingCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplex
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.OpenBaseChange

/-!
# Makeshift base change for `f^!`, from the chart description

Let `X' = X ×_Y Y'` be a cartesian square of `AlgebraicGeometry.FTS S`, `S` Noetherian, with
`f : X ⟶ Y` flat, and let `E ∈ D⁺_QCoh(𝒪_Y)` with `Lg^*E` bounded below. [Stacks, Tag 0BZY]
says that `L(g')^*f^!E` and `(f')^!Lg^*E` restrict to isomorphic objects on every affine open
`U' ⊆ X'` mapping into affine opens of `X`, `Y'` and `Y`. This file proves it from the affine
chart descriptions of `f^!` at `E` and of `f'^!` at `Lg^*E` (`Stacks.Duality.upperShriekCharts`,
[Stacks, Tag 0BV2]): `f^!(K)|_U ≅ (p^!ω)~` for every tilde model `ω` of `K` on an affine `V` and
every polynomial presentation `p` of `Γ(Y, V) → Γ(X, U)`.

On the spectra of the affine opens everything is a tilde model: `ω` of `E` on `V`, its base
change `ω ⊗ᴸ Γ(Y', V')` of `Lg^*E` on `V'` and the base change of `p^!ω` of `L(g')^*f^!E` on `U'`
by [Stacks, Tag 08DW] (2), and `q^!(ω ⊗ᴸ Γ(Y', V'))` of `(f')^!Lg^*E` on `U'`. The two models on
`U'` agree by the ring-level
`Dualizing.nonempty_totalDerivedExtensionScalars_upperShriekFunctor_iso_of_isOpenImmersion`, since
`Spec Γ(X', U')` is an open of `Spec(Γ(Y', V') ⊗_{Γ(Y, V)} Γ(X, U))`.

## Main results

* `Stacks.Duality.exists_tensorProduct_ringHom_isOpenImmersion` — the ring map
  `Γ(Y', V') ⊗_{Γ(Y, V)} Γ(X, U) → Γ(X', U')` of a compatible quadruple of affine opens, whose
  spectrum map is an open immersion.
* `Stacks.Duality.nonempty_derivedPullback_fromSpec_derivedPullback_iso` — the derived pullback of
  a tilde model is the tilde model of the derived base change.
* `Stacks.Duality.nonempty_restrict_derivedPullback_upperShriek_iso` — [Stacks, Tag 0BZY].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace Stacks.Duality

/-! ### Tilde models on an affine open, read on its spectrum -/

section SpecForm

variable {Z : Scheme.{u}} {U : Z.Opens} (hU : IsAffineOpen U) (K : DerivedCategory Z.Modules)
  (ω : @DerivedCategory (ModuleCat.{u} Γ(Z, U)) _ _ (HasDerivedCategory.standard _))

/-- A tilde model of `K` on an affine open `U`, read at the locally small model on `U`, is a
tilde model of the derived pullback of `K` to `Spec Γ(Z, U)`. -/
theorem nonempty_derivedPullback_fromSpec_iso
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(Z, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _).obj ω) :
    Nonempty ((derivedPullback hU.fromSpec).obj K ≅
      (tilde.functor Γ(Z, U)).mapDerivedCategory.obj ω) := by
  let A := Γ(Z, U)
  let e' := e ≪≫ Stacks.Injectives.mapDerivedCategoryObjIso (ModuleCat.{u} A)
    (tilde.functor A ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ω
  let d4 : (tilde.functor A ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory ⋙
      (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory ≅
        (tilde.functor A).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCongr (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ hU.restrictIsoSpecCompIso ≪≫ Functor.rightUnitor _)
  exact ⟨((derivedRestrictIsoDerivedPullback hU.fromSpec).app K).symm ≪≫
      ((Functor.mapDerivedCategoryCompIsoOfCompIso
        (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm).app K).symm ≪≫
      (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.mapIso e' ≪≫ d4.app ω⟩

/-- An isomorphism from the derived pullback of `K` to `Spec Γ(Z, U)` with `N` gives one from the
restriction of `K` to `U` to the restriction of `N` along `hU.isoSpec.hom`. -/
private theorem nonempty_restrict_iso_of_iso_derivedPullback_fromSpec
    {N : DerivedCategory (Spec Γ(Z, U)).Modules} (e : (derivedPullback hU.fromSpec).obj K ≅ N) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj N) :=
  let c := Functor.mapDerivedCategoryCompIsoOfCompIso hU.restrictIsoSpecInvCompIso ≪≫
    Functor.mapDerivedCategoryId _
  ⟨(c.app _).symm ≪≫ (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.mapIso
    ((Functor.mapDerivedCategoryCompIsoOfCompIso
      (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm).app K ≪≫
      (derivedRestrictIsoDerivedPullback hU.fromSpec).app K ≪≫ e)⟩

/-- A tilde model of the derived pullback of `K` to `Spec Γ(Z, U)` is a tilde model of `K` on
`U`, read at the locally small model on `U`. -/
theorem nonempty_restrict_iso_of_derivedPullback_fromSpec
    (e : (derivedPullback hU.fromSpec).obj K ≅
      (tilde.functor Γ(Z, U)).mapDerivedCategory.obj ω) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(Z, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _).obj ω) := by
  let A := Γ(Z, U)
  let i₃ := (@Functor.mapDerivedCategoryCompIsoOfCompIso _ _ _ (HasDerivedCategory.standard _) _ _ _ _
    _ _ _ _ (tilde.functor A) _ _ _ (Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _ _ _ _ _
    (Iso.refl _)).app ω
  obtain ⟨i⟩ := nonempty_restrict_iso_of_iso_derivedPullback_fromSpec hU K
    (e ≪≫ (Stacks.Injectives.mapDerivedCategoryObjIso (ModuleCat.{u} A) (tilde.functor A) ω).symm)
  exact ⟨i ≪≫ i₃⟩

/-- A tilde model of `K` on `U` in the sense of `Stacks.Duality.IsTildeModelOnAnyModel`, whose
`D(𝒪_U)` is the standard model, is the same as one read at the locally small model on `U`. -/
theorem isTildeModelOn_iff_nonempty [IsLocallyNoetherian Z] :
    IsTildeModelOnAnyModel K U hU ω ↔
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
        (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
          (tilde.functor Γ(Z, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _).obj
            ω) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let F₂ := tilde.functor Γ(Z, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom
  exact ⟨fun ⟨e⟩ => ⟨((Stacks.Injectives.mapDerivedCategoryTargetModelIso
      U.toScheme.Modules F).app K).symm ≪≫
    (Stacks.Injectives.grothendieckModelEquiv U.toScheme.Modules).functor.mapIso e ≪≫
    (@Stacks.Injectives.mapDerivedCategoryTargetModelIso _ _ _ _ _ _ _
      (HasDerivedCategory.standard _) F₂ _ _ _).app ω⟩, fun ⟨e⟩ =>
    ⟨Stacks.Injectives.isoOfTargetModelIso U.toScheme.Modules F
      (hd₂ := HasDerivedCategory.standard _)
      F₂ K ω e⟩⟩

/-- **A tilde model of a bounded below complex is bounded below**: `H^i(K)|_U` is the associated
sheaf of `H^i(ω)`, and the associated-sheaf functor reflects zero objects. -/
theorem isBoundedBelow_of_tildeModel
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(Z, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _).obj ω)
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    @DerivedCategoryB.IsBoundedBelow _ _ _ (HasDerivedCategory.standard _) ω := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n, fun i hi => ?_⟩
  let M := (@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(Z, U)) _ _
    (HasDerivedCategory.standard _) i).obj ω
  have h₁ : IsZero ((Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde M)) :=
    ((Scheme.Modules.restrictFunctor U.ι).map_isZero (hn i hi)).of_iso
      (homologyRestrictIsoTilde hU e i).symm
  have h₂ : IsZero (tilde M) :=
    ((Scheme.Modules.pullback hU.isoSpec.inv).map_isZero h₁).of_iso
      (((Scheme.Modules.pullbackId _).app (tilde M)).symm ≪≫
        (Scheme.Modules.pullbackCongr hU.isoSpec.inv_hom_id.symm).app (tilde M) ≪≫
        ((Scheme.Modules.pullbackComp hU.isoSpec.inv hU.isoSpec.hom).app (tilde M)).symm)
  rw [IsZero.iff_id_eq_zero]
  refine Functor.map_injective (tilde.functor Γ(Z, U)) ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h₂.eq_of_src _ _

end SpecForm

/-! ### Derived pullback of a tilde model -/

/-- **The derived pullback of a tilde model is the tilde model of the derived base change**, by
[Stacks, Tag 08DW] (2): for `g : Y' ⟶ Y` and affine opens `V' ⊆ g⁻¹(V)`, a tilde model `ω` of `K`
on `Spec Γ(Y, V)` gives the tilde model `ω ⊗ᴸ_{Γ(Y, V)} Γ(Y', V')` of `Lg^*K` on
`Spec Γ(Y', V')`. -/
theorem nonempty_derivedPullback_fromSpec_derivedPullback_iso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {V : Y.Opens} (hV : IsAffineOpen V) {V' : Y'.Opens} (hV' : IsAffineOpen V')
    (hV'V : V' ≤ g ⁻¹ᵁ V) (K : DerivedCategory Y.Modules)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(Y, V)) _ _ (HasDerivedCategory.standard _))
    (e : (derivedPullback hV.fromSpec).obj K ≅ (tilde.functor Γ(Y, V)).mapDerivedCategory.obj ω) :
    Nonempty ((derivedPullback hV'.fromSpec).obj ((derivedPullback g).obj K) ≅
      (tilde.functor Γ(Y', V')).mapDerivedCategory.obj
        (letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
        letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y', V'))
        (totalDerivedExtensionScalars.{u, u, u} (g.appLE V V' hV'V).hom).functor.obj ω)) := by
  let a := g.appLE V V' hV'V
  exact ⟨(derivedPullbackCompIso hV'.fromSpec g).app K ≪≫
    eqToIso (congrArg (fun k => (derivedPullback k).obj K)
      (IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' hV'V).symm) ≪≫
    ((derivedPullbackCompIso (Spec.map a) hV.fromSpec).app K).symm ≪≫
    (derivedPullback (Spec.map a)).mapIso e ≪≫
    (affinePullbackComparison _ _ a).app ω ≪≫
    (tilde.functor Γ(Y', V')).mapDerivedCategory.mapIso
      (totalDerivedExtensionScalarsModelIso a.hom ω).symm⟩

/-! ### The chart of a cartesian square over a compatible quadruple of affine opens -/

/-- **An affine open of the base change lying over affine opens is an open of their fibre
product.** In a cartesian square `X' = X ×_S S'`, let `U' ⊆ X'`, `U ⊆ X`, `V' ⊆ S'`, `V ⊆ S` be
affine opens with `g'(U') ⊆ U`, `f'(U') ⊆ V'`, `f(U) ⊆ V` and `g(V') ⊆ V`, and write
`R = Γ(S, V)`, `A = Γ(X, U)`, `R' = Γ(S', V')`, `B = Γ(X', U')`. Then there is a ring map
`R' ⊗_R A → B` whose spectrum map is an open immersion and which restricts to the maps of
sections induced by `g'` and `f'`. -/
theorem exists_tensorProduct_ringHom_isOpenImmersion {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    {U : X.Opens} {V : S.Opens} {V' : S'.Opens} {U' : X'.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hU' : IsAffineOpen U')
    (hUV : U ≤ f ⁻¹ᵁ V) (hV'V : V' ≤ g ⁻¹ᵁ V) (hU'U : U' ≤ g' ⁻¹ᵁ U) (hU'V' : U' ≤ f' ⁻¹ᵁ V') :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Algebra Γ(S, V) Γ(S', V') := (g.appLE V V' hV'V).hom.toAlgebra
    ∃ e : Γ(S', V') ⊗[Γ(S, V)] Γ(X, U) →+* Γ(X', U'),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom e)) ∧
      e.comp (Algebra.TensorProduct.includeRight :
        Γ(X, U) →ₐ[Γ(S, V)] Γ(S', V') ⊗[Γ(S, V)] Γ(X, U)).toRingHom =
          (g'.appLE U U' hU'U).hom ∧
      e.comp (algebraMap Γ(S', V') (Γ(S', V') ⊗[Γ(S, V)] Γ(X, U))) =
        (f'.appLE V' U' hU'V').hom := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(S', V') := (g.appLE V V' hV'V).hom.toAlgebra
  let ch := BaseChangeChart.ofAffineOpens sq U V V' hU hV hV' hUV hV'V
  let A' := CommRingCat.of (Γ(X, U) ⊗[Γ(S, V)] Γ(S', V'))
  let iL : Γ(X, U) ⟶ A' := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : Γ(S', V') ⟶ A' := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let ι' : Spec A' ⟶ X' := ch.incU'
  have : IsOpenImmersion ι' := BaseChangeChart.isOpenImmersion_incU' sq ch
  have wU : ι' ≫ g' = Spec.map iL ≫ hU.fromSpec := ch.wU'U
  have wV : ι' ≫ f' = Spec.map iR ≫ hV'.fromSpec := ch.wU'V'
  have hrange : Set.range hU'.fromSpec ⊆ Set.range ι' := by
    rw [hU'.range_fromSpec]
    exact fun x' hx' => BaseChangeChart.exists_incU'_ofAffineOpens_eq sq U V V' hU hV hV' hUV
      hV'V x' (hU'U hx') (hU'V' hx')
  let k := IsOpenImmersion.lift ι' hU'.fromSpec hrange
  have hk : k ≫ ι' = hU'.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ ι') := hk ▸ hU'.isOpenImmersion_fromSpec
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k ι'
  let e₀ : A' ⟶ Γ(X', U') := Spec.preimage k
  have he₀ : Spec.map e₀ = k := Spec.map_preimage k
  let c : (Γ(S', V') ⊗[Γ(S, V)] Γ(X, U)) ≃ₐ[Γ(S, V)] (Γ(X, U) ⊗[Γ(S, V)] Γ(S', V')) :=
    Algebra.TensorProduct.comm _ _ _
  let cC : CommRingCat.of (Γ(S', V') ⊗[Γ(S, V)] Γ(X, U)) ⟶ A' :=
    CommRingCat.ofHom c.toRingEquiv.toRingHom
  have key : ∀ {T : Scheme.{u}} {W : T.Opens} (hW : IsAffineOpen W) (m : X' ⟶ T)
      (hm : U' ≤ m ⁻¹ᵁ W) (i : Γ(T, W) ⟶ A'), ι' ≫ m = Spec.map i ≫ hW.fromSpec →
        i ≫ e₀ = m.appLE W U' hm := fun hW m hm i w => by
    apply Spec.map_injective
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, he₀, Category.assoc, ← w, ← Category.assoc,
      hk, IsAffineOpen.SpecMap_appLE_fromSpec m hW hU' hm]
  have h1 := key hU g' hU'U iL wU
  have h2 := key hV' f' hU'V' iR wV
  refine ⟨(cC ≫ e₀).hom, ?_, ?_, ?_⟩
  · have : IsIso cC := c.toRingEquiv.toCommRingCatIso.isIso_hom
    show IsOpenImmersion (Spec.map (cC ≫ e₀))
    rw [Spec.map_comp, he₀]
    infer_instance
  · rw [← h1]
    ext a
    simp [cC, c, iL]
    rfl
  · rw [← h2]
    ext a
    simp [cC, c, iR]

/-- Restriction to an affine open is determined by the derived pullback to its spectrum: an
isomorphism of the derived pullbacks of `K` and `L` along `Spec Γ(Z, U) ⟶ Z` gives one of their
restrictions to `U`. -/
theorem nonempty_restrict_iso_of_derivedPullback_fromSpec_iso {Z : Scheme.{u}} {U : Z.Opens}
    (hU : IsAffineOpen U) {K L : DerivedCategory Z.Modules}
    (e : (derivedPullback hU.fromSpec).obj K ≅ (derivedPullback hU.fromSpec).obj L) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj L) := by
  obtain ⟨i⟩ := nonempty_restrict_iso_of_iso_derivedPullback_fromSpec hU K e
  obtain ⟨j⟩ := nonempty_restrict_iso_of_iso_derivedPullback_fromSpec hU L (Iso.refl _ :
    (derivedPullback hU.fromSpec).obj L ≅ _)
  exact ⟨i ≪≫ j.symm⟩

/-- Upper shriek along presentations of equal ring maps agree. -/
theorem nonempty_upperShriekFunctor_obj_iso_of_eq {R A : Type u} [CommRing R] [CommRing A]
    {φ ψ : R →+* A} (h : φ = ψ) (q : Dualizing.PolynomialPresentation φ)
    (K : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)) :
    Nonempty ((h ▸ q).upperShriekFunctor.{u, u}.obj K ≅ q.upperShriekFunctor.{u, u}.obj K) := by
  subst h
  exact ⟨Iso.refl _⟩

/-! ### Makeshift base change -/

section Makeshift

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]

/-- A scheme of finite type over a Noetherian scheme is locally Noetherian. -/
theorem isLocallyNoetherian_left_of_FTS (X : AlgebraicGeometry.FTS S) :
    IsLocallyNoetherian X.left := by
  have : IsLocallyNoetherian ((Functor.fromPUnit S).obj X.right) :=
    inferInstanceAs (IsLocallyNoetherian S)
  exact LocallyOfFiniteType.isLocallyNoetherian X.hom

attribute [local instance] isLocallyNoetherian_left_of_FTS

/-- **[Stacks, Tag 0BZY] (makeshift base change).** In Situation 48.16.1 let `X' = X ×_Y Y'` be a
cartesian square of `FTS S` with `f` flat, let `E ∈ D⁺_QCoh(𝒪_Y)` with `Lg^*E` bounded below,
and let `j`, `j'` be compactifications computing `f^!` and `f'^!`. For an affine open `U' ⊆ X'`
mapping into affine opens `U ⊆ X`, `V' ⊆ Y'`, `V ⊆ Y` of the square (`g'(U') ⊆ U`,
`f'(U') ⊆ V'`, `f(U) ⊆ V`, `g(V') ⊆ V`), the restrictions to `U'` of `L(g')^*f^!E` and
`(f')^!Lg^*E` are isomorphic.

*The reading of "mapping into affine opens".* The source asks for `U' ⊂ X'` "affine open mapping
into affine opens of `Y`, `Y'`, and `X`", and its proof begins "we immediately reduce to the case
where `X`, `Y`, `Y'`, and `X'` are affine", which needs the four affine opens to form a cartesian
square of affines; so the opens are a compatible quadruple, `f(U) ⊆ V` and `g(V') ⊆ V`. Three
independently chosen affine opens containing the images of `U'` need not form such a square:
`U ∩ f⁻¹(V)` need not be affine (the base `S` is not assumed separated), so no single affine chart
of `f` need contain `g'(U')`.

The proof is the source's: on the charts both sides are the sheaves
associated to the algebraic base change
`Dualizing.nonempty_totalDerivedExtensionScalars_upperShriekFunctor_iso_of_isOpenImmersion`, by
the chart description `Stacks.Duality.upperShriekCharts` of [Stacks, Tag 0BV2]. -/
@[stacks 0BZY]
theorem nonempty_restrict_derivedPullback_upperShriek_iso
    {X X' Y Y' : AlgebraicGeometry.FTS S} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : IsPullback g'.left f'.left f.left g.left) [Flat f.left]
    (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))
    (j' : AlgebraicGeometry.CompactificationOf (Over.mk f'.left))
    (E : quasiCoherentDerivedCategory Y.left) (hE : DerivedCategoryB.IsBoundedBelow E.obj)
    (hE' : DerivedCategoryB.IsBoundedBelow ((quasiCoherentDerivedPullback' g.left).obj E).obj)
    {U' : X'.left.Opens} (hU' : IsAffineOpen U') {U : X.left.Opens} (hU : IsAffineOpen U)
    {V' : Y'.left.Opens} (hV' : IsAffineOpen V') {V : Y.left.Opens} (hV : IsAffineOpen V)
    (hU'U : U' ≤ g'.left ⁻¹ᵁ U) (hU'V' : U' ≤ f'.left ⁻¹ᵁ V') (hUV : U ≤ f.left ⁻¹ᵁ V)
    (hV'V : V' ≤ g.left ⁻¹ᵁ V) :
    Nonempty ((Scheme.Modules.restrictFunctor U'.ι).mapDerivedCategory.obj
        ((quasiCoherentDerivedPullback' g'.left).obj ((upperShriek f j).obj E)).obj ≅
      (Scheme.Modules.restrictFunctor U'.ι).mapDerivedCategory.obj
        ((upperShriek f' j').obj ((quasiCoherentDerivedPullback' g.left).obj E)).obj) := by
  -- A tilde model `ω` of `E` on `V`.
  obtain ⟨ω, hωV⟩ := exists_nonempty_iso_tilde_of_isQuasicoherent (K := E.obj) hV E.2
  have hωT : IsTildeModelOnAnyModel E.obj V hV ω := hωV
  obtain ⟨sV⟩ := nonempty_derivedPullback_fromSpec_iso hV E.obj ω
    ((isTildeModelOn_iff_nonempty hV E.obj ω).1 hωT).some
  -- Its base change `ω'` is a tilde model of `Lg^*E` on `V'`.
  obtain ⟨sV'⟩ := nonempty_derivedPullback_fromSpec_derivedPullback_iso g.left hV hV' hV'V
    E.obj ω sV
  let ω' := (let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y.left, V))
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y'.left, V'))
    (totalDerivedExtensionScalars.{u, u, u} (g.left.appLE V V' hV'V).hom).functor.obj ω)
  obtain ⟨eV'⟩ := nonempty_restrict_iso_of_derivedPullback_fromSpec hV'
    ((quasiCoherentDerivedPullback' g.left).obj E).obj ω' sV'
  -- The two charts on `U'`.
  have := locallyOfFiniteType_left f'
  have := locallyOfFiniteType_left f
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation (f.left.appLE V U hUV).hom
    (f.left.finiteType_appLE hV hU hUV)
  -- The ring-level base change.
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(Y'.left, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(Y.left, V) Γ(Y'.left, V') := (g.left.appLE V V' hV'V).hom.toAlgebra
  obtain ⟨e, he, hc, hd⟩ := exists_tensorProduct_ringHom_isOpenImmersion sq hU hV hV' hU' hUV
    hV'V hU'U hU'V'
  obtain ⟨q⟩ := Dualizing.nonempty_polynomialPresentation
    (e.comp (algebraMap Γ(Y'.left, V') (Γ(Y'.left, V') ⊗[Γ(Y.left, V)] Γ(X.left, U))))
    (hd ▸ (f'.left.finiteType_appLE hV' hU' hU'V'))
  obtain ⟨r⟩ :=
    Dualizing.nonempty_totalDerivedExtensionScalars_upperShriekFunctor_iso_of_isOpenImmersion
      (RingHom.flat_algebraMap_iff.mpr (f.left.flat_appLE hV hU hUV)) p e he q ω
      (isBoundedBelow_of_tildeModel hV' _ ω' eV' hE')
  obtain ⟨rq⟩ := nonempty_upperShriekFunctor_obj_iso_of_eq hd q ω'
  -- `L(g')^*f^!E` on `U'`.
  obtain ⟨eU⟩ := upperShriekCharts f j E hE V hV U hU hUV p ω hωT
  obtain ⟨sU⟩ := nonempty_derivedPullback_fromSpec_iso hU _ _ eU
  obtain ⟨s₁⟩ := nonempty_derivedPullback_fromSpec_derivedPullback_iso g'.left hU hU' hU'U _ _ sU
  -- `(f')^!Lg^*E` on `U'`.
  obtain ⟨eU'⟩ := upperShriekCharts f' j' _ hE' V' hV' U' hU' hU'V' (hd ▸ q) ω'
    ((isTildeModelOn_iff_nonempty hV' _ ω').2 ⟨eV'⟩)
  obtain ⟨s₂⟩ := nonempty_derivedPullback_fromSpec_iso hU' _ _ eU'
  let B := Γ(X'.left, U')
  let t : (let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X.left, U))
      let := HasDerivedCategory.standard (ModuleCat.{u} B)
      (totalDerivedExtensionScalars.{u, u, u} (g'.left.appLE U U' hU'U).hom).functor.obj
        (p.upperShriekFunctor.{u, u}.obj ω)) ≅ (hd ▸ q).upperShriekFunctor.{u, u}.obj ω' :=
    eqToIso (by rw [← hc]) ≪≫ r ≪≫ rq.symm
  exact nonempty_restrict_iso_of_derivedPullback_fromSpec_iso hU'
    (s₁ ≪≫ (tilde.functor B).mapDerivedCategory.mapIso
      ((Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} B)).functor.mapIso t) ≪≫ s₂.symm)

end Makeshift

end Stacks.Duality
