module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechReindex
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.LocalizedPresheafVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechPullback07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisModuleInverseImageValues
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StandardCoverAcyclicity

/-!
# The higher cohomology of `f_cris^*ℱ` over objects mapping to `Cris(X'/S')`

Let `f : X/S ⟶ X'/S'` be a morphism of global crystalline situations (`fS : S ⟶ S'` on the divided
power bases, `fX : X ⟶ X'`), and let `ℱ` be a locally quasi-coherent crystal on `Cris(X'/S')`.
Write `ℱ' = f_cris^*ℱ` for the module pullback of the universe lift of `ℱ`, an abelian sheaf on
`Cris(X/S)` at the coefficient universe `u + 1`.  This file proves

`H^p(Cris(X/S)/A', ℱ') = 0`,  `p > 0`,

for every object `A'` of `Cris(X/S)` with affine ambient scheme which admits a morphism
`τ : f_CRIS(A') ⟶ A` to an object `A` of `Cris(X'/S')` with affine ambient scheme
(`isZero_overCohomology_crisModuleInverseImage07Q9`).  As a consequence the comparison of
[Stacks, Tag 0133] used for the local step of [Stacks, Tag 07Q9] applies to `ℱ'` along every
system of thickenings of `Cris(X/S)` which maps to a system of `Cris(X'/S')` with affine levels
(`vanishingOnLevels07Q9_crisModuleInverseImage`).

## The argument

It is the argument of [Stacks, Tag 07JJ], with the class of objects of affine ambient scheme
replaced by the class `crisInverseImageAffineObjects07Q9` of those which in addition admit a map
to an object of `Cris(X'/S')` of affine ambient scheme.  That class is closed under passage to
any object with affine ambient scheme mapping to one of its members — in particular under
restriction to basic opens and under the finite fibre products of a standard restriction cover —
so the Čech criterion `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero`
([Stacks, Tag 03F9]) applies to it with the standard restriction covers.  The Čech vanishing on
such a cover of `A'` is computed on the Zariski site of the ambient scheme `T` of `A'`: there the
restriction of `ℱ'` receives the map `tauToSheaf` from the base-change presheaf
`W ↦ Γ(W, 𝒪_T) ⊗_{Γ(A, 𝒪)} ℱ(A)`, bijective over every affine open of `T`
(`bijective_tauToSheaf_app_of_isAffineOpen07Q9`), and the base-change presheaf localizes on the
basic opens of `T`.  So the Čech complex is the algebraic Čech complex of a family generating the
unit ideal of `Γ(T, 𝒪_T)` with coefficients in `Γ(T, 𝒪_T) ⊗_{Γ(A, 𝒪)} ℱ(A)`, which is exact in
positive degrees (`Stacks.Cohomology.Cech.exactAt_cechComplex_of_isLocalizedModule`).

## Main definitions

* `crisInverseImageRestrictOpenComparison07Q9` — the identification of the restriction of
  `i_!ℱ` to the ambient scheme of `f_CRIS(A')` with the restriction of `ℱ'` to the ambient scheme
  of `A'`, the two differing only by the bracketing of the structure maps.
* `crisInverseImageAffineObjects07Q9` — the class of objects the criterion is run on.

## Main results

* `exactAt_cechComplex_crisInverseImage07Q9` — the Zariski Čech vanishing.
* `isZero_overCohomology_crisModuleInverseImage07Q9` — the vanishing of the higher cohomology.
* `vanishingOnLevels07Q9_crisModuleInverseImage` — the vanishing at the levels of a system of
  thickenings mapping to a system with affine levels.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

/-- The inverse of the comparison `changeBaseRestrictOpenHom`, whose two components are
identities. -/
noncomputable def changeBaseRestrictOpenInv07Q9 (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    ((changeBase S S' f g h).obj A).restrictOpen V ⟶
      (changeBase S S' f g h).obj (A.restrictOpen V) where
  sourceHom := 𝟙 _
  targetHom := 𝟙 _
  immersion_naturality := (Category.comp_id _).trans (Category.id_comp _).symm
  base_naturality := (Category.id_comp _).trans (Category.assoc _ _ _)
  toX_naturality := (Category.id_comp _).trans (Category.assoc _ _ _)

/-- `changeBaseRestrictOpenHom` is an isomorphism, with inverse
`changeBaseRestrictOpenInv07Q9`. -/
instance isIso_changeBaseRestrictOpenHom07Q9 (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    IsIso (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A V) :=
  ⟨changeBaseRestrictOpenInv07Q9 A V,
    Thickening.Hom.ext (Category.comp_id _) (Category.comp_id _),
    Thickening.Hom.ext (Category.comp_id _) (Category.comp_id _)⟩

/-- **`changeBaseRestrictOpenHom` is natural in the open**: restricting after change of base and
before are compatible with the transition morphisms between nested opens. -/
theorem changeBaseRestrictOpenHom_restrictOpenLE07Q9 (A : Thickening S)
    {W W' : A.thickening.target.scheme.Opens} (hle : W ≤ W') :
    changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A W ≫
        ((changeBase S S' f g h).obj A).restrictOpenLE hle =
      (changeBase S S' f g h).map (A.restrictOpenLE hle) ≫ changeBaseRestrictOpenHom A W' :=
  Thickening.Hom.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

namespace SmallSite

/-! ### `tauToSheaf` over an affine open -/

section TauAffine

variable (F : SheafOfModules.{u} (structureSheaf S)) {B : Thickening S}
  {A : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A)
  [IsAffine A.obj.thickening.target.scheme]
  (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F)

include hF hcrys in
/-- **Over an affine open `V` of the ambient scheme of `B`, the comparison `tauToSheaf` is
bijective on sections**: it and the universe lift of the sheafification unit of the base-change
presheaf are two locally bijective morphisms out of one presheaf into two Zariski sheaves, and
the latter is bijective over the affine `V`.  This is `bijective_tauToSheaf_app_top` with `⊤`
replaced by any affine open. -/
theorem bijective_tauToSheaf_app_of_isAffineOpen07Q9 {V : B.thickening.target.scheme.Opens}
    (hV : IsAffineOpen V) :
    Function.Bijective (ConcreteCategory.hom ((tauToSheaf F τ).app (op V))) := by
  have := isLocallyInjective_tauToSheaf F τ hF hcrys
  have := isLocallySurjective_tauToSheaf F τ hF hcrys
  have hZ₁ : Presheaf.IsSheaf (Opens.grothendieckTopology B.thickening.target.scheme)
      (sheafify (Opens.grothendieckTopology B.thickening.target.scheme)
        (tauPresheaf F τ).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _
      ((presheafToSheaf (Opens.grothendieckTopology B.thickening.target.scheme) _).obj
        (tauPresheaf F τ).presheaf).property
  have hZ₂ := isSheaf_restrictOpenFunctorBig B
    ((moduleLowerShriek S).obj ((moduleULift S).obj F)).isSheaf
  have hb := Stacks.AlgebraicGeometry.BaseChangePresheaf.bijective_toSheafify_basePresheaf_app
    (tauRing τ) (sectionsOver F A) hV
  refine bijective_app_of_isLocallyBijective hZ₁ hZ₂
    (Functor.whiskerRight (toSheafify (Opens.grothendieckTopology B.thickening.target.scheme)
      (tauPresheaf F τ).presheaf) AddCommGrpCat.uliftFunctor.{u + 1, u}) (tauToSheaf F τ) _ ?_
  refine ⟨fun x y hxy ↦ ULift.ext (hb.1 (congrArg ULift.down hxy)), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hb.2 y.down
  exact ⟨ULift.up x, ULift.ext hx⟩

end TauAffine

/-! ### The restriction of `f_cris^*ℱ` to the ambient scheme of an object -/

variable (f g h)

/-- The restriction maps of the underlying abelian presheaf of `f_cris^*M` along a morphism `k` of
`Cris(X/S)` are those of `i_!M` along `f_CRIS(k)`, on elements. -/
theorem crisModuleInverseImage_obj_map_apply07Q9 (M : ModuleSheaf S')
    {A₁ A₂ : CrystallineThickening S} (k : A₁ ⟶ A₂)
    (x : ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj M)).obj.obj (op A₂)) :
    ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj M)).obj.map k.op x =
      ((moduleLowerShriek S').obj M).val.presheaf.map
        ((changeBase S S' f g h).map ((CrystallineThickening.ι S).map k)).op x :=
  rfl

/-- The naturality square of `crisInverseImageRestrictOpenComparison07Q9`, on `i_!M`. -/
theorem crisInverseImageRestrictOpenComparison07Q9_naturality (M : ModuleSheaf S')
    (A' : Thickening S) {W W' : A'.thickening.target.scheme.Opens} (hle : W' ≤ W) :
    ((moduleLowerShriek S').obj M).val.presheaf.map
        (((changeBase S S' f g h).obj A').restrictOpenLE hle).op ≫
      ((moduleLowerShriek S').obj M).val.presheaf.map
        (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A' W').op =
    ((moduleLowerShriek S').obj M).val.presheaf.map
        (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A' W).op ≫
      ((moduleLowerShriek S').obj M).val.presheaf.map
        ((changeBase S S' f g h).map (A'.restrictOpenLE hle)).op := by
  have key := changeBaseRestrictOpenHom_restrictOpenLE07Q9 (f := f) (g := g) (h := h) A' hle
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, key]

/-- **The restriction of `i_!M` to the ambient scheme of `f_CRIS(A')` is the restriction of
`f_cris^*M` to the ambient scheme of `A'`.**  Over an open `W` the first takes the sections of
`i_!M` over `f_CRIS(A')|_W`, the second over `f_CRIS(A'|_W)`; the two objects differ only by the
bracketing of the structure maps, and the comparison is `changeBaseRestrictOpenHom`. -/
def crisInverseImageRestrictOpenComparison07Q9 (M : ModuleSheaf S')
    (A' : CrystallineThickening S) :
    ((changeBase S S' f g h).obj ((CrystallineThickening.ι S).obj A')).restrictOpenFunctor.op ⋙
        ((moduleLowerShriek S').obj M).val.presheaf ⟶
      (CrystallineThickening.restrictOpenFunctor A').op ⋙
        ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj M)).obj where
  app W := ((moduleLowerShriek S').obj M).val.presheaf.map
    (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A'.obj
      (show A'.obj.thickening.target.scheme.Opens from W.unop)).op
  naturality {W W'} i := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    have hle : (show A'.obj.thickening.target.scheme.Opens from W'.unop) ≤
        (show A'.obj.thickening.target.scheme.Opens from W.unop) := leOfHom i.unop
    change ((moduleLowerShriek S').obj M).val.presheaf.map
        (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A'.obj _).op
        (((moduleLowerShriek S').obj M).val.presheaf.map
          (((changeBase S S' f g h).obj A'.obj).restrictOpenLE hle).op x) =
      ((moduleLowerShriek S').obj M).val.presheaf.map
        ((changeBase S S' f g h).map (A'.obj.restrictOpenLE hle)).op
        (((moduleLowerShriek S').obj M).val.presheaf.map
          (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A'.obj _).op x)
    exact (ConcreteCategory.comp_apply _ _ x).symm.trans
      ((ConcreteCategory.congr_hom
        (crisInverseImageRestrictOpenComparison07Q9_naturality f g h M A'.obj hle) x).trans
        (ConcreteCategory.comp_apply _ _ x))

/-- The components of `crisInverseImageRestrictOpenComparison07Q9` are bijective. -/
theorem bijective_crisInverseImageRestrictOpenComparison07Q9_app (M : ModuleSheaf S')
    (A' : CrystallineThickening S) (W : (A'.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    Function.Bijective (ConcreteCategory.hom
      ((crisInverseImageRestrictOpenComparison07Q9 f g h M A').app W)) :=
  ConcreteCategory.bijective_of_isIso (((moduleLowerShriek S').obj M).val.presheaf.map
    (changeBaseRestrictOpenHom (f := f) (g := g) (h := h) A'.obj W.unop).op)

/-! ### The Zariski Čech vanishing -/

section Cech

variable (F : SheafOfModules.{u} (structureSheaf S')) (hF : IsLocallyQuasiCoherent F)
  (hcrys : IsSheafCrystal F)

/-- **The comparison of the base-change presheaf with the restriction of `f_cris^*ℱ` to the
ambient scheme of `A'`**: `tauToSheaf` at `τ : f_CRIS(A') ⟶ A`, followed by
`crisInverseImageRestrictOpenComparison07Q9`. -/
def crisInverseImageTauComparison07Q9 {A' : CrystallineThickening S}
    {A : CrystallineThickening S'}
    (τ : (changeBase S S' f g h).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A) :
    (tauPresheaf F τ).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ⟶
      (CrystallineThickening.restrictOpenFunctor A').op ⋙
        ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
          ((moduleULift S').obj F))).obj :=
  tauToSheaf F τ ≫ crisInverseImageRestrictOpenComparison07Q9 f g h _ A'

include hF hcrys in
/-- **The Čech complex of `f_cris^*ℱ` on a standard cover of the ambient scheme of `A'` is exact in
positive degrees**, for `A'` of affine ambient scheme `T` with a morphism
`τ : f_CRIS(A') ⟶ A` to an object `A` of `Cris(X'/S')` of affine ambient scheme, and `g` a family
of global sections of `T` generating the unit ideal.  Over the basic opens of `T` the restriction
of `f_cris^*ℱ` is the base-change presheaf `W ↦ Γ(W, 𝒪_T) ⊗_{Γ(A, 𝒪)} ℱ(A)`, which localizes on
basic opens, so the complex is an algebraic Čech complex. -/
theorem exactAt_cechComplex_crisInverseImage07Q9 {A' : CrystallineThickening S}
    [IsAffine A'.obj.thickening.target.scheme] {A : CrystallineThickening S'}
    [IsAffine A.obj.thickening.target.scheme]
    (τ : (changeBase S S' f g h).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    {n : ℕ} (t : Fin n → Γ(A'.obj.thickening.target.scheme, ⊤))
    (ht : Ideal.span (Set.range t) = ⊤) (p : ℕ) :
    ((cechComplexFunctor fun i ↦ A'.obj.thickening.target.scheme.basicOpen (t i)).obj
      ((CrystallineThickening.restrictOpenFunctor A').op ⋙
        ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
          ((moduleULift S').obj F))).obj)).ExactAt (p + 1) := by
  have : IsAffine ((changeBase S S' f g h).obj
      ((CrystallineThickening.ι S).obj A')).thickening.target.scheme :=
    inferInstanceAs (IsAffine A'.obj.thickening.target.scheme)
  refine Stacks.Cohomology.Cech.exactAt_cechComplex_of_isLocalizedModule (U := ⊤)
    (Q := tauPresheaf F τ) (g := t)
    (fun s W hW hWU ↦ Stacks.AlgebraicGeometry.BaseChangePresheaf.isLocalizedModule_basePresheaf
      (tauRing τ) (sectionsOver F A) (isAffineOpen_top _) s hW hWU)
    (crisInverseImageTauComparison07Q9 f g h F τ) (fun s W hW _ ↦ ?_) ht p
  subst hW
  have h₁ := bijective_tauToSheaf_app_of_isAffineOpen07Q9 F τ hF hcrys
    ((isAffineOpen_top _).basicOpen s)
  have h₂ := bijective_crisInverseImageRestrictOpenComparison07Q9_app f g h
    ((moduleULift S').obj F) A' (op (Scheme.basicOpen _ s))
  exact h₂.comp h₁

end Cech

/-! ### The class of objects and the Čech criterion -/

/-- **The objects of `Cris(X/S)` the criterion is run on**: those with affine ambient scheme
admitting a morphism `f_CRIS(A') ⟶ A` to an object `A` of `Cris(X'/S')` with affine ambient
scheme. -/
def crisInverseImageAffineObjects07Q9 : Set (CrystallineThickening S) :=
  {A' | IsAffine A'.obj.thickening.target.scheme ∧ ∃ A : CrystallineThickening S',
    IsAffine A.obj.thickening.target.scheme ∧
      Nonempty ((changeBase S S' f g h).obj ((CrystallineThickening.ι S).obj A') ⟶
        (CrystallineThickening.ι S').obj A)}

/-- **The class `crisInverseImageAffineObjects07Q9` is closed under maps**: an object with affine
ambient scheme mapping to a member is a member, composing the map to `Cris(X'/S')`. -/
theorem mem_crisInverseImageAffineObjects07Q9_of_hom {A'' A' : CrystallineThickening S}
    (k : A'' ⟶ A') (hA'' : IsAffine A''.obj.thickening.target.scheme)
    (hA' : A' ∈ crisInverseImageAffineObjects07Q9 f g h) :
    A'' ∈ crisInverseImageAffineObjects07Q9 f g h := by
  obtain ⟨-, A, hA, ⟨τ⟩⟩ := hA'
  exact ⟨hA'', A, hA, ⟨(changeBase S S' f g h).map ((CrystallineThickening.ι S).map k) ≫ τ⟩⟩

/-- **The system of coverings the criterion is run on**: the standard restriction covers of the
members of `crisInverseImageAffineObjects07Q9`. -/
def crisInverseImageCoverings07Q9 (A' : CrystallineThickening S) :
    Set { E : PreZeroHypercover.{u + 1} A' // E.sieve₀ ∈ smallTopology S A' } :=
  {E | A' ∈ crisInverseImageAffineObjects07Q9 f g h ∧ E ∈ standardRestrictCoverings A'}

/-- The iterated fibre products of the coverings `crisInverseImageCoverings07Q9` exist. -/
theorem hasProduct_of_mem_crisInverseImageCoverings07Q9 {A' : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A' // E.sieve₀ ∈ smallTopology S A' })
    (hE : E ∈ crisInverseImageCoverings07Q9 f g h A') (p : ℕ) (i : Fin (p + 1) → E.1.I₀) :
    HasProduct fun a ↦ Over.mk (E.1.f (i a)) :=
  hasProduct_of_mem_standardRestrictCoverings E hE.2 p i

/-- **The hypothesis `hCovObjects` of [Stacks, Tag 03F9]** for `crisInverseImageCoverings07Q9`
and `crisInverseImageAffineObjects07Q9`: the members of a covering and its finite fibre products
have affine ambient scheme and map to the covered object. -/
theorem crisInverseImageCoverings07Q9_covObjects {A' : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A' // E.sieve₀ ∈ smallTopology S A' })
    (hE : E ∈ crisInverseImageCoverings07Q9 f g h A') :
    A' ∈ crisInverseImageAffineObjects07Q9 f g h ∧
      (∀ i, E.1.X i ∈ crisInverseImageAffineObjects07Q9 f g h) ∧
      ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
          hasProduct_of_mem_crisInverseImageCoverings07Q9 f g h E hE
        (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ crisInverseImageAffineObjects07Q9 f g h := by
  obtain ⟨_, hX, hprod⟩ := standardRestrictCoverings_covObjects E hE.2
  refine ⟨hE.1, fun i ↦ mem_crisInverseImageAffineObjects07Q9_of_hom f g h (E.1.f i) (hX i) hE.1,
    fun p i ↦ ?_⟩
  let : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀), HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
    hasProduct_of_mem_crisInverseImageCoverings07Q9 f g h E hE
  exact mem_crisInverseImageAffineObjects07Q9_of_hom f g h
    (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).hom (hprod p i) hE.1

/-- **The hypothesis `hCovCofinal` of [Stacks, Tag 03F9]** for `crisInverseImageCoverings07Q9`:
every covering sieve of a member of `crisInverseImageAffineObjects07Q9` is refined by a standard
restriction cover, `standardRestrictCoverings_cofinal`. -/
theorem crisInverseImageCoverings07Q9_cofinal :
    ∀ A' ∈ crisInverseImageAffineObjects07Q9 f g h, ∀ R ∈ smallTopology S A',
      ∃ E : { E : PreZeroHypercover.{u + 1} A' // E.sieve₀ ∈ smallTopology S A' },
        E ∈ crisInverseImageCoverings07Q9 f g h A' ∧ E.1.sieve₀ ≤ R := by
  intro A' hA' R hR
  obtain ⟨E, hE, hle⟩ := standardRestrictCoverings_cofinal S A' hA'.1 R hR
  exact ⟨E, ⟨hA', hE⟩, hle⟩

section Vanishing

variable (F : SheafOfModules.{u} (structureSheaf S')) (hF : IsLocallyQuasiCoherent F)
  (hcrys : IsSheafCrystal F)

include hF hcrys in
/-- **The hypothesis `hCech` of [Stacks, Tag 03F9]** for `f_cris^*ℱ` and the coverings
`crisInverseImageCoverings07Q9`: the Čech cohomology of a standard restriction cover of a member
of `crisInverseImageAffineObjects07Q9` is the Zariski Čech cohomology of the cover of its ambient
scheme by basic opens, which vanishes in positive degrees by
`exactAt_cechComplex_crisInverseImage07Q9`. -/
theorem isZero_cechCohomology_crisInverseImage07Q9 {A' : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A' // E.sieve₀ ∈ smallTopology S A' })
    (hE : E ∈ crisInverseImageCoverings07Q9 f g h A') (p : ℕ) (hp : 0 < p) :
    letI : ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
      hasProduct_of_mem_crisInverseImageCoverings07Q9 f g h E hE
    IsZero (Stacks.CechSite.cechCohomology E.1
      ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
        ((moduleULift S').obj F))).obj p) := by
  obtain ⟨E, hEcov⟩ := E
  obtain ⟨⟨hA', A, hA, ⟨τ⟩⟩, -, n, t, ht, hEeq⟩ := hE
  have : IsAffine A'.obj.thickening.target.scheme := hA'
  have : IsAffine A.obj.thickening.target.scheme := hA
  change E = _ at hEeq
  subst hEeq
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  refine CrystallineThickening.isZero_cechCohomology_restrictOpenHypercover A' _ _ (q + 1) ?_
  refine Stacks.CategoryTheory.CechComplex.isZero_homology_of_ulift
    (fun j : Fin n ↦ A'.obj.thickening.target.scheme.basicOpen (t j)) _ (q + 1) ?_
  exact (exactAt_cechComplex_crisInverseImage07Q9 f g h F hF hcrys τ t
    (Stacks.Cohomology.Cech.span_range_eq_top_of_isStandardOpenCoverOfSpectrum ht)
    q).isZero_homology

open Stacks.Cohomology.FreeYonedaUnivLE in
include hF hcrys in
/-- **The higher cohomology of `f_cris^*ℱ` over a member of `crisInverseImageAffineObjects07Q9`
vanishes**: `H^p(Cris(X/S)/A', f_cris^*ℱ) = 0` for `p > 0`.  This is the Čech criterion
[Stacks, Tag 03F9] for the class `crisInverseImageAffineObjects07Q9` and the coverings
`crisInverseImageCoverings07Q9`, read through the identifications of `Ext` out of the free abelian
sheaf on `A'` with the cohomology of the localized site, as in
`vanishing07JJ_of_hasStandardCechVanishing`. -/
theorem isZero_overCohomology_crisModuleInverseImage_of_mem07Q9 (A' : CrystallineThickening S)
    (hA' : A' ∈ crisInverseImageAffineObjects07Q9 f g h) (p : ℕ) (hp : 0 < p) :
    IsZero ((overCohomologyFunctor S A' p).obj ((restrictToOver S A').obj
      ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
        ((moduleULift S').obj F))))) := by
  have hsub := Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero.{u + 1, u + 1}
    (smallTopology S) (crisInverseImageAffineObjects07Q9 f g h)
    (crisInverseImageCoverings07Q9 f g h)
    (fun E hE ↦ hasProduct_of_mem_crisInverseImageCoverings07Q9 f g h E hE)
    (fun E hE ↦ crisInverseImageCoverings07Q9_covObjects f g h E hE)
    (crisInverseImageCoverings07Q9_cofinal f g h) _
    (fun E hE q hq ↦ isZero_cechCohomology_crisInverseImage07Q9 f g h F hF hcrys E hE q hq)
    A' hA' p hp
  refine IsZero.of_iso ?_ (overCohomologyIsoRightDerivedSections S A' _ p)
  refine IsZero.of_iso ?_
    (cohomologyPresheafObjIsoRightDerivedSectionsOfEnoughInjectives.{u + 1}
      (smallTopology S) _ p A').symm
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsub

include hF hcrys in
/-- **The higher cohomology of `ℱ' = f_cris^*ℱ` over an object mapping to `Cris(X'/S')`
vanishes.**  Let `ℱ` be a locally quasi-coherent crystal on `Cris(X'/S')`, `A'` an object of
`Cris(X/S)` and `τ : f_CRIS(A') ⟶ A` a morphism to an object `A` of `Cris(X'/S')`, both with affine
ambient schemes.  Then `H^p(Cris(X/S)/A', ℱ') = 0` for every `p > 0`. -/
theorem isZero_overCohomology_crisModuleInverseImage07Q9 {A' : CrystallineThickening S}
    [IsAffine A'.obj.thickening.target.scheme] {A : CrystallineThickening S'}
    [IsAffine A.obj.thickening.target.scheme]
    (τ : (changeBase S S' f g h).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A) (p : ℕ) (hp : 0 < p) :
    IsZero ((overCohomologyFunctor S A' p).obj ((restrictToOver S A').obj
      ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
        ((moduleULift S').obj F))))) :=
  isZero_overCohomology_crisModuleInverseImage_of_mem07Q9 f g h F hF hcrys A'
    ⟨inferInstance, A, inferInstance, ⟨τ⟩⟩ p hp

end Vanishing

/-! ### The vanishing at the levels of a system mapping to a system with affine levels -/

variable {f g h} in
/-- **The higher cohomology of `f_cris^*ℱ` vanishes at the levels of a system of thickenings
mapping to a system with affine levels.**  For a morphism `Φ : T ⟶ T'` of systems of thickenings
over `f` (`CechSystemHom`), with `T` and `T'` of affine ambient schemes at every level, the level
maps `Φ.τ` put every level of `T` in the class `crisInverseImageAffineObjects07Q9`, so
`isZero_overCohomology_crisModuleInverseImage07Q9` applies there. -/
theorem vanishingOnLevels07Q9_crisModuleInverseImage
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom f g h T T')
    (hT : HasAffineMonoLevels T) (hT' : HasAffineMonoLevels T')
    (F : SheafOfModules.{u} (structureSheaf S')) (hF : IsLocallyQuasiCoherent F)
    (hcrys : IsSheafCrystal F) :
    VanishingOnLevels07Q9 T ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
      ((moduleULift S').obj F))) := fun b e n hn ↦
  isZero_overCohomology_crisModuleInverseImage_of_mem07Q9 f g h F hF hcrys _
    ⟨hT.isAffine b e, _, hT'.isAffine b (e + Φ.k), ⟨Φ.τ ⦋b⦌ e⟩⟩ n hn

variable {f g h} in
/-- `vanishingOnLevels07Q9_crisModuleInverseImage` for a crystal in quasi-coherent modules. -/
theorem vanishingOnLevels07Q9_crisModuleInverseImage_of_isQuasiCoherentCrystal
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom f g h T T')
    (hT : HasAffineMonoLevels T) (hT' : HasAffineMonoLevels T')
    (F : SheafOfModules.{u} (structureSheaf S')) (hF : IsQuasiCoherentCrystal S' F) :
    VanishingOnLevels07Q9 T ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
      ((moduleULift S').obj F))) :=
  vanishingOnLevels07Q9_crisModuleInverseImage Φ hT hT' F
    ((isQuasicoherentOnSite_iff F).1 hF.1).1 hF.2

end SmallSite

end Crystalline.GlobalCrystallineSituation
