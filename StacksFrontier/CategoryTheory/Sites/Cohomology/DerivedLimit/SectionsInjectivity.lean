module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MonoHomologyProjection
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.CategoryTheory.Functor.NatIsoMonoEpi
import StacksCore.Tactic.StacksAttribute

/-! # Injectivity on sections of cohomology of a derived inverse limit

Let `(C, O)` be a ringed site, let `(Kₙ)` be an inverse system in the unbounded derived category
`D(O)` and let `L` be a derived limit of it, so that the structural map `p : L ⟶ ∏ Kₙ` is the
first map of a distinguished triangle whose second map is the difference map
`(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))`. Fix an object `V` of `C`, a degree `m`, an index `N` and a cofinal
system of coverings of `V`. Suppose that over every member of every covering in the system the
first derived inverse limit of the tower of cohomology *presheaves* vanishes in degree `m - 1`,
and that the tower is injective on cohomology in degree `m` from the index `N` on. Then

`H^m(L)(V) ⟶ H^m(K_N)(V)`

is injective.

The argument is the one of the source. Over a single object `V_i` of a covering, cohomology
presheaf sections commute with the product, so the vanishing of `R¹ lim` in degree `m - 1`
makes the difference map surjective there; the long exact sequence of the derived-limit triangle
then makes `H^m(L)(V_i) ⟶ (∏ H^m(K_n))(V_i)` injective, and `H^m(L)(V_i)` therefore embeds in
the limit of the tower, whose projection to the stage `N` is injective because every transition
map above `N` is. That gives injectivity of the map of cohomology presheaves on every `V_i`, and
injectivity on sections over `V` follows because sheafification is injective on sections over `V`
as soon as the map of presheaves is injective on a cofinal system of coverings of `V` — the
kernel presheaf has no nonzero section over `V` — together with the Tag 0BKV identification of
the sheafified cohomology presheaf with the cohomology sheaf.

## Main results

* `Stacks.Cohomology.DerivedLimitSections.cohomology_derivedLimit_projection_mono_on_sections`:
  the injectivity criterion, with the module universe free and therefore with five class
  hypotheses. Tag 0D6L is registered on its restatement at the module universe `max u v r w`,
  where those five are theorems,
  `cohomology_derivedLimit_projection_mono_on_sections_unconditional`.

## Implementation notes

Covering families and their cofinality are `Stacks.Cohomology.CofinalCoveringSystem`. The
objectwise cohomology towers are obtained by evaluating the derived cohomology presheaf of Tag
0BKV, so that their transition maps are canonically induced by the original tower. The first
derived inverse limit is the cokernel of the usual `1 - shift` endomorphism of the product. The
derived limit is presented by the distinguished product triangle of Tag 0A09 rather than by a
`HasDerivedLimit` predicate, so the component of the structural map at any index is literally
the canonical projection.

`IsGrothendieckAbelian` for the sheaves of modules appears as a hypothesis, with its own
universe, because the Tag 0BKV associated-sheaf isomorphism needs it to supply K-injective
resolutions. It is none of the source's business, and neither are the other four class
hypotheses: all five are theorems as soon as the module universe contains the site, and they
are discharged at `cohomology_derivedLimit_projection_mono_on_sections_unconditional`, which
carries the tag.

That the derived sections presheaf is a triangulated right adjoint — which is what lets the long
exact homology sequence of the derived-limit triangle be pushed to presheaves — is proved here as
`derivedSectionsPresheaf_isTriangulated_and_isRightAdjoint`. It comes from
`CategoryTheory.Adjunction.derived` applied to the sheafification adjunction lifted to homotopy
categories: sheafification is exact, so the derived functor of its homotopy-category lift is
inverted by the comparison with `mapDerivedCategory`, and the derived adjunction's right adjoint
is the Tag 0BKV derived sections presheaf.

## References

* [Stacks Project, Tag 0D6L](https://stacks.math.columbia.edu/tag/0D6L)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Stacks.Cohomology.SiteCohomologyPresheaf
open Stacks.Homology (homotopyHomologyIso)

namespace Stacks.Cohomology.DerivedLimitSections

universe u v w g

attribute [local instance] HasDerivedCategory.standard

/-! ### Products of derived presheaves of modules -/

/-- Countable products of presheaves of modules are exact, being computed sectionwise. -/
private theorem presheaf_exact_products
    {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{w}) :
    HasExactLimitsOfShape (Discrete ℕ) (PresheafOfModules.{w} O) :=
  HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) (PresheafOfModules.toPresheaf O)

/-- Cohomology of a derived presheaf of modules commutes with countable products. -/
private theorem presheaf_derivedHomology_preserves_products
    {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{w}) (m : ℤ) :
    PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor (PresheafOfModules.{w} O) m) := by
  have := presheaf_exact_products O
  have := Stacks.DerivedProducts.hasProductsOfShape_nat (A := PresheafOfModules.{w} O)
  exact Stacks.DerivedProducts.preservesLimitsOfShape_discrete_of_isIso_piComparison _
    fun Y => Stacks.DerivedProducts.isIso_piComparison_homologyFunctor Y m

/-! ### The derived sections presheaf is a triangulated right adjoint -/

/-- The homology comparison for an exact functor, descended to derived categories. -/
private def exactDerivedHomologyIso {A B : Type*} [Category* A] [Abelian A]
    [Category* B] [Abelian B] (E : A ⥤ B) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (n : ℤ) :
    E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B n ≅
      DerivedCategory.homologyFunctor A n ⋙ E :=
  Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.mapDerivedCategoryFactorsh _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactorsh B n) ≪≫
      (homotopyHomologyIso E n).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh A n).symm E ≪≫
      Functor.associator _ _ _)

variable (X : RingedSite.{u, v, w})

/-- Sheafification of the cohomology of the derived unit of the sections functor is an
isomorphism in every degree. -/
private theorem isIso_sheafification_homology_map_totalRightDerivedUnit
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [(homotopySectionsPresheaf X).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))]
    (n : ℤ)
    (I : HomotopyCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor
        (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) n ⋙
        PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (((homotopySectionsPresheaf X).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))).app I)) := by
  rw [← isIso_comp_right_iff _
    ((sheafificationCohomologyPresheafIso X n).hom.app (DerivedCategory.Qh.obj I)),
    sheafificationCohomologyPresheafIso_comp X n I]
  infer_instance

/-- The Tag 0BKV derived sections presheaf is a triangulated functor and a right adjoint. Its
left adjoint is the derived functor of sheafification; the comparison with `mapDerivedCategory`
is an isomorphism because sheafification is exact, and `CategoryTheory.Adjunction.derived`
then produces the adjunction of derived functors. -/
private theorem derivedSectionsPresheaf_isTriangulated_and_isRightAdjoint
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [(homotopySectionsPresheaf X).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))] :
    ∃ s : (derivedSectionsPresheaf X).CommShift ℤ,
      let := s
      (derivedSectionsPresheaf X).IsTriangulated ∧
        (derivedSectionsPresheaf X).IsRightAdjoint := by
  let A := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let P := PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
  let a : P ⥤ A :=
    PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  let i : A ⥤ P := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have : i.Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let adj : a ⊣ i :=
    PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  have := adj.isLeftAdjoint
  have : PreservesBinaryBiproducts a := preservesBinaryBiproducts_of_preservesBinaryCoproducts a
  have : a.Additive := Functor.additive_of_preservesBinaryBiproducts a
  let aD := a.mapDerivedCategory
  let R := derivedSectionsPresheaf X
  let α := a.mapDerivedCategoryFactorsh.hom
  let β := (homotopySectionsPresheaf X).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))
  have ha : (HomotopyCategory.quasiIso P (.up ℤ)).IsInvertedBy
      (a.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso _ a.mapDerivedCategoryFactorsh.symm]
    exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts _ _) _
  have : aD.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso P (.up ℤ)) :=
    (Functor.isLeftDerivedFunctor_iff_of_inverts _ _ ha).2 inferInstance
  have : (aD ⋙ R).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α R)
      (HomotopyCategory.quasiIso P (.up ℤ)) :=
    (Functor.isLeftDerivedFunctor_iff_of_inverts _ _
      (MorphismProperty.IsInvertedBy.of_comp _ _ ha _)).2 inferInstance
  have : IsIso (Functor.whiskerRight β aD ≫ (Functor.associator _ _ _).hom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro I
    have : IsIso (aD.map (β.app I)) := (DerivedCategory.isIso_iff _ _).2 fun n ↦
      (NatIso.isIso_map_iff (exactDerivedHomologyIso a n) (β.app I)).2
        (isIso_sheafification_homology_map_totalRightDerivedUnit X n I)
    dsimp
    infer_instance
  have : (R ⋙ aD).IsRightDerivedFunctor
      (Functor.whiskerRight β aD ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A (.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ (asIso _).symm
  let d := (adj.mapHomotopyCategory (.up ℤ)).derived
    (HomotopyCategory.quasiIso P (.up ℤ)) (HomotopyCategory.quasiIso A (.up ℤ)) α β
  let s := d.rightAdjointCommShift ℤ
  let := s
  have : d.CommShift ℤ := d.commShift_of_leftAdjoint ℤ
  exact ⟨s, d.isTriangulated_rightAdjoint, d.isRightAdjoint⟩

/-! ### Tag 0D6L, with the module universe free -/

/-- **Stacks Project, Tag 0D6L**, with the module universe of the ringed site left free. A
locally vanishing `R¹ lim` in degree `m - 1` and eventual injectivity on cohomology in degree
`m`, over a cofinal system of coverings of `V`, force the projection from a derived limit to the
stage `N` to be injective on cohomology sections over `V`.

The five class hypotheses below are not hypotheses of the source, and they are all theorems
once the module universe contains the site. Tag 0D6L is registered on
`cohomology_derivedLimit_projection_mono_on_sections_unconditional` (in this namespace), which
is this statement at the module universe `max u v r w` with all five discharged. -/
theorem cohomology_derivedLimit_projection_mono_on_sections (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [(homotopySectionsPresheaf X).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (V : X.C) (m : ℤ) (N : ℕ)
    (Cov : CofinalCoveringSystem X.J V)
    (hlimOne : ∀ 𝒰 : PreZeroHypercover.{max u v} V, Cov.cov 𝒰 →
      ∀ i : 𝒰.I₀,
        let F := K ⋙ derivedSectionsPresheaf X ⋙
          DerivedCategory.homologyFunctor
            (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) (m - 1) ⋙
          PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
            (.op (𝒰.X i))
        IsZero (cokernel (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
              F.map (homOfLE (Nat.le_succ n)).op)))
    (hinj : ∀ 𝒰 : PreZeroHypercover.{max u v} V, Cov.cov 𝒰 →
      ∀ i : 𝒰.I₀,
        let F := K ⋙ derivedSectionsPresheaf X ⋙
          DerivedCategory.homologyFunctor
            (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) m ⋙
          PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
            (.op (𝒰.X i))
        ∀ (n : ℕ) (hn : N ≤ n), Mono (F.map (homOfLE hn).op)) :
    Mono ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (.op V)).map
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).map
        (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N))) := by
  classical
  let P := PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
  let R := derivedSectionsPresheaf X
  obtain ⟨s, ht, ha⟩ := derivedSectionsPresheaf_isTriangulated_and_isRightAdjoint X
  let : R.CommShift ℤ := s
  have : R.IsTriangulated := ht
  have : R.IsRightAdjoint := ha
  have (n : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor P n) :=
    presheaf_derivedHomology_preserves_products (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj n
  let φ := p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N
  let H := R ⋙ DerivedCategory.homologyFunctor P m
  obtain ⟨δ, hδ⟩ := hL
  have hmono : ∀ 𝒰, Cov.cov 𝒰 → ∀ i : 𝒰.I₀,
      Mono ((H.map φ).app (.op (𝒰.X i))) := by
    intro 𝒰 h𝒰 i
    let E := PresheafOfModules.evaluation.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
      (.op (𝒰.X i))
    let G := H ⋙ E
    let Gprev := R ⋙ DerivedCategory.homologyFunctor P (m - 1) ⋙ E
    let T := Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
          K.map (homOfLE (Nat.le_succ n)).op) δ
    have hT : T ∈ distTriang _ := hδ
    have : Epi (E.map ((DerivedCategory.homologyFunctor P (m - 1)).map
        (R.mapTriangle.obj T).mor₂)) :=
      epi_map_difference K Gprev (hlimOne 𝒰 h𝒰 i)
    have : Mono (G.map p) :=
      _root_.mono_homology_eval_of_epi E (R.mapTriangle.obj T) (R.map_distinguished T hT) m
    exact mono_projection_of_difference K p
      (comp_distTriang_mor_zero₁₂ T hT) G N (hinj 𝒰 h𝒰 i)
  exact (NatIso.mono_map_iff
    (Functor.isoWhiskerRight (sheafificationCohomologyPresheafIso X m)
      (SheafOfModules.evaluation.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (.op V))) φ).1
    (sheafification_eval_mono (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V Cov (H.map φ) hmono)

end Stacks.Cohomology.DerivedLimitSections

end
