module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinFractionDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetDegreewise

/-!
# Compatibility of the Gysin map with the de Rham differentials

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global equations with
`c = c' + 1` and let `i : Z ⟶ X` be a closed immersion cut out by them.  [Stacks, Tag 0G85] says
that the Gysin map

`γ^p_{f₁, …, f_c} : Ω^p_{Z/S} ⟶ ℋ ᶜ_Z(Ω^{p+c}_{X/S})`

of [Stacks, Tag 0G83] is compatible with the de Rham differentials on `Ω^•_{X/S}` and
`Ω^•_{Z/S}`.  Since `d` is only `π⁻¹𝒪_S`-linear, every arrow of the square is read on the
underlying abelian (pre)sheaves on `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pushforwardDeRhamDifferentialPresheafHom` and
  `pushforwardDeRhamDifferentialAbHom`: the de Rham differential of `Z/S` pushed forward along
  `i`, as a morphism of the underlying abelian presheaves, resp. abelian sheaves, on `X`.
* `AlgebraicGeometry.Scheme.Hom.gysinTargetReindex`: the canonical identification of two terms of
  the de Rham complex of equal degree, pushed through `i_*ℋ ᶜ_Z`.
* `AlgebraicGeometry.Scheme.Hom.GysinMapCommutesWithDeRham`: the comparison square of
  [Stacks, Tag 0G85] for the Gysin map of [Stacks, Tag 0G83], as a proposition.

## Main results

* `AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham`: the square
  `GysinMapCommutesWithDeRham` commutes.
* `AlgebraicGeometry.Scheme.Hom.formRestriction_comm_deRhamDifferentialPresheafHom` and
  `formRestriction_comm_deRhamDifferentialAbHom`: restriction of relative `p`-forms to `Z`
  commutes with the de Rham differentials, as a square of morphisms of abelian presheaves, resp.
  abelian sheaves, on `X`.
* `AlgebraicGeometry.Scheme.Hom.epi_abelianSheaf_formRestriction`: restriction of relative
  `p`-forms to `Z` stays an epimorphism after forgetting the module structure.
* `AlgebraicGeometry.Scheme.Hom.precomp_gysinMap_left` and `precomp_gysinMap_right`: each side
  of the square for the Gysin map, precomposed with restriction of forms to `Z`, is the
  corresponding side of the square for the Gysin formula.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G84](https://stacks.math.columbia.edu/tag/0G84)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Z S : Scheme.{u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-! ### The de Rham differential of `Z/S` pushed forward along `i` -/

/-- The relative de Rham differential `d : Ω^p_{Z/S} ⟶ Ω^{p+1}_{Z/S}` of `Z/S`, pushed forward
along `i`, as a morphism of the underlying abelian presheaves of `i_*Ω^p_{Z/S}` and
`i_*Ω^{p+1}_{Z/S}` on `X`. -/
public def pushforwardDeRhamDifferentialPresheafHom (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) :
    Scheme.Modules.presheaf
        ((Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ))) ⟶
      Scheme.Modules.presheaf
        ((Scheme.Modules.pushforward i).obj
          (relativeDifferentialForms (i ≫ π) ((p + 1 : ℕ) : ℤ))) :=
  (TopCat.Presheaf.pushforward Ab i.base).map (deRhamDifferentialPresheafHom (i ≫ π) p)

/-- On a local `p`-form on `Z` over `i⁻¹U`, the morphism of abelian presheaves of
`AlgebraicGeometry.Scheme.Hom.pushforwardDeRhamDifferentialPresheafHom` is the de Rham differential
of `Z/S`. -/
public theorem pushforwardDeRhamDifferentialPresheafHom_app (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ)
    (U : X.Opens) (ω : Γ(relativeDifferentialForms (i ≫ π) (p : ℤ), i ⁻¹ᵁ U)) :
    (pushforwardDeRhamDifferentialPresheafHom i π p).app (op U) ω =
      ((deRhamComplex (i ≫ π)).d p (p + 1)).val.app (op (i ⁻¹ᵁ U)) ω := rfl

/-- The relative de Rham differential of `Z/S` pushed forward along `i`, as a morphism of the
underlying abelian sheaves on `X`, through the forgetful functor
`Stacks.Perfect.AbelianFraction.abelianSheaf`. -/
public def pushforwardDeRhamDifferentialAbHom (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) :
    (abelianSheaf X).obj
        ((Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ))) ⟶
      (abelianSheaf X).obj
        ((Scheme.Modules.pushforward i).obj
          (relativeDifferentialForms (i ≫ π) ((p + 1 : ℕ) : ℤ))) :=
  abHom (pushforwardDeRhamDifferentialPresheafHom i π p)

/-- The underlying morphism of abelian presheaves of
`AlgebraicGeometry.Scheme.Hom.pushforwardDeRhamDifferentialAbHom` is
`AlgebraicGeometry.Scheme.Hom.pushforwardDeRhamDifferentialPresheafHom`. -/
public theorem pushforwardDeRhamDifferentialAbHom_hom (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) :
    (pushforwardDeRhamDifferentialAbHom i π p).hom =
      pushforwardDeRhamDifferentialPresheafHom i π p := rfl

/-! ### Restriction of forms to `Z` commutes with the de Rham differentials -/

/-- Restriction of relative `p`-forms to `Z` commutes with the de Rham differentials, as a
square of morphisms of abelian presheaves on `X`:

`Ω^p_{X/S} ⟶ i_*Ω^p_{Z/S}`,  `Ω^{p+1}_{X/S} ⟶ i_*Ω^{p+1}_{Z/S}`

with `AlgebraicGeometry.Scheme.Hom.formRestriction` as horizontal arrows and the two de Rham
differentials, read on the underlying abelian presheaves, as vertical arrows. -/
public theorem formRestriction_comm_deRhamDifferentialPresheafHom (i : Z ⟶ X) (π : X ⟶ S)
    (p : ℕ) :
    Scheme.Modules.Hom.mapPresheaf (formRestriction i π (p : ℤ)) ≫
        pushforwardDeRhamDifferentialPresheafHom i π p =
      deRhamDifferentialPresheafHom π p ≫
        Scheme.Modules.Hom.mapPresheaf (formRestriction i π ((p + 1 : ℕ) : ℤ)) := by
  refine NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ω => ?_))
  exact deRhamComplex_d_relativeDifferentialFormsMap i π (i ≫ π) (𝟙 S) (by simp) p U.unop ω

/-- Restriction of relative `p`-forms to `Z` commutes with the de Rham differentials, as a
square of morphisms of abelian sheaves on `X`. -/
public theorem formRestriction_comm_deRhamDifferentialAbHom (i : Z ⟶ X) (π : X ⟶ S) (p : ℕ) :
    (abelianSheaf X).map (formRestriction i π (p : ℤ)) ≫
        pushforwardDeRhamDifferentialAbHom i π p =
      deRhamDifferentialAbHom π p ≫
        (abelianSheaf X).map (formRestriction i π ((p + 1 : ℕ) : ℤ)) :=
  congrArg abHom (formRestriction_comm_deRhamDifferentialPresheafHom i π p)

/-- Restriction of relative `p`-forms to `Z` stays an epimorphism after forgetting the module
structure. -/
public theorem epi_abelianSheaf_formRestriction (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    (p : ℕ) : Epi ((abelianSheaf X).map (formRestriction i π (p : ℤ))) :=
  have := epi_formRestriction i π p
  inferInstance

/-! ### The comparison square of Stacks 0G85 for the Gysin map -/

/-- The canonical identification of two terms of the de Rham complex of `X/S` of equal degree,
pushed through `i_*ℋ ᶜ_Z`. -/
public def gysinTargetReindex (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤)) {m n : ℤ}
    (h : m = n) :
    pushforwardLocalCohomology f (relativeDifferentialForms π m) ⟶
      pushforwardLocalCohomology f (relativeDifferentialForms π n) :=
  (Stacks.Perfect.GysinLocalCohomology.localCohomologyPushforwardFunctor
      (isClosed_equationsClosedSet f) ((c + 1 : ℕ) : ℤ)).map
    (eqToHom (congrArg (relativeDifferentialForms π) h))

/-- The degree equality `(p + 1) + (c + 1) = p + (c + 1) + 1`, as an equality of integers. -/
public theorem gysinTargetDegree_eq {c : ℕ} (p : ℕ) :
    ((p + 1 : ℕ) : ℤ) + ((c + 1 : ℕ) : ℤ) = ((p + (c + 1) + 1 : ℕ) : ℤ) := by
  push_cast; ring

/-- The comparison square of [Stacks, Tag 0G85] for the Gysin map of [Stacks, Tag 0G83], as a
proposition: the square

`i_*Ω^p_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c}_{X/S})`,  `i_*Ω^{p+1}_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c+1}_{X/S})`

whose horizontal arrows are the underlying abelian-sheaf morphisms of
`AlgebraicGeometry.Scheme.Hom.gysinMap` in degrees `p` and `p + 1`, whose left vertical arrow is
the de Rham differential of `Z/S` pushed forward along `i` and read on the underlying abelian
sheaves, and whose right vertical arrow is
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap` — the action of `i_*ℋ ᶜ_Z` on the de Rham
differential of `X/S` supplied by [Stacks, Tag 0G74] part (2) — commutes.  The degree transport
`AlgebraicGeometry.Scheme.Hom.gysinTargetReindex` identifies the two spellings `p + 1 + c` and
`p + c + 1` of the target degree. -/
public def GysinMapCommutesWithDeRham (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f) : Prop :=
  (abelianSheaf X).map (gysinMap i π f p hcut) ≫ gysinTargetDeRhamMap π f (p + (c + 1)) =
    pushforwardDeRhamDifferentialAbHom i π p ≫
      (abelianSheaf X).map (gysinMap i π f (p + 1) hcut ≫
        gysinTargetReindex π f (gysinTargetDegree_eq (c := c) p))

/-! ### The square for the Gysin map follows from the square for the Gysin formula -/

/-- Passing to underlying abelian presheaves with `Scheme.Modules.Hom.mapPresheaf` is
functorial. -/
public theorem mapPresheaf_comp {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C) :
    Scheme.Modules.Hom.mapPresheaf (a ≫ b) =
      Scheme.Modules.Hom.mapPresheaf a ≫ Scheme.Modules.Hom.mapPresheaf b :=
  (Scheme.Modules.toPresheaf X).map_comp a b

/-- The degree reindexing of `AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom` is the
underlying morphism of abelian presheaves of the canonical identification of the two terms of the
de Rham complex as `𝒪_X`-modules. -/
public theorem deRhamReindexPresheafHom_eq_mapPresheaf (π : X ⟶ S) {m n : ℕ} (h : m = n) :
    deRhamReindexPresheafHom π h =
      Scheme.Modules.Hom.mapPresheaf
        (eqToHom (congrArg (relativeDifferentialForms π) (congrArg Nat.cast h))) := by
  subst h
  simp only [deRhamReindexPresheafHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    eqToHom_refl]
  rfl

/-- The fraction class of [Stacks, Tag 0G7Q] commutes with a degree reindexing: identifying
two terms of the de Rham complex of equal degree before taking the class of the fraction is the
same as identifying the corresponding terms of `i_*ℋ ᶜ_Z` afterwards. -/
public theorem formFractionClass_comm_eqToHom (π : X ⟶ S) {c : ℕ} (f : Fin (c + 1) → Γ(X, ⊤))
    {m n : ℤ} (h : m = n)
    [(relativeDifferentialForms π m).IsQuasicoherent]
    [(relativeDifferentialForms π n).IsQuasicoherent] :
    eqToHom (congrArg (relativeDifferentialForms π) h) ≫ formFractionClass π f n =
      formFractionClass π f m ≫ gysinTargetReindex π f h := by
  subst h
  simp only [gysinTargetReindex, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- Precomposing the left-hand composite of the square of [Stacks, Tag 0G85] for the Gysin map
with restriction of forms to `Z` turns the Gysin map into the Gysin formula. -/
public theorem precomp_gysinMap_left (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f) :
    (abelianSheaf X).map (formRestriction i π (p : ℤ)) ≫
        (abelianSheaf X).map (gysinMap i π f p hcut) ≫
          gysinTargetDeRhamMap π f (p + (c + 1)) =
      (abelianSheaf X).map (gysinFormulaHom π f (p : ℤ)) ≫
        gysinTargetDeRhamMap π f (p + (c + 1)) := by
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, formRestriction_comp_gysinMap]

/-- Precomposing the right-hand composite of the square of [Stacks, Tag 0G85] for the Gysin map
with restriction of forms to `Z` gives the de Rham differential of `X/S` followed by the Gysin
formula. -/
public theorem precomp_gysinMap_right (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f)
    (hdeg : ((p + 1 : ℕ) : ℤ) + ((c + 1 : ℕ) : ℤ) = ((p + (c + 1) + 1 : ℕ) : ℤ)) :
    (abelianSheaf X).map (formRestriction i π (p : ℤ)) ≫
        pushforwardDeRhamDifferentialAbHom i π p ≫
          (abelianSheaf X).map (gysinMap i π f (p + 1) hcut ≫ gysinTargetReindex π f hdeg) =
      deRhamDifferentialAbHom π p ≫
        (abelianSheaf X).map
          (gysinFormulaHom π f ((p + 1 : ℕ) : ℤ) ≫ gysinTargetReindex π f hdeg) := by
  rw [← Category.assoc, formRestriction_comm_deRhamDifferentialAbHom, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← Category.assoc, formRestriction_comp_gysinMap]

/-! ### The reindexed Gysin formula is the right-hand composite of the formula square -/

/-- The Gysin formula in degree `q` followed by the degree transport
`AlgebraicGeometry.Scheme.Hom.gysinTargetReindex` is the wedge factor, then the identification of
the two terms of the de Rham complex, then the fraction class in the transported degree. -/
public theorem gysinFormulaHom_comp_gysinTargetReindex (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (q n : ℕ)
    (hdeg : ((q : ℕ) : ℤ) + ((c + 1 : ℕ) : ℤ) = ((n : ℕ) : ℤ)) :
    gysinFormulaHom π f (q : ℤ) ≫ gysinTargetReindex π f hdeg =
      (gysinWedgeHom π f (q : ℤ) ≫ eqToHom (congrArg (relativeDifferentialForms π) hdeg)) ≫
        formFractionClass π f ((n : ℕ) : ℤ) := by
  rw [show gysinFormulaHom π f (q : ℤ) =
      gysinWedgeHom π f (q : ℤ) ≫ formFractionClass π f ((q : ℤ) + ((c + 1 : ℕ) : ℤ)) from rfl]
  simp only [Category.assoc]
  rw [formFractionClass_comm_eqToHom]

/-- The Gysin formula followed by the degree transport, read on the underlying abelian sheaves,
is the wedge factor followed by the identification of degrees, then the fraction class. -/
public theorem abelianSheaf_map_gysinFormulaHom_comp_gysinTargetReindex (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (q n : ℕ)
    (hdeg : ((q : ℕ) : ℤ) + ((c + 1 : ℕ) : ℤ) = ((n : ℕ) : ℤ)) :
    (abelianSheaf X).map (gysinFormulaHom π f (q : ℤ) ≫ gysinTargetReindex π f hdeg) =
      (abelianSheaf X).map (gysinWedgeHom π f (q : ℤ) ≫
          eqToHom (congrArg (relativeDifferentialForms π) hdeg)) ≫
        (abelianSheaf X).map (formFractionClass π f ((n : ℕ) : ℤ)) := by
  rw [gysinFormulaHom_comp_gysinTargetReindex, CategoryTheory.Functor.map_comp]

/-- The identification of the terms of the de Rham complex in the integer degrees `(p + 1) + c`
and `p + c + 1`, read on the underlying abelian presheaves, is
`AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom` for the natural numbers `p + 1 + c` and
`p + c + 1`. -/
public theorem mapPresheaf_eqToHom_eq_deRhamReindexPresheafHom (π : X ⟶ S) (c p : ℕ) :
    (show Scheme.Modules.presheaf (relativeDifferentialForms π ((p + 1 + (c + 1) : ℕ) : ℤ)) ⟶
          Scheme.Modules.presheaf (relativeDifferentialForms π ((p + (c + 1) + 1 : ℕ) : ℤ)) from
        Scheme.Modules.Hom.mapPresheaf
          (eqToHom (congrArg (relativeDifferentialForms π) (gysinTargetDegree_eq (c := c) p)))) =
      deRhamReindexPresheafHom π (show p + 1 + (c + 1) = p + (c + 1) + 1 by omega) :=
  (deRhamReindexPresheafHom_eq_mapPresheaf π _).symm

/-- The wedge factor followed by the degree transport, read on the underlying abelian
presheaves, is the wedge factor followed by
`AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom`. -/
public theorem mapPresheaf_gysinWedgeHom_comp_eqToHom (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) :
    Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ) ≫
        eqToHom (congrArg (relativeDifferentialForms π) (gysinTargetDegree_eq (c := c) p))) =
      Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
        deRhamReindexPresheafHom π (show p + 1 + (c + 1) = p + (c + 1) + 1 by omega) :=
  (mapPresheaf_comp _ _).trans
    (whisker_eq _ (mapPresheaf_eqToHom_eq_deRhamReindexPresheafHom π c p))

/-- The wedge factor followed by the degree transport, read on the underlying abelian sheaves,
is the wedge factor followed by `AlgebraicGeometry.Scheme.Hom.deRhamReindexPresheafHom`, under
`Stacks.Perfect.AbelianFraction.abHom`. -/
public theorem abelianSheaf_map_gysinWedgeHom_comp_eqToHom (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) :
    (abelianSheaf X).map (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ) ≫
        eqToHom (congrArg (relativeDifferentialForms π) (gysinTargetDegree_eq (c := c) p))) =
      abHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
        deRhamReindexPresheafHom π (show p + 1 + (c + 1) = p + (c + 1) + 1 by omega)) :=
  (Stacks.Perfect.AbelianFraction.abelianSheaf_map _).trans
    (congrArg abHom (mapPresheaf_gysinWedgeHom_comp_eqToHom π f p))

/-- The Gysin formula in degree `p + 1` followed by the degree transport, read on the underlying
abelian sheaves, is the right-hand composite of the square for the Gysin formula. -/
public theorem abelianSheaf_map_gysinFormulaHom_reindex_eq (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) :
    (abelianSheaf X).map (gysinFormulaHom π f ((p + 1 : ℕ) : ℤ) ≫
        gysinTargetReindex π f (gysinTargetDegree_eq (c := c) p)) =
      abHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
          deRhamReindexPresheafHom π (show p + 1 + (c + 1) = p + (c + 1) + 1 by omega)) ≫
        (abelianSheaf X).map (formFractionClass π f ((p + (c + 1) + 1 : ℕ) : ℤ)) :=
  (abelianSheaf_map_gysinFormulaHom_comp_gysinTargetReindex π f (p + 1) (p + (c + 1) + 1)
      (gysinTargetDegree_eq (c := c) p)).trans
    (congrArg (· ≫ (abelianSheaf X).map (formFractionClass π f ((p + (c + 1) + 1 : ℕ) : ℤ)))
      (abelianSheaf_map_gysinWedgeHom_comp_eqToHom π f p))

/-! ### Stacks 0G85 for the Gysin map -/

/-- The Gysin map of [Stacks, Tag 0G83] is compatible with the de Rham differentials on
`Ω^•_{X/S}` and `Ω^•_{Z/S}`: the square

`i_*Ω^p_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c}_{X/S})`,  `i_*Ω^{p+1}_{Z/S} ⟶ i_*ℋ ᶜ_Z(Ω^{p+c+1}_{X/S})`

of `AlgebraicGeometry.Scheme.Hom.GysinMapCommutesWithDeRham` commutes. -/
@[stacks 0G85]
public theorem gysinMapCommutesWithDeRham (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin (c + 1) → Γ(X, ⊤)) (p : ℕ) (hcut : Stacks.Gysin.IsCutOutByEquations i f) :
    GysinMapCommutesWithDeRham i π f p hcut := by
  have hepi := epi_abelianSheaf_formRestriction i π p
  simp only [GysinMapCommutesWithDeRham]
  refine (cancel_epi ((abelianSheaf X).map (formRestriction i π (p : ℤ)))).mp ?_
  rw [precomp_gysinMap_left, precomp_gysinMap_right i π f p hcut (gysinTargetDegree_eq (c := c) p),
    abelianSheaf_map_gysinFormulaHom_reindex_eq]
  exact Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham f π p

end AlgebraicGeometry.Scheme.Hom

end
