module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.GabrielPopescu
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# Derived functors at an arbitrary localization of the cochain complexes

Let `𝒜` be an abelian category and let `Q : C(𝒜) ⥤ D(𝒜)` be *any* localization of the cochain
complexes at the quasi-isomorphisms, not necessarily `CategoryTheory.DerivedCategory.Q`.  A total
right derived functor of an additive functor `F : 𝒜 ⥤ ℬ` relative to `Q` is a pair `(R, α)` with
`α : F_* ⋙ Q' ⟶ Q ⋙ R` exhibiting `R` as a left Kan extension along `Q`, where `F_*` is `F`
applied degreewise.

Statements of this shape cannot be fed directly to the derived-adjunction criterion
`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`,
because the quasi-isomorphisms of `C(𝒜)` admit no calculus of fractions; those of the homotopy
category `K(𝒜)` do.  This file moves such a pair to `K(𝒜)`: a localization `Q` of `C(𝒜)` factors
uniquely through `K(𝒜)` (`Stacks.DerivedModel.homotopyLocalization`), the unit `α` transports to a
unit `β` on `K(𝒜)` (`Stacks.DerivedModel.homotopyUnit`), and K-injective complexes compute the
transported pair pointwise (`Stacks.DerivedModel.exists_isRightDerivedValueAt_homotopy`).

The companion construction is for a left adjoint which is *exact*: it needs no derivation, being
obtained from the degreewise functor by descending along the localization
(`Stacks.DerivedModel.derivedFunctorOfExact`), and the constant pro-object computes it.  Combining
the two pointwise computations gives the adjunction
`Stacks.DerivedModel.adjunctionOfExact` between arbitrary chosen models.

## Main definitions

* `Stacks.DerivedModel.homotopyLocalization` — the factorisation of `Q` through `K(𝒜)`.
* `Stacks.DerivedModel.homotopyUnit` — the derivation unit `α`, transported to `K(𝒜)`.
* `Stacks.DerivedModel.derivedFunctorOfExact` — the functor induced between chosen models by an
  exact functor, with no derivation.
* `Stacks.DerivedModel.adjunctionOfExact` — the adjunction between the derived functor of an exact
  left adjoint and the total right derived functor of its right adjoint, both at arbitrary chosen
  models.

## Main results

* `Stacks.DerivedModel.homotopyLocalizationQuotientIso` — `Q` is recovered from its factorisation.
* `Stacks.DerivedModel.exists_isRightDerivedValueAt_homotopy` — K-injective complexes compute the
  transported pair at every object of `K(𝒜)`.
* `Stacks.DerivedModel.derivedFunctorOfExactFac` — the defining factorisation of the derived
  functor of an exact functor.

## Implementation notes

The transported unit is **not** separately shown to exhibit `R` as a left Kan extension along
`Stacks.DerivedModel.homotopyLocalization Q`; that is a consequence of
`Stacks.DerivedModel.exists_isRightDerivedValueAt_homotopy` and is derived inside
`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`, which
is the only consumer.  The pointwise invertibility of `β` at a K-injective complex that the proof
needs is read off from invertibility of `α` there, which is the complex-level criterion
`Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective`; no transfer of the
Kan-extension property between the two localizations is required.

The four purely category-theoretic ingredients — `Stacks.Injectives.coneOfInvertedMorphisms`,
`Stacks.Injectives.coneOfInvertedMorphisms_isLeftDerivedValueAt`,
`Stacks.Injectives.coconeOfTerminalUnder_isRightDerivedValueAt` and
`Stacks.Injectives.isTerminalUnderKInjective` — are imported from
`StacksFrontier/Homology/Injectives/GabrielPopescu.lean`, where they were `private`.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedModel

variable {A : Type*} {B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]

section Factorization

variable (Q : CochainComplex A ℤ ⥤ DerivedCategory A)
  [Q.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- The factorisation of an arbitrary localization `Q : C(𝒜) ⥤ D(𝒜)` of the cochain complexes at
the quasi-isomorphisms through the homotopy category `K(𝒜)`.

It is `CategoryTheory.DerivedCategory.Qh` followed by the comparison equivalence between the
chosen model and the standard one, which `CategoryTheory.Localization.uniq` provides from the two
localizations of `C(𝒜)`. -/
def homotopyLocalization : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  DerivedCategory.Qh ⋙
    (Localization.uniq (DerivedCategory.Q (C := A)) Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor

/-- `Stacks.DerivedModel.homotopyLocalization Q` is a localization of the homotopy category at the
quasi-isomorphisms: it is `CategoryTheory.DerivedCategory.Qh` followed by an equivalence. -/
instance homotopyLocalization_isLocalization :
    (homotopyLocalization Q).IsLocalization
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.IsLocalization.of_equivalence_target
    (DerivedCategory.Qh (C := A))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (homotopyLocalization Q)
    (Localization.uniq (DerivedCategory.Q (C := A)) Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    (Iso.refl _)

/-- Composing the factorisation `Stacks.DerivedModel.homotopyLocalization Q` with the quotient
`C(𝒜) ⥤ K(𝒜)` recovers `Q`. -/
def homotopyLocalizationQuotientIso :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ homotopyLocalization Q ≅ Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      (Localization.uniq (DerivedCategory.Q (C := A)) Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor ≪≫
    Localization.compUniqFunctor (DerivedCategory.Q (C := A)) Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

variable {E : Type*} [Category* E]

/-- The factorisation of `Stacks.DerivedModel.homotopyLocalizationQuotientIso` whiskered by a
functor out of the chosen derived category. -/
def homotopyLocalizationCompIso (R : DerivedCategory A ⥤ E) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ (homotopyLocalization Q ⋙ R) ≅ Q ⋙ R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homotopyLocalizationQuotientIso Q) R

end Factorization

section Unit

variable [CategoryWithHomology A] [CategoryWithHomology B]

/-- For an additive functor `F`, applying `F` degreewise to a complex and then localizing agrees
with passing to the homotopy category first.  This is the standard-model form of
`Stacks.DerivedModel.mapHomotopyCategoryCompLocalizationIso`. -/
def mapHomotopyCategoryCompQhIso (F : A ⥤ B) [F.Additive] :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)

variable (F : A ⥤ B) [F.Additive]
  (Q : CochainComplex B ℤ ⥤ DerivedCategory B)
  [Q.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]

/-- For an additive functor `F` and a chosen localization `Q` of the cochain complexes of the
target, applying `F` degreewise and localizing by `Q` factors through the homotopy category of the
source through `Stacks.DerivedModel.homotopyLocalization Q`. -/
def mapHomotopyCategoryCompLocalizationIso :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ homotopyLocalization Q) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapHomotopyCategoryCompQhIso F)
      (Localization.uniq (DerivedCategory.Q (C := B)) Q
        (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Localization.compUniqFunctor (DerivedCategory.Q (C := B)) Q
      (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)))

variable (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q ⟶ QSource ⋙ R)

/-- **The derivation unit, transported to the homotopy category.**  A unit
`α : F_* ⋙ Q ⟶ QSource ⋙ R` for a total right derived functor relative to a chosen localization
`QSource` of the cochain complexes determines a unit for the same `R` relative to the induced
localization `Stacks.DerivedModel.homotopyLocalization QSource` of the homotopy category.

It is `α` conjugated by `Stacks.DerivedModel.mapHomotopyCategoryCompLocalizationIso` and
`Stacks.DerivedModel.homotopyLocalizationCompIso`, descended along the quotient
`C(𝒜) ⥤ K(𝒜)` — which is possible because the two outer functors are homotopy invariant. -/
def homotopyUnit :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ homotopyLocalization Q ⟶
      homotopyLocalization QSource ⋙ R :=
  Quotient.natTransLift _
    ((mapHomotopyCategoryCompLocalizationIso F Q).hom ≫ α ≫
      (homotopyLocalizationCompIso QSource R).inv)

/-- At the homotopy class of a complex, `Stacks.DerivedModel.homotopyUnit` is `α` conjugated by the
two comparison isomorphisms. -/
lemma homotopyUnit_app_quotient (K : CochainComplex A ℤ) :
    (homotopyUnit F Q QSource R α).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (mapHomotopyCategoryCompLocalizationIso F Q).hom.app K ≫ α.app K ≫
        (homotopyLocalizationCompIso QSource R).inv.app K := rfl

end Unit

section Pointwise

variable [CategoryWithHomology A] [CategoryWithHomology B] [IsGrothendieckAbelian A]
  (F : A ⥤ B) [F.Additive]
  (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
  [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R)

variable [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- **The transported unit is invertible at a K-injective complex.**  This is the complex-level
statement that K-injective complexes compute the right derived functor, read through the
conjugation of `Stacks.DerivedModel.homotopyUnit_app_quotient`. -/
lemma isIso_homotopyUnit_app_quotient (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((homotopyUnit F QTarget QSource R α).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  have hInv : Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget) := by
    intro K L f hK hL hf
    exact Localization.inverts QTarget (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) _
      ((HomologicalComplex.mem_quasiIso_iff _).2
        (Injectives.KInjectiveResolution.quasiIso_mapHomologicalComplex_map_of_isKInjective
          F f hK hL hf))
  have hα : IsIso (α.app I) :=
    Injectives.KInjectiveResolution.isIso_app_of_isKInjective QSource R α hInv I inferInstance
  rw [homotopyUnit_app_quotient]
  infer_instance

/-- **K-injective complexes compute the transported derived functor at every object.**  For every
object `K` of `K(𝒜)` there is a cocone over the quasi-isomorphisms out of `K` which computes the
right derived value of `F_* ⋙ Stacks.DerivedModel.homotopyLocalization QTarget` at `K`, together
with an identification of its vertex with `R(K)` compatible with
`Stacks.DerivedModel.homotopyUnit`.

This is the input that
`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`
requires on the right-hand side.  The cocone is the one attached to a K-injective resolution of
`K`, which is a terminal object of the category of quasi-isomorphisms out of `K`. -/
theorem exists_isRightDerivedValueAt_homotopy :
    ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
    ∃ (c : Cocone (MorphismProperty.Under.forget
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ K ⋙
          Under.forget K ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            homotopyLocalization QTarget))
      (_ : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        homotopyLocalization QTarget).IsRightDerivedValueAt
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
      (e : c.pt ≅ R.obj ((homotopyLocalization QSource).obj K)),
      ∀ s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ K,
        c.ι.app s ≫ e.hom ≫ R.map ((homotopyLocalization QSource).map s.hom) =
          (homotopyUnit F QTarget QSource R α).app s.right := by
  let c := ComplexShape.up ℤ
  let qA := HomotopyCategory.quotient A c
  let W := HomotopyCategory.quasiIso A c
  let Qs := homotopyLocalization QSource
  let Qt := homotopyLocalization QTarget
  let Fh := F.mapHomotopyCategory c
  let β := homotopyUnit F QTarget QSource R α
  intro K
  obtain ⟨Kc, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  let q := (Injectives.kInjectiveResolutionInclusion A).app Kc
  have hqi : QuasiIso q := inferInstance
  let qh := qA.map q
  have hqhW : W qh := (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hqi
  let t₀ : W.Under ⊤ (qA.obj Kc) := MorphismProperty.Under.mk ⊤ qh hqhW
  let ht := Injectives.isTerminalUnderKInjective
    ((Injectives.kInjectiveResolutionFunctor A).obj Kc) qh hqhW
  let coc := Limits.coconeOfDiagramTerminal ht
    (MorphismProperty.Under.forget W ⊤ (qA.obj Kc) ⋙
      Under.forget (qA.obj Kc) ⋙ Fh ⋙ Qt)
  have hvalue := Injectives.coconeOfTerminalUnder_isRightDerivedValueAt (Fh ⋙ Qt) W
    (qA.obj Kc) t₀ ht
  have hβ : IsIso (β.app t₀.right) :=
    isIso_homotopyUnit_app_quotient F QSource QTarget R α _
  let eβ : _ ≅ _ := asIso (β.app t₀.right)
  have hR : ∀ u : W.Under ⊤ (qA.obj Kc), IsIso (R.map (Qs.map u.hom)) := fun u =>
    have := Localization.inverts Qs W u.hom u.prop
    inferInstance
  have := hR t₀
  let eR : _ ≅ _ := asIso (R.map (Qs.map t₀.hom))
  let e : coc.pt ≅ R.obj (Qs.obj (qA.obj Kc)) := eβ ≪≫ eR.symm
  refine ⟨coc, hvalue, e, fun s => ?_⟩
  have hcomp : s.hom ≫ (ht.from s).right = t₀.hom := MorphismProperty.Under.w (ht.from s)
  have hnat : (Fh ⋙ Qt).map ((ht.from s).right) ≫ β.app t₀.right =
      β.app s.right ≫ R.map (Qs.map ((ht.from s).right)) := by
    simpa only [Functor.comp_map] using β.naturality ((ht.from s).right)
  have := hR s
  have he : e.hom = β.app t₀.right ≫ eR.inv := by
    change (eβ ≪≫ eR.symm).hom = β.app t₀.right ≫ eR.inv
    simp [eβ]
  have hright : R.map (Qs.map ((ht.from s).right)) = inv (R.map (Qs.map s.hom)) ≫ eR.hom := by
    rw [IsIso.eq_inv_comp, ← Functor.map_comp, ← Functor.map_comp, hcomp]
    rfl
  dsimp [coc, Limits.coconeOfDiagramTerminal]
  rw [he]
  change Qt.map (Fh.map (ht.from s).right) ≫ (β.app t₀.right ≫ eR.inv) ≫
      R.map (Qs.map s.hom) = β.app s.right
  rw [Category.assoc, reassoc_of% hnat, hright]
  simp

end Pointwise

section Exact

variable [CategoryWithHomology A] [CategoryWithHomology B]
  (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
  [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]

/-- An exact functor applied degreewise and followed by a chosen localization of the target
inverts the quasi-isomorphisms of the homotopy category of the source: it agrees up to isomorphism
with the localization followed by the induced functor of derived categories. -/
lemma isInvertedBy_mapHomotopyCategory_comp_homotopyLocalization :
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ homotopyLocalization QSource) := by
  have hInv₀ : (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (DerivedCategory.Qh ⋙ G.mapDerivedCategory) :=
    MorphismProperty.IsInvertedBy.of_comp _ _
      (Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))) G.mapDerivedCategory
  have hInv₁ : (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _ G.mapDerivedCategoryFactorsh]
    exact hInv₀
  exact MorphismProperty.IsInvertedBy.of_comp _ _ hInv₁
    (Localization.uniq (DerivedCategory.Q (C := A)) QSource
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor

/-- **The functor of chosen derived categories induced by an exact functor.**  No derivation is
involved: an exact functor applied degreewise already inverts quasi-isomorphisms, so it descends
along the localization `Stacks.DerivedModel.homotopyLocalization QTarget`.

This is the arbitrary-model counterpart of `CategoryTheory.Functor.mapDerivedCategory`. -/
def derivedFunctorOfExact : DerivedCategory B ⥤ DerivedCategory A :=
  Localization.lift (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ homotopyLocalization QSource)
    (isInvertedBy_mapHomotopyCategory_comp_homotopyLocalization G QSource)
    (homotopyLocalization QTarget)

/-- The defining factorisation of `Stacks.DerivedModel.derivedFunctorOfExact`: precomposing with
the localization of the homotopy category gives back the degreewise functor followed by the
localization of the target. -/
def derivedFunctorOfExactFac :
    homotopyLocalization QTarget ⋙ derivedFunctorOfExact G QSource QTarget ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ homotopyLocalization QSource :=
  Localization.fac (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ homotopyLocalization QSource)
    (isInvertedBy_mapHomotopyCategory_comp_homotopyLocalization G QSource)
    (homotopyLocalization QTarget)

variable [IsGrothendieckAbelian A] {F : A ⥤ B} [F.Additive]
  (adj : G ⊣ F)
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R)
  [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- **Stacks 09T5 at arbitrary chosen models.**  Let `G ⊣ F` be an adjunction of additive functors
with `G` exact, let `QSource` and `QTarget` be chosen localizations of the cochain complexes of the
two abelian categories, and let `(R, α)` be a total right derived functor of `F` relative to them.
Then the functor `Stacks.DerivedModel.derivedFunctorOfExact G` induced by `G` is left adjoint
to `R`.

Both sides are computed pointwise: `R` by K-injective resolutions
(`Stacks.DerivedModel.exists_isRightDerivedValueAt_homotopy`) and the derived functor of the exact
`G` by the constant pro-object
(`Stacks.Injectives.coneOfInvertedMorphisms_isLeftDerivedValueAt`), and
`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt` turns
the two computations into the adjunction. -/
def adjunctionOfExact : derivedFunctorOfExact G QSource QTarget ⊣ R := by
  set c := ComplexShape.up ℤ
  set Qs := homotopyLocalization QSource
  set Qt := homotopyLocalization QTarget
  set W' := HomotopyCategory.quasiIso B c
  set Gc := G.mapHomotopyCategory c
  set H := Gc ⋙ Qs
  have hInv : W'.IsInvertedBy H :=
    isInvertedBy_mapHomotopyCategory_comp_homotopyLocalization G QSource
  set LG := derivedFunctorOfExact G QSource QTarget
  set αL : Qt ⋙ LG ⟶ H := (Localization.fac H hInv Qt).hom
  have hLGvalue : ∀ M : HomotopyCategory B c,
      ∃ (d : Cone (MorphismProperty.Over.forget W' ⊤ M ⋙ Over.forget M ⋙ H))
        (_ : H.IsLeftDerivedValueAt W' M d) (e : LG.obj (Qt.obj M) ≅ d.pt),
        ∀ t : W'.Over ⊤ M, LG.map (Qt.map t.hom) ≫ e.hom ≫ d.π.app t = αL.app t.left := by
    intro M
    refine ⟨Injectives.coneOfInvertedMorphisms H W' hInv M,
      Injectives.coneOfInvertedMorphisms_isLeftDerivedValueAt H W' hInv M,
      (Localization.fac H hInv Qt).app M, fun t => ?_⟩
    have : IsIso (H.map t.hom) := hInv t.hom t.prop
    have hn : LG.map (Qt.map t.hom) ≫ αL.app M = αL.app t.left ≫ H.map t.hom := by
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj,
        Functor.const_obj_obj, H] using αL.naturality t.hom
    dsimp only [Injectives.coneOfInvertedMorphisms]
    change LG.map (Qt.map t.hom) ≫ αL.app M ≫ inv (H.map t.hom) = αL.app t.left
    rw [reassoc_of% hn, IsIso.hom_inv_id, Category.comp_id]
  exact Classical.choose
    (CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      (CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction adj c)
      (HomotopyCategory.quasiIso A c) W' Qs Qt R
      (homotopyUnit F QTarget QSource R α) LG αL
      (exists_isRightDerivedValueAt_homotopy F QSource QTarget R α) hLGvalue)

end Exact

end Stacks.DerivedModel

end
