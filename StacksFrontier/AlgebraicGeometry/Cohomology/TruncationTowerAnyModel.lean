module

public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerInput
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Convergence of the truncation tower at an arbitrary model of the derived category

[Stacks, Tag 0D6M] says that, on a ringed site which is locally covered by objects carrying
cofinal systems of coverings on whose members the cohomology of the cohomology sheaves of
`E ∈ D(𝒪)` vanishes above an object- and degree-dependent bound, the canonical map from `E` to the
derived limit of the tower `τ_{≥ -n}E` of its truncations from below is an isomorphism. It is
proved by `Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower`, which is *sorry*-free —
but its module
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence`
opens with a file-level `attribute [local instance] CategoryTheory.HasDerivedCategory.standard`,
so the derived category in its type is the standard one and the statement says nothing
about any other model. Everything the derived Spec–Γ development needs it for — [Stacks, Tag 08D3]
and through it the upper half of [Stacks, Tag 08D4] and [Stacks, Tag 06Z0] — lives at the locally
small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, where the *objects* of the two derived
categories agree definitionally and the *morphisms* do not:
`Quiver.Hom.{u, u+1}` against `Quiver.Hom.{u+1, u+1}`. The *What is not done* section of
`StacksFrontier/AlgebraicGeometry/Cohomology/TruncationTowerInput.lean` records the resulting hard
error and names the repair, which is what this file carries out.

The repair is a transport, not a restatement: the pinned theorem is applied unchanged, to the
image of the given data under the comparison equivalence of the two models.

## The three steps

1. **The t-structures.** `Stacks.TStructureTransport` works for an arbitrary exact functor `F`
   between pretriangulated categories with t-structures which carries `t₁.IsGE _ n` to
   `t₂.IsGE _ n`: the canonical comparison `τ_{≥n}(F X) ⟶ F(τ_{≥n}X)` obtained from the universal
   property of `τ_{≥n}` is then invertible, and compatible with the transition maps of the tower.
   Invertibility is `CategoryTheory.Triangulated.TStructure.triangle_iso_exists` applied to the
   image under `F` of the truncation triangle of `X`, which is distinguished because `F` is exact
   and whose two outer vertices lie in the right subcategories because `F` respects them.
2. **The two models.** `Stacks.DerivedModel` specializes this to the comparison equivalence
   `StacksDraft.Perfect.derivedEquivalence` of two chosen models of `D(C)`, which is already
   known to be exact and to commute with the shift. Respect for the t-structure needs no homology
   computation: `CategoryTheory.Triangulated.TStructure.IsGE` for the canonical t-structure on a
   derived category is by definition *being isomorphic to `Q K` for a strictly bounded below
   complex `K`*, and the comparison identifies the two localization functors `Q`. The homology
   functors of the two models are identified separately, by the universal property of the
   localization, because the vanishing hypothesis of Tag 0D6M is a statement about them.
3. **The transport.** The product of the tower is carried over by exactness of an equivalence and
   the objectwise comparison of step 1; the derived-limit triangle by exactness of the comparison;
   and the normalization `c ≫ q ≫ π n = τ_{≥ -n}π` by the defining property of the comparison.

## Main definitions

* `Stacks.TStructureTransport.truncGEComparison` — the comparison `τ_{≥n}(F X) ⟶ F(τ_{≥n}X)`.
* `Stacks.DerivedModel.modelHomologyIso` — the homology functors of two chosen models of `D(C)`
  agree along the comparison equivalence.

## Main results

* `Stacks.TStructureTransport.isIso_truncGEComparison` and
  `Stacks.TStructureTransport.truncGEComparison_natTrans` — the comparison is invertible, and
  commutes with the transition maps `τ_{≥a} ⟶ τ_{≥b}`.
* `Stacks.DerivedModel.isGE_modelEquiv_obj`, `Stacks.DerivedModel.isLE_modelEquiv_obj` — the
  comparison equivalence respects the canonical t-structures.
* `Stacks.TruncationTower.isIso_to_isDerivedLimit_truncGETower` — **[Stacks, Tag 0D6M] at an
  arbitrary model** of the derived category of modules on a ringed site.
* `Stacks.TruncationTower.isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherent` — **its
  instance for a scheme and an object with quasi-coherent cohomology**, which is [Stacks, Tag
  08D3]: the distinguished objects are the affine opens, the distinguished coverings are the
  coverings by affine opens, and the bound is identically `0` by Serre vanishing
  ([Stacks, Tag 01XB]). The four pieces of instantiating data are the model-free ones of
  `StacksFrontier/AlgebraicGeometry/Cohomology/TruncationTowerInput.lean`.

## Implementation notes

*The derived limit is presented, not constructed.* Both statements take the derived limit as a
distinguished triangle together with the requirement that the canonical truncation maps be the
components of the asserted morphism, exactly as the pinned Tag 0D6M does; so the transported
statement is the same statement, with the model freed and nothing else changed.

*Why the model binders are passed by name.* `AlgebraicGeometry.Scheme.Modules` is a `def` and not
a reducible abbreviation, and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is keyed on
`X.Modules` while `SheafOfModules.hasDerivedCategory` is keyed on `SheafOfModules R`: at the
ringed-site spelling `SheafOfModules X.ringCatSheaf` instance search finds the *second*, which is
a different term, and the two `HasProduct` hypotheses then fail to match. The scheme-level
statement therefore passes `hD` and `hP` to the ringed-site one by name rather than letting search
supply them.

*Why two `HasDerivedCategory` instances may not both be ambient.* With two local instances for one
category, synthesis of `∀ n : ℤ, (shiftFunctor (DerivedCategory C) n).Additive` fails,
so the standard model is introduced as a plain `let` and the two instances of that class are
supplied by name as `CategoryTheory.DerivedCategory.instAdditiveShiftFunctorInt`, whose value is
the one search would have produced.

*Transparency.* Three steps are in term mode rather than tactic mode because `rw`'s motive check
runs at `implicit` transparency, where the two models' identity morphisms are not interchangeable:
the identification of `e.inv.hom₂` with the identity in `isIso_truncGEComparison`, the
cancellation in the normalization, and the third commuting square of the triangle isomorphism.

No `@[stacks]` attribute appears below. Tag 0D6M is already carried by
`Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower`, and what is proved here is
the same statement at another model, not a second realization of the tag; Tag 08D3 is one of the
covering statements of a tag whose remaining content — the identification of the derived limit
itself — is not established here.

## References

* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 0D62](https://stacks.math.columbia.edu/tag/0D62)
* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Stacks.DerivedLimit

universe v u wRing wModule w z vC uC wR' wM'

/-! ### Transport of truncation along an exact functor respecting the t-structures -/

namespace Stacks.TStructureTransport
variable {D₁ D₂ : Type*} [Category* D₁] [Preadditive D₁] [HasZeroObject D₁] [HasShift D₁ ℤ]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [Pretriangulated D₁]
  [Category* D₂] [Preadditive D₂] [HasZeroObject D₂] [HasShift D₂ ℤ]
  [∀ n : ℤ, (shiftFunctor D₂ n).Additive] [Pretriangulated D₂]
  (t₁ : TStructure D₁) (t₂ : TStructure D₂) (F : D₁ ⥤ D₂) [F.CommShift ℤ] [F.IsTriangulated]
  (hGE : ∀ (n : ℤ) (X : D₁), t₁.IsGE X n → t₂.IsGE (F.obj X) n)

/-- The canonical comparison morphism `τ_{≥n}(F X) ⟶ F(τ_{≥n}X)`, induced by the universal
property of `τ_{≥n}` from `F` applied to the truncation map `X ⟶ τ_{≥n}X`. -/
def truncGEComparison (n : ℤ) (X : D₁) :
    (t₂.truncGE n).obj (F.obj X) ⟶ F.obj ((t₁.truncGE n).obj X) :=
  haveI := hGE n ((t₁.truncGE n).obj X) inferInstance
  t₂.descTruncGE (F.map ((t₁.truncGEπ n).app X)) n

omit [F.CommShift ℤ] [F.IsTriangulated] in
/-- The comparison `truncGEComparison` restricts along the truncation map `F X ⟶ τ_{≥n}(F X)` to
the image under `F` of the truncation map `X ⟶ τ_{≥n}X`. -/
@[reassoc (attr := simp)]
theorem π_truncGEComparison (n : ℤ) (X : D₁) :
    (t₂.truncGEπ n).app (F.obj X) ≫ truncGEComparison t₁ t₂ F hGE n X =
      F.map ((t₁.truncGEπ n).app X) :=
  have := hGE n ((t₁.truncGE n).obj X) inferInstance
  t₂.π_descTruncGE _ n

/-- If the exact functor `F` also carries `t₁.IsLE _ n` to `t₂.IsLE _ n`, then the comparison
`τ_{≥n}(F X) ⟶ F(τ_{≥n}X)` is an isomorphism. -/
theorem isIso_truncGEComparison
    (hLE : ∀ (n : ℤ) (X : D₁), t₁.IsLE X n → t₂.IsLE (F.obj X) n) (n : ℤ) (X : D₁) :
    IsIso (truncGEComparison t₁ t₂ F hGE n X) := by
  have h₃ := hGE n ((t₁.truncGE n).obj X) inferInstance
  have h₁ := hLE (n - 1) ((t₁.truncLT n).obj X) inferInstance
  obtain ⟨e, he⟩ := t₂.triangle_iso_exists
    (F.map_distinguished _ (t₁.triangleLTGE_distinguished n X))
    (t₂.triangleLTGE_distinguished n (F.obj X)) (Iso.refl (F.obj X)) (n - 1) n
    h₁ h₃ inferInstance inferInstance (by omega)
  have h1 : e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 _ := e.hom_inv_id_triangle_hom₂
  rw [he] at h1
  have hinv₂ : e.inv.hom₂ = 𝟙 _ := (Category.id_comp (e.inv.hom₂)).symm.trans h1
  have key : truncGEComparison t₁ t₂ F hGE n X = e.inv.hom₃ := by
    refine t₂.from_truncGE_obj_ext ?_
    rw [π_truncGEComparison]
    have hc := e.inv.comm₂
    rw [hinv₂] at hc
    exact (hc.trans (Category.id_comp _)).symm
  rw [key]
  exact ⟨e.hom.hom₃, e.inv_hom_id_triangle_hom₃, e.hom_inv_id_triangle_hom₃⟩

omit [F.CommShift ℤ] [F.IsTriangulated] in
/-- The comparison `truncGEComparison` commutes with the transition maps `τ_{≥a} ⟶ τ_{≥b}` for
`a ≤ b`. -/
theorem truncGEComparison_natTrans (a b : ℤ) (hab : a ≤ b) (X : D₁) :
    (t₂.natTransTruncGEOfLE a b hab).app (F.obj X) ≫ truncGEComparison t₁ t₂ F hGE b X =
      truncGEComparison t₁ t₂ F hGE a X ≫ F.map ((t₁.natTransTruncGEOfLE a b hab).app X) := by
  have hb := hGE b ((t₁.truncGE b).obj X) inferInstance
  have ha : t₂.IsGE (F.obj ((t₁.truncGE b).obj X)) a := t₂.isGE_of_ge _ a b hab
  refine t₂.from_truncGE_obj_ext ?_
  rw [← Category.assoc, t₂.π_natTransTruncGEOfLE_app a b hab, π_truncGEComparison,
    π_truncGEComparison_assoc, ← F.map_comp, t₁.π_natTransTruncGEOfLE_app a b hab]

end Stacks.TStructureTransport

/-! ### The two models of a derived category -/

namespace Stacks.DerivedModel
variable {C : Type u} [Category.{v} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)

/-- The homology functors of two models of the derived category agree along the comparison
equivalence `StacksDraft.Perfect.derivedEquivalence`. -/
def modelHomologyIso (n : ℤ) :
    (StacksDraft.Perfect.derivedEquivalence h₁ h₂).functor ⋙
        @DerivedCategory.homologyFunctor C _ _ h₂ n ≅
      @DerivedCategory.homologyFunctor C _ _ h₁ n := by
  letI := h₁
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      ((StacksDraft.Perfect.derivedEquivalence h₁ h₂).functor ⋙
        @DerivedCategory.homologyFunctor C _ _ h₂ n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (StacksDraft.Perfect.derivedEquivalenceCompQIso h₁ h₂) _ ≪≫
      @DerivedCategory.homologyFunctorFactors C _ _ h₂ n⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      (@DerivedCategory.homologyFunctor C _ _ h₁ n) :=
    ⟨DerivedCategory.homologyFunctorFactors C n⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) _ _ (Iso.refl _)

/-- An isomorphism `X ≅ Q K` in one model gives one `Φ X ≅ Q K` in the other. -/
private def modelEquivObjIsoQ {X : @DerivedCategory C _ _ h₁}
    {K : CochainComplex C ℤ} (e : X ≅ (@DerivedCategory.Q C _ _ h₁).obj K) :
    (StacksDraft.Perfect.derivedEquivalence h₁ h₂).functor.obj X ≅
      (@DerivedCategory.Q C _ _ h₂).obj K :=
  (StacksDraft.Perfect.derivedEquivalence h₁ h₂).functor.mapIso e ≪≫
    (StacksDraft.Perfect.derivedEquivalenceCompQIso h₁ h₂).app K

/-- The comparison equivalence between two models of the derived category carries objects which
are `≥ n` for the canonical t-structure to objects which are `≥ n`. -/
theorem isGE_modelEquiv_obj (n : ℤ) (X : @DerivedCategory C _ _ h₁)
    (hX : @DerivedCategory.IsGE C _ _ h₁ X n) :
    @DerivedCategory.IsGE C _ _ h₂
      ((StacksDraft.Perfect.derivedEquivalence h₁ h₂).functor.obj X) n := by
  obtain ⟨K, e, hK⟩ := hX.ge
  exact ⟨K, modelEquivObjIsoQ h₁ h₂ e, hK⟩

/-- The comparison equivalence between two models of the derived category carries objects which
are `≤ n` for the canonical t-structure to objects which are `≤ n`. -/
theorem isLE_modelEquiv_obj (n : ℤ) (X : @DerivedCategory C _ _ h₁)
    (hX : @DerivedCategory.IsLE C _ _ h₁ X n) :
    @DerivedCategory.IsLE C _ _ h₂
      ((StacksDraft.Perfect.derivedEquivalence h₁ h₂).functor.obj X) n := by
  obtain ⟨K, e, hK⟩ := hX.le
  exact ⟨K, modelEquivObjIsoQ h₁ h₂ e, hK⟩

end Stacks.DerivedModel

/-! ### Cohomology over an object is invariant under isomorphism -/

namespace Stacks.Cohomology
/-- If `F ≅ G` are isomorphic sheaves of modules and `H^p(U, G)` vanishes, then `H^p(U, F)`
vanishes. -/
theorem isZero_moduleCohomology_of_iso {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (O : Sheaf J RingCat.{wR'})
    [HasSheafify J AddCommGrpCat.{wM'}] [J.WEqualsLocallyBijective AddCommGrpCat.{wM'}]
    [EnoughInjectives (SheafOfModules.{wM'} O)] (U : C) (p : ℕ)
    {F G : SheafOfModules.{wM'} O} (e : F ≅ G)
    (h : IsZero (moduleCohomology O U p G)) : IsZero (moduleCohomology O U p F) := by
  have : (SheafOfModules.evaluation.{wM'} O (.op U)).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  exact h.of_iso
    ((Functor.rightDerived (SheafOfModules.evaluation.{wM'} O (.op U)) p).mapIso e)

end Stacks.Cohomology

/-! ### Tag 0D6M at an arbitrary model -/

namespace Stacks.TruncationTower
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [EnoughInjectives (SheafOfModules.{wModule} O)]
  [hD : HasDerivedCategory.{w} (SheafOfModules.{wModule} O)]

/-- Let `E` be an object of an arbitrary model of the derived category of modules on a ringed
site. Suppose every object is covered by objects of `B`, and each `V ∈ B` carries a cofinal system
`Cov V` of coverings on whose members the `p`-th cohomology of `H^{m-p}(E)` vanishes whenever
`p > degreeBound V m`. Then the canonical map from `E` to the derived limit `L` of the tower
`τ_{≥ -n}E`, presented by a distinguished triangle whose structure maps compose with `c` to the
truncation maps, is an isomorphism. -/
theorem isIso_to_isDerivedLimit_truncGETower
    (E : DerivedCategory (SheafOfModules.{wModule} O)) (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (degreeBound : ∀ V : C, B V → ℤ → ℤ)
    (Cov : ∀ V : C, B V → Set (PreZeroHypercover.{max u v} V))
    (Cov_isCover : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      Cov V hV 𝒰 → 𝒰.sieve₀ ∈ J V)
    (Cov_cofinal : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      𝒰.sieve₀ ∈ J V → ∃ 𝒱 : PreZeroHypercover.{max u v} V, Cov V hV 𝒱 ∧ Nonempty (𝒱.Hom 𝒰))
    (vanishing : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      Cov V hV 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ) (m : ℤ),
        degreeBound V hV m < (p : ℤ) →
          IsZero (Stacks.Cohomology.moduleCohomology O (𝒰.X i) p
            ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O)
              (m - (p : ℤ))).obj E)))
    [hP : HasProduct fun n : ℕ ↦ (truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{wModule} O))
    (c : E ⟶ L)
    (q : L ⟶ ∏ᶜ fun n : ℕ ↦ (truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk q (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) (n + 1) ≫
            (truncGETower (SheafOfModules.{wModule} O) E).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory (SheafOfModules.{wModule} O)))
    (hc : ∀ n : ℕ, c ≫ q ≫
      Pi.π (fun n : ℕ ↦ (truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  let h₂ : HasDerivedCategory (SheafOfModules.{wModule} O) :=
    HasDerivedCategory.standard (SheafOfModules.{wModule} O)
  let i1 : ∀ n : ℤ,
      (shiftFunctor (@DerivedCategory (SheafOfModules.{wModule} O) _ _ hD) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt (SheafOfModules.{wModule} O) _ _ hD n
  let i2 : ∀ n : ℤ,
      (shiftFunctor (@DerivedCategory (SheafOfModules.{wModule} O) _ _ h₂) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt (SheafOfModules.{wModule} O) _ _ h₂ n
  let Φ := (StacksDraft.Perfect.derivedEquivalence hD h₂).functor
  let : Φ.CommShift ℤ := StacksDraft.Perfect.derivedEquivalenceCommShift hD h₂
  have : Φ.IsTriangulated := StacksDraft.Perfect.derivedEquivalence_isTriangulated hD h₂
  have : Φ.Additive := StacksDraft.DerivedModel.modelEquiv_functor_additive hD h₂
  have hGE := Stacks.DerivedModel.isGE_modelEquiv_obj hD h₂
  have hLE := Stacks.DerivedModel.isLE_modelEquiv_obj hD h₂
  set t1 := @DerivedCategory.TStructure.t (SheafOfModules.{wModule} O) _ _ hD with ht1
  set t2 := @DerivedCategory.TStructure.t (SheafOfModules.{wModule} O) _ _ h₂ with ht2
  have hcmpiso := Stacks.TStructureTransport.isIso_truncGEComparison t1 t2 Φ hGE hLE
  have hnat := Stacks.TStructureTransport.truncGEComparison_natTrans t1 t2 Φ hGE
  -- families
  let f : ℕ → @DerivedCategory (SheafOfModules.{wModule} O) _ _ hD :=
    fun n => (@truncGETower (SheafOfModules.{wModule} O) _ _ hD E).obj ⟨n⟩
  let g : ℕ → @DerivedCategory (SheafOfModules.{wModule} O) _ _ h₂ :=
    fun n => (@truncGETower (SheafOfModules.{wModule} O) _ _ h₂ (Φ.obj E)).obj ⟨n⟩
  let ι : ∀ n : ℕ, Φ.obj (f n) ≅ g n := fun n =>
    have := hcmpiso (-(n : ℤ)) E
    (asIso (Stacks.TStructureTransport.truncGEComparison t1 t2 Φ hGE (-(n : ℤ)) E)).symm
  have hιinv : ∀ n : ℕ, (ι n).inv =
      Stacks.TStructureTransport.truncGEComparison t1 t2 Φ hGE (-(n : ℤ)) E := fun _ => rfl
  have hpl : PreservesLimit (Discrete.functor f) Φ := inferInstance
  have hlim := Limits.isLimitOfHasProductOfPreservesLimit Φ f
  let α : Discrete.functor (fun n : ℕ => Φ.obj (f n)) ≅ Discrete.functor g :=
    Discrete.natIso (fun j => ι j.as)
  have hlim2 : IsLimit (Fan.mk (Φ.obj (∏ᶜ f)) (fun n : ℕ => Φ.map (Pi.π f n) ≫ (ι n).hom)) :=
    IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α _).symm hlim)
      (Cone.ext (Iso.refl _) (by rintro ⟨n⟩; simp [α]))
  have hprod2 : HasProduct g := HasLimit.mk ⟨_, hlim2⟩
  let pIso : Φ.obj (∏ᶜ f) ≅ ∏ᶜ g :=
    hlim2.conePointUniqueUpToIso (limit.isLimit (Discrete.functor g))
  have hpIso : ∀ n : ℕ, pIso.hom ≫ Pi.π g n = Φ.map (Pi.π f n) ≫ (ι n).hom := fun n =>
    IsLimit.conePointUniqueUpToIso_hom_comp hlim2 (limit.isLimit (Discrete.functor g)) ⟨n⟩
  -- the tower square
  have hnat' : ∀ n : ℕ,
      (@truncGETower (SheafOfModules.{wModule} O) _ _ h₂ (Φ.obj E)).map
          (homOfLE (Nat.le_succ n)).op ≫ (ι n).inv =
        (ι (n + 1)).inv ≫ Φ.map ((@truncGETower (SheafOfModules.{wModule} O) _ _ hD E).map
          (homOfLE (Nat.le_succ n)).op) := by
    intro n
    rw [truncGETower_map_homOfLE_succ, truncGETower_map_homOfLE_succ, hιinv, hιinv]
    exact hnat (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) E
  have hsq : ∀ n : ℕ, (ι (n + 1)).hom ≫
        (@truncGETower (SheafOfModules.{wModule} O) _ _ h₂ (Φ.obj E)).map
          (homOfLE (Nat.le_succ n)).op =
      Φ.map ((@truncGETower (SheafOfModules.{wModule} O) _ _ hD E).map
        (homOfLE (Nat.le_succ n)).op) ≫ (ι n).hom := by
    intro n
    rw [← cancel_mono (ι n).inv, Category.assoc, hnat' n, Iso.hom_inv_id_assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  -- the two difference maps
  let m1 : (∏ᶜ f) ⟶ ∏ᶜ f := Pi.lift fun n : ℕ => Pi.π f n -
    Pi.π f (n + 1) ≫ (@truncGETower (SheafOfModules.{wModule} O) _ _ hD E).map
      (homOfLE (Nat.le_succ n)).op
  let m2 : (∏ᶜ g) ⟶ ∏ᶜ g := Pi.lift fun n : ℕ => Pi.π g n -
    Pi.π g (n + 1) ≫ (@truncGETower (SheafOfModules.{wModule} O) _ _ h₂ (Φ.obj E)).map
      (homOfLE (Nat.le_succ n)).op
  have hcomm : pIso.hom ≫ m2 = Φ.map m1 ≫ pIso.hom := by
    refine Limits.Pi.hom_ext _ _ (fun n => ?_)
    have e1 : m2 ≫ Pi.π g n = Pi.π g n - Pi.π g (n + 1) ≫
        (@truncGETower (SheafOfModules.{wModule} O) _ _ h₂ (Φ.obj E)).map
          (homOfLE (Nat.le_succ n)).op := Pi.lift_π _ n
    have e2 : m1 ≫ Pi.π f n = Pi.π f n - Pi.π f (n + 1) ≫
        (@truncGETower (SheafOfModules.{wModule} O) _ _ hD E).map
          (homOfLE (Nat.le_succ n)).op := Pi.lift_π _ n
    rw [Category.assoc, Category.assoc, e1, hpIso n, Preadditive.comp_sub, hpIso n,
      ← Category.assoc, hpIso (n + 1), Category.assoc, hsq n, ← Φ.map_comp_assoc,
      ← Preadditive.sub_comp, ← Φ.map_sub, ← e2, Φ.map_comp_assoc]
  -- the transported triangle
  have hcomm2 : m2 ≫ pIso.inv = pIso.inv ≫ Φ.map m1 := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hL' : Triangle.mk (Φ.map q ≫ pIso.hom) m2
      (pIso.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L) ∈
      distTriang (@DerivedCategory (SheafOfModules.{wModule} O) _ _ h₂) := by
    refine Pretriangulated.isomorphic_distinguished _ (Φ.map_distinguished _ hL) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl (Φ.obj L)) pIso.symm pIso.symm
      ((Category.assoc _ _ _).trans
        (((Φ.map q) ≫= Iso.hom_inv_id pIso).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm))) hcomm2
      (by
        have h : (shiftFunctor (@DerivedCategory (SheafOfModules.{wModule} O) _ _ h₂)
            (1 : ℤ)).map (Iso.refl (Φ.obj L)).hom = 𝟙 _ :=
          CategoryTheory.Functor.map_id _ _
        exact (congrArg (fun z => (pIso.inv ≫ Φ.map δ ≫
          (Functor.commShiftIso Φ (1 : ℤ)).hom.app L) ≫ z) h).trans (Category.comp_id _))
  -- the transported normalization
  have hc' : ∀ n : ℕ, Φ.map c ≫ (Φ.map q ≫ pIso.hom) ≫ Pi.π g n =
      ((@DerivedCategory.TStructure.t (SheafOfModules.{wModule} O) _ _ h₂).truncGEπ
        (-(n : ℤ))).app (Φ.obj E) := by
    intro n
    have hi := hcmpiso (-(n : ℤ)) E
    have hπ := Stacks.TStructureTransport.π_truncGEComparison t1 t2 Φ hGE (-(n : ℤ)) E
    have hιhom : (ι n).hom =
        inv (Stacks.TStructureTransport.truncGEComparison t1 t2 Φ hGE (-(n : ℤ)) E) := rfl
    rw [Category.assoc, hpIso n, ← Φ.map_comp_assoc, ← Φ.map_comp_assoc, Category.assoc,
      hc n, hιhom]
    exact (IsIso.comp_inv_eq
      (Stacks.TStructureTransport.truncGEComparison t1 t2 Φ hGE (-(n : ℤ)) E)).2 hπ.symm
  -- the transported vanishing
  have hvan' : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      Cov V hV 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ) (m : ℤ),
        degreeBound V hV m < (p : ℤ) →
          IsZero (Stacks.Cohomology.moduleCohomology O (𝒰.X i) p
            ((@DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) _ _ h₂
              (m - (p : ℤ))).obj (Φ.obj E))) := by
    intro V hV 𝒰 h𝒰 i p m hm
    exact Stacks.Cohomology.isZero_moduleCohomology_of_iso O (𝒰.X i) p
      ((Stacks.DerivedModel.modelHomologyIso hD h₂ (m - (p : ℤ))).app E)
      (vanishing V hV 𝒰 h𝒰 i p m hm)
  -- apply the standard-model statement and reflect
  have hkey := Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower
    O (Φ.obj E) B basisCover degreeBound Cov Cov_isCover Cov_cofinal hvan'
    (Φ.obj L) (Φ.map c) (Φ.map q ≫ pIso.hom)
    (pIso.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L) hL' hc'
  exact isIso_of_reflects_iso c Φ

end Stacks.TruncationTower

/-! ### Tag 08D3: the instance for a scheme -/

namespace Stacks.TruncationTower

/-- Let `X` be a scheme and `E` an object of the derived category of `𝒪_X`-modules whose
cohomology sheaves are quasi-coherent. Then the canonical map from `E` to the derived limit `L` of
the tower `τ_{≥ -n}E`, presented by a distinguished triangle whose structure maps compose with `c`
to the truncation maps, is an isomorphism. -/
theorem isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherent
    (X : AlgebraicGeometry.Scheme.{u}) (E : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    [hprod : HasProduct fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩]
    (L : DerivedCategory X.Modules) (c : E ⟶ L)
    (q : L ⟶ ∏ᶜ fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk q (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) (n + 1) ≫
            (truncGETower X.Modules E).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory X.Modules))
    (hc : ∀ n : ℕ, c ≫ q ≫ Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  refine isIso_to_isDerivedLimit_truncGETower
    (hD := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X) (hP := hprod)
    X.ringCatSheaf E X.affineOpens
    (fun U => ⟨X.affineZeroHypercover U, X.affineZeroHypercover_sieve₀_mem U,
      fun i => X.isAffineOpen_affineZeroHypercover_X U i⟩)
    (fun _ _ _ => 0) (fun V _ => X.affineCoverings V)
    (fun _ _ _ hU => X.sieve₀_mem_of_mem_affineCoverings hU)
    (fun _ _ U hU => by
      obtain ⟨W, hW, hh⟩ := X.exists_mem_affineCoverings_nonempty_hom U hU
      exact ⟨W, hW, hh⟩)
    ?_ L c q δ hL hc
  intro V hV 𝒰 h𝒰 i p m hm
  exact Stacks.Cohomology.isZero_moduleCohomology_of_isAffineOpen X _ (hE (m - (p : ℤ)))
    (𝒰.X i) (X.isAffineOpen_of_mem_affineCoverings h𝒰 i) p (by exact_mod_cast hm)

end Stacks.TruncationTower

end
