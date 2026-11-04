module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubfunctorFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleFromCompletionSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismEqualityFromCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties

/-!
# Relations detected by an open complement and a formal completion

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian
algebraic space over `S`, let `T ⊆ |X|` be a closed subset and let `s, t : R ⟶ U` be two
morphisms of algebraic spaces over `X` with `R` and `U` locally of finite type over `X`.
**Stacks 0AR8** says that if the base change of `s` and `t` to `X ∖ T` is an étale equivalence
relation and the formal completion `(t_{/T}, s_{/T})` is an equivalence relation, then
`(t, s) : R ⟶ U ×_X U` is an étale equivalence relation. The second of those hypotheses is read
here as asking for an *étale* equivalence relation: under the literal reading the statement is
false, already for `X = Spec k`, `T = |X|`, `U = 𝔸¹`, `R = U ×_X U` and `(t, s)` the identity.

## Main definitions

* `AlgebraicGeometry.FormalSpace.relationMap` is the morphism `(t, s) : R ⟶ U ×_X U` attached
  to a pair of morphisms `s, t : R ⟶ U` over `X`.
* `AlgebraicGeometry.FormalSpace.compositionMap` is the morphism
  `(t ∘ pr₀, s ∘ pr₁) : R ×_{s, U, t} R ⟶ U ×_X U` whose factorization through `(t, s)` is the
  transitivity axiom.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_section_of_openComplement_and_completion` and
  `AlgebraicGeometry.FormalSpace.isIso_of_openComplement_and_completion`: Stacks 0AR6 run on
  the identity of its target. A monomorphism locally of finite type onto a locally Noetherian
  algebraic space which admits a section over the open complement of `T` and over the
  completion along `T` admits a section, and is therefore an isomorphism.
* `AlgebraicGeometry.FormalSpace.mono_of_openComplement_and_completion`: a morphism of
  algebraic spaces over `S` whose relative diagonal admits those two factorizations is a
  monomorphism.
* `AlgebraicGeometry.FormalSpace.mono_of_proj_eq_on_openComplement_and_completion`: the same
  with the two factorizations replaced by agreement of the two projections of `R ×_P R`.
* `AlgebraicGeometry.FormalSpace.mono_relationMap_of_openComplement_and_completion`: the same
  statement for `(t, s) : R ⟶ U ×_X U`.
* `AlgebraicGeometry.FormalSpace.exists_composition_of_openComplement_and_completion`: the
  composition morphism factors through `(t, s)` once it does so over the open complement of `T`
  and over the completion along `T`.
* `AlgebraicGeometry.FormalSpace.isEquivalenceRelation_of_exists_factorizations`: `(t, s)` is
  an equivalence relation once it is a monomorphism and the relative diagonal of `U` over `X`,
  the swapped relation and the composition morphism all factor through it.
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_relationMap` and
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_pullback_self`: `(t, s)` is locally of
  finite type, and the fibre products of `R` with itself over `U` and over `U ×_X U` are locally
  Noetherian.
* `AlgebraicGeometry.FormalSpace.exists_factorization_of_openComplement_and_completionSheaf`:
  Stacks 0AR6 with both of its hypotheses read on the open subspace cut out by the complement
  of the closed subset and on the completion of Stacks 0AMC.
* `AlgebraicGeometry.FormalSpace.isPullback_ι_openSubspaceOfPoints_compl`: the subspace cut out
  by the complement of the inverse image of `T` is the base change of `X ∖ T`.
* `AlgebraicGeometry.FormalSpace.isPullback_completionSheafRestrict_of_isPullback`: completion
  commutes with fibre products.
* `AlgebraicGeometry.FormalSpace.isEquivalenceRelation_of_openComplement_and_completionSheaf`:
  the equivalence-relation half of Stacks 0AR8.
* `AlgebraicGeometry.FormalSpace.isEtaleEquivalenceRelation_of_openComplement_and_completion`:
  Stacks 0AR8, the equivalence-relation half together with étaleness of `s` and `t`.

## References

* [Stacks Project, Tag 0AR8](https://stacks.math.columbia.edu/tag/0AR8)
* [Stacks Project, Tag 0AR6](https://stacks.math.columbia.edu/tag/0AR6)
* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

/-! ### A monomorphism criterion through the relative diagonal -/

/-- A morphism whose relative diagonal admits a section is a monomorphism. -/
theorem mono_of_section_diagonal {C : Type*} [Category C] {A P : C} (j : A ⟶ P)
    [HasPullback j j] (v : pullback j j ⟶ A) (hv : v ≫ pullback.diagonal j = 𝟙 _) :
    Mono j := by
  have : IsSplitEpi (pullback.diagonal j) := IsSplitEpi.mk' ⟨v, hv⟩
  exact (pullback.isIso_diagonal_iff j).mp (isIso_of_mono_of_isSplitEpi _)

/-- A morphism into a kernel pair of `j` whose two components agree factors through any common
section of the two projections of the kernel pair, in particular through the relative
diagonal. -/
theorem exists_factorization_of_isPullback_diagonal {C : Type*} [Category C] {A P Q W : C}
    {p q : Q ⟶ A} {j : A ⟶ P} (h : IsPullback p q j j) (d : A ⟶ Q)
    (hdp : d ≫ p = 𝟙 A) (hdq : d ≫ q = 𝟙 A) (w : W ⟶ Q) (hw : w ≫ p = w ≫ q) :
    ∃ v : W ⟶ A, v ≫ d = w := by
  refine ⟨w ≫ p, h.hom_ext ?_ ?_⟩
  · simp only [Category.assoc, hdp, Category.comp_id]
  · simpa only [Category.assoc, hdq, Category.comp_id] using hw

/-- A morphism into `A ×_P A` whose two projections agree factors through the relative
diagonal of `j : A ⟶ P`. -/
theorem exists_factorization_diagonal {C : Type*} [Category C] {A P W : C} (j : A ⟶ P)
    [HasPullback j j] (w : W ⟶ pullback j j)
    (hw : w ≫ pullback.fst j j = w ≫ pullback.snd j j) :
    ∃ v : W ⟶ A, v ≫ pullback.diagonal j = w :=
  exists_factorization_of_isPullback_diagonal (IsPullback.of_hasPullback j j)
    (pullback.diagonal j) (pullback.diagonal_fst j) (pullback.diagonal_snd j) w hw

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factorizations through the subspace cut out by a set of points -/

/-- A morphism all of whose points lie in `W` factors through the subspace of `F` cut out by
`W`. -/
theorem exists_factorization_openSubspaceOfPoints {A F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : A ⟶ F) (W : Set (Space.points B S hS F))
    (hk : Set.range (Space.pointsMap B S hS A k) ⊆ W) :
    ∃ v : A ⟶ (Space.openSubspaceOfPoints B S hS F W).toFunctor,
      v ≫ (Space.openSubspaceOfPoints B S hS F W).ι = k :=
  ⟨Subfunctor.lift k ((Space.range_le_openSubspaceOfPoints_range_pointsMap k).trans
    (Space.openSubspaceOfPoints_mono B S hS hk)), rfl⟩

/-- A subfunctor which is the inverse image of a subfunctor is its base change, and any
morphism of subfunctors lying over the given morphism exhibits the cartesian square. -/
private theorem isPullback_ι_of_eq_preimage {C : Type*} [Category C] {X Y : C ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X) (Z' : Subfunctor Y) (hZ' : Z' = Z.preimage f)
    (r : Z'.toFunctor ⟶ Z.toFunctor) (hr : r ≫ Z.ι = Z'.ι ≫ f) :
    IsPullback Z'.ι r f Z.ι := by
  subst hZ'
  have hr' : r = Z.fromPreimage f :=
    (cancel_mono Z.ι).mp (hr.trans (Subfunctor.fromPreimage_ι Z f).symm)
  subst hr'
  exact (Subfunctor.isPullback_preimage f Z).flip

/-- For a morphism `g : F' ⟶ F` and a set `T` of points of `F`, the subspace of `F'` cut out by
the complement of the inverse image of `T` is the fibre product `F' ×_F (F ∖ T)`. -/
theorem isPullback_ι_openSubspaceOfPoints_compl
    {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F' ⟶ F) (T : Set (Space.points B S hS F))
    (r : (Space.openSubspaceOfPoints B S hS F' (Space.pointsMap B S hS F' g ⁻¹' T)ᶜ).toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS F Tᶜ).toFunctor)
    (hr : r ≫ (Space.openSubspaceOfPoints B S hS F Tᶜ).ι =
      (Space.openSubspaceOfPoints B S hS F' (Space.pointsMap B S hS F' g ⁻¹' T)ᶜ).ι ≫ g) :
    IsPullback (Space.openSubspaceOfPoints B S hS F' (Space.pointsMap B S hS F' g ⁻¹' T)ᶜ).ι r g
      (Space.openSubspaceOfPoints B S hS F Tᶜ).ι :=
  isPullback_ι_of_eq_preimage g _ _
    (by rw [Space.preimage_openSubspaceOfPoints, Set.preimage_compl]) r hr

/-- Étaleness of the restriction of a morphism to the subspaces cut out by two sets of points
only depends on those sets, not on the way they are written. -/
theorem isEtale_openSubspaceOfPointsRestrict_of_eq
    {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F' ⟶ F)
    {A A' : Set (Space.points B S hS F')} {W W' : Set (Space.points B S hS F)}
    (hA : A = A') (hW : W = W')
    (h : A ⊆ Space.pointsMap B S hS F' g ⁻¹' W)
    (h' : A' ⊆ Space.pointsMap B S hS F' g ⁻¹' W')
    (hE : Space.IsEtale B S hS (Space.openSubspaceOfPointsRestrict B S hS g A W h)) :
    Space.IsEtale B S hS (Space.openSubspaceOfPointsRestrict B S hS g A' W' h') := by
  subst hA hW
  exact hE

/-! ### Stacks 0AR6 with its completion hypothesis read on the completion sheaf -/

/-- The inclusion of a completion into the universe lift is natural for the restriction
morphisms of completions along an arbitrary inclusion of sets of points. -/
@[reassoc]
theorem completionSheafRestrict_comp_completionToULift
    {Z' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z')
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z) (f : Z' ⟶ Z)
    (T' : Set (Space.points B S hS Z')) (T : Set (Space.points B S hS Z))
    (h : T' ⊆ Space.pointsMap B S hS Z' f ⁻¹' T) :
    (Space.completionSheafRestrict B S hS f T' T h).hom ≫ completionToULift B S hS Z hZ T =
      completionToULift B S hS Z' hZ' T' ≫ Functor.whiskerRight f uliftFunctor.{u + 1} := by
  have hw := congrArg (fun φ : Space.completionSheaf B S hS Z' T' ⟶
      Space.sheafifiedULift B S hS Z ↦ φ.hom)
    (Space.completionSheafRestrict_comp_inclusion B S hS f T' T h)
  rw [← cancel_mono (Space.sheafifiedULiftIso B S hS Z hZ).hom]
  simp only [completionToULift, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rwa [← Space.sheafifiedULiftMap_hom_eq B S hS hZ' hZ f]

/-- If `f_{/T}` factors through `g_{/T}` as morphisms of completions, then the inclusion of the
completion subfunctor of the source composed with `f` factors through `g`. -/
theorem exists_factorization_completionSubfunctor_of_restrict
    {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    (f : W ⟶ Y) (g : Z ⟶ Y) (T : Set (Space.points B S hS Y))
    (TW : Set (Space.points B S hS W)) (TZ : Set (Space.points B S hS Z))
    (hTW : TW ⊆ Space.pointsMap B S hS W f ⁻¹' T)
    (hTZ : TZ ⊆ Space.pointsMap B S hS Z g ⁻¹' T)
    (h : ∃ w : Space.completionSheaf B S hS W TW ⟶ Space.completionSheaf B S hS Z TZ,
      w ≫ Space.completionSheafRestrict B S hS g TZ T hTZ =
        Space.completionSheafRestrict B S hS f TW T hTW) :
    ∃ v : (Space.completionSubfunctor B S hS W TW).toFunctor ⟶ Z ⋙ uliftFunctor.{u + 1},
      v ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
        (Space.completionSubfunctor B S hS W TW).ι ≫
          Functor.whiskerRight f uliftFunctor.{u + 1} := by
  obtain ⟨w, hw⟩ := h
  have hw' := congrArg (fun φ : Space.completionSheaf B S hS W TW ⟶
      Space.completionSheaf B S hS Y T ↦ φ.hom) hw
  refine exists_factorization_completionSubfunctor_of_completionSheaf B S hS hW f g TW
    ⟨w.hom ≫ completionToULift B S hS Z hZ TZ, ?_⟩
  rw [Category.assoc, ← completionSheafRestrict_comp_completionToULift B S hS hZ hY g TZ T hTZ,
    ← Category.assoc,
    show w.hom ≫ (Space.completionSheafRestrict B S hS g TZ T hTZ).hom =
      (Space.completionSheafRestrict B S hS f TW T hTW).hom from hw']
  exact completionSheafRestrict_comp_completionToULift B S hS hW hY f TW T hTW

/-- Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic spaces over `S` with `X`
locally Noetherian and `g` a monomorphism locally of finite type, and let `T_X ⊆ |X|` be closed
and carried into a set `T` of points of `Y` by `f`. If `f` restricted to `X ∖ T_X` factors
through `g`, and `f_{/T_X}` factors through `g_{/T_Z}` as morphisms of completions, then `f`
factors through `g`. -/
theorem exists_factorization_of_openComplement_and_completionSheaf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (T : Set (Space.points B S hS Y)) (TX : Set (Space.points B S hS X))
    (TZ : Set (Space.points B S hS Z))
    (hTX : TX ⊆ Space.pointsMap B S hS X f ⁻¹' T)
    (hTZ : TZ ⊆ Space.pointsMap B S hS Z g ⁻¹' T) (hTXclosed : IsClosed TX)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hgmono : Mono g) (hgft : Space.IsLocallyOfFiniteType B S hS g)
    (hopen : ∃ v : (Space.openSubspaceOfPoints B S hS X TXᶜ).toFunctor ⟶ Z,
      v ≫ g = (Space.openSubspaceOfPoints B S hS X TXᶜ).ι ≫ f)
    (hcompletion : ∃ w : Space.completionSheaf B S hS X TX ⟶ Space.completionSheaf B S hS Z TZ,
      w ≫ Space.completionSheafRestrict B S hS g TZ T hTZ =
        Space.completionSheafRestrict B S hS f TX T hTX) :
    ∃ v : X ⟶ Z, v ≫ g = f := by
  refine exists_factorization_of_openComplement_and_completion B S hS hX hY hZ f g TX
    hTXclosed hXnoeth hgmono hgft ?_ ?_
  · rw [openSubspacesOrderIso_symm_compl B S hS hX TX hTXclosed]
    exact hopen
  · exact exists_factorization_completionSubfunctor_of_restrict B S hS
      hX.isSheaf hY.isSheaf hZ.isSheaf f g T TX TZ hTX hTZ hcompletion

/-! ### Stacks 0AR6 on the identity of its target -/

/-- Let `g : Z ⟶ Y` be a monomorphism locally
of finite type between algebraic spaces over `S` with `Y` locally Noetherian, and let
`T ⊆ |Y|` be closed. If the inclusion of the open subspace `Y ∖ T` and the inclusion of the
completion `Y_{/T}` both factor through `g`, then `g` admits a section. -/
theorem exists_section_of_openComplement_and_completion
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (g : Z ⟶ Y)
    (T : Set (Space.points B S hS Y)) (hT : IsClosed T)
    (hYnoeth : Space.HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hgmono : Mono g) (hgft : Space.IsLocallyOfFiniteType B S hS g)
    (hopen : ∃ v : (Space.openSubspaceOfPoints B S hS Y Tᶜ).toFunctor ⟶ Z,
      v ≫ g = (Space.openSubspaceOfPoints B S hS Y Tᶜ).ι)
    (hcompletion : ∃ v : completionOfAlgebraicSpace B S hS hY T ⟶ upliftedSheaf Z hZ,
      v ≫ upliftedMap B S hS hZ hY g = completionOfAlgebraicSpaceInclusion B S hS hY T) :
    ∃ v : Y ⟶ Z, v ≫ g = 𝟙 Y := by
  refine exists_factorization_of_openComplement_and_completion B S hS hY hY hZ (𝟙 Y) g T hT
    hYnoeth hgmono hgft ?_ ?_
  · rw [openSubspacesOrderIso_symm_compl B S hS hY T hT]
    obtain ⟨v, hv⟩ := hopen
    exact ⟨v, by rw [hv, Category.comp_id]⟩
  · refine exists_factorization_completionSubfunctor_of_completion B S hS hY hY hZ (𝟙 Y) g T ?_
    obtain ⟨v, hv⟩ := hcompletion
    exact ⟨v, by rw [hv, upliftedMap_id, Category.comp_id]⟩

/-- A monomorphism locally of finite type onto a locally Noetherian algebraic space which the
open complement of `T` and the completion along `T` both factor through is an isomorphism. -/
theorem isIso_of_openComplement_and_completion
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (g : Z ⟶ Y)
    (T : Set (Space.points B S hS Y)) (hT : IsClosed T)
    (hYnoeth : Space.HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hgmono : Mono g) (hgft : Space.IsLocallyOfFiniteType B S hS g)
    (hopen : ∃ v : (Space.openSubspaceOfPoints B S hS Y Tᶜ).toFunctor ⟶ Z,
      v ≫ g = (Space.openSubspaceOfPoints B S hS Y Tᶜ).ι)
    (hcompletion : ∃ v : completionOfAlgebraicSpace B S hS hY T ⟶ upliftedSheaf Z hZ,
      v ≫ upliftedMap B S hS hZ hY g = completionOfAlgebraicSpaceInclusion B S hS hY T) :
    IsIso g := by
  obtain ⟨v, hv⟩ := exists_section_of_openComplement_and_completion B S hS hY hZ g T hT
    hYnoeth hgmono hgft hopen hcompletion
  have : IsSplitEpi g := IsSplitEpi.mk' ⟨v, hv⟩
  have := hgmono
  exact isIso_of_mono_of_isSplitEpi g

/-! ### The monomorphism clause -/

/-- The source of the relative diagonal of a morphism of algebraic spaces over `S` is an
algebraic space. -/
theorem isAlgebraicSpace_diagonalObj {R P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P) (j : R ⟶ P) :
    IsAlgebraicSpace B S hS (pullback j j) :=
  isAlgebraicSpace_pullback B S hS j j hR hR hP

/-- Let `j : R ⟶ P` be a morphism of algebraic
spaces over `S` and let `T ⊆ |R ×_P R|` be a closed subset with `R ×_P R` locally Noetherian.
If the inclusion of the open subspace `(R ×_P R) ∖ T` and the inclusion of the completion
`(R ×_P R)_{/T}` both factor through the relative diagonal `Δ_j : R ⟶ R ×_P R`, then `j` is a
monomorphism. -/
theorem mono_of_openComplement_and_completion
    {R P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P) (j : R ⟶ P)
    (T : Set (Space.points B S hS (pullback j j))) (hT : IsClosed T)
    (hnoeth : Space.HasEtaleLocalProperty B S hS (pullback j j)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hopen : ∃ v : (Space.openSubspaceOfPoints B S hS (pullback j j) Tᶜ).toFunctor ⟶ R,
      v ≫ pullback.diagonal j =
        (Space.openSubspaceOfPoints B S hS (pullback j j) Tᶜ).ι)
    (hcompletion : ∃ v : completionOfAlgebraicSpace B S hS
        (isAlgebraicSpace_diagonalObj B S hS hR hP j) T ⟶ upliftedSheaf R hR,
      v ≫ upliftedMap B S hS hR (isAlgebraicSpace_diagonalObj B S hS hR hP j)
          (pullback.diagonal j) =
        completionOfAlgebraicSpaceInclusion B S hS
          (isAlgebraicSpace_diagonalObj B S hS hR hP j) T) :
    Mono j := by
  obtain ⟨v, hv⟩ := exists_section_of_openComplement_and_completion B S hS
    (isAlgebraicSpace_diagonalObj B S hS hR hP j) hR (pullback.diagonal j) T hT hnoeth
    inferInstance
    (Space.presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS _
      (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS j hR))
    hopen hcompletion
  exact mono_of_section_diagonal j v hv

/-- A morphism of sheaves of large sets into the universe lift of `R ×_P R` whose two
projections agree factors through the universe lift of the relative diagonal. -/
theorem exists_factorization_upliftedDiagonal
    {R P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R)
    (hP : IsAlgebraicSpace B S hS P) (j : R ⟶ P)
    {F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (w : F ⟶ upliftedSheaf (pullback j j) (isAlgebraicSpace_diagonalObj B S hS hR hP j))
    (hw : w ≫ upliftedMap B S hS (isAlgebraicSpace_diagonalObj B S hS hR hP j) hR
          (pullback.fst j j) =
        w ≫ upliftedMap B S hS (isAlgebraicSpace_diagonalObj B S hS hR hP j) hR
          (pullback.snd j j)) :
    ∃ v : F ⟶ upliftedSheaf R hR,
      v ≫ upliftedMap B S hS hR (isAlgebraicSpace_diagonalObj B S hS hR hP j)
        (pullback.diagonal j) = w := by
  obtain ⟨v, hv⟩ := exists_factorization_of_isPullback_diagonal
    (isPullback_uliftPresheaf_map B S hS (IsPullback.of_hasPullback j j))
    ((upliftFunctor B S hS).map (pullback.diagonal j))
    (by rw [← Functor.map_comp, pullback.diagonal_fst, CategoryTheory.Functor.map_id])
    (by rw [← Functor.map_comp, pullback.diagonal_snd, CategoryTheory.Functor.map_id])
    w.hom (congrArg (fun φ : F ⟶ upliftedSheaf R hR ↦ φ.hom) hw)
  exact ⟨ObjectProperty.homMk v, Sheaf.hom_ext hv⟩

/-- Let `j : R ⟶ P` be a morphism of algebraic spaces over `S` and let
`T ⊆ |R ×_P R|` be a closed subset with `R ×_P R` locally Noetherian. If the two projections
`R ×_P R ⟶ R` agree on the open subspace `(R ×_P R) ∖ T` and on the completion
`(R ×_P R)_{/T}`, then `j` is a monomorphism. -/
theorem mono_of_proj_eq_on_openComplement_and_completion
    {R P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P) (j : R ⟶ P)
    (T : Set (Space.points B S hS (pullback j j))) (hT : IsClosed T)
    (hnoeth : Space.HasEtaleLocalProperty B S hS (pullback j j)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hopen : (Space.openSubspaceOfPoints B S hS (pullback j j) Tᶜ).ι ≫ pullback.fst j j =
      (Space.openSubspaceOfPoints B S hS (pullback j j) Tᶜ).ι ≫ pullback.snd j j)
    (hcompletion :
      completionOfAlgebraicSpaceInclusion B S hS
            (isAlgebraicSpace_diagonalObj B S hS hR hP j) T ≫
          upliftedMap B S hS (isAlgebraicSpace_diagonalObj B S hS hR hP j) hR
            (pullback.fst j j) =
        completionOfAlgebraicSpaceInclusion B S hS
            (isAlgebraicSpace_diagonalObj B S hS hR hP j) T ≫
          upliftedMap B S hS (isAlgebraicSpace_diagonalObj B S hS hR hP j) hR
            (pullback.snd j j)) :
    Mono j :=
  mono_of_openComplement_and_completion B S hS hR hP j T hT hnoeth
    (exists_factorization_diagonal j _ hopen)
    (exists_factorization_upliftedDiagonal B S hS hR hP j _ hcompletion)

/-! ### The two morphisms attached to a pair `s, t : R ⟶ U` over `X` -/

section Relation

variable {X R U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism `(t, s) : R ⟶ U ×_X U` attached to a pair of morphisms `s, t : R ⟶ U` of
algebraic spaces over `X`. Its source is the first component, as in Stacks 0AR8. -/
abbrev relationMap (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU) :
    R ⟶ pullback qU qU :=
  pullback.lift t s hcomm

/-- The morphism `(t ∘ pr₀, s ∘ pr₁) : R ×_{s, U, t} R ⟶ U ×_X U`. A factorization of it
through `AlgebraicGeometry.FormalSpace.relationMap` is the transitivity axiom for the relation
cut out by `s` and `t`. -/
abbrev compositionMap (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU) :
    pullback s t ⟶ pullback qU qU :=
  pullback.lift (pullback.fst s t ≫ t) (pullback.snd s t ≫ s)
    (by rw [Category.assoc, hcomm, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, hcomm])

/-- The first component of `AlgebraicGeometry.FormalSpace.relationMap` is `t`. -/
@[simp]
theorem relationMap_fst (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU) :
    relationMap B S hS qU s t hcomm ≫ pullback.fst qU qU = t :=
  pullback.lift_fst _ _ _

/-- The second component of `AlgebraicGeometry.FormalSpace.relationMap` is `s`. -/
@[simp]
theorem relationMap_snd (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU) :
    relationMap B S hS qU s t hcomm ≫ pullback.snd qU qU = s :=
  pullback.lift_snd _ _ _

/-! ### What hypothesis (1) of Stacks 0AR8 gives -/

/-- `(t, s) : R ⟶ U ×_X U` is locally of finite type as soon as `R` is locally of finite type
over `X`. -/
theorem isLocallyOfFiniteType_relationMap
    (qR : R ⟶ X) (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU) (ht : t ≫ qU = qR)
    (hR : IsAlgebraicSpace B S hS R) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X)
    (hqR : Space.IsLocallyOfFiniteType B S hS qR) :
    Space.IsLocallyOfFiniteType B S hS (relationMap B S hS qU s t hcomm) := by
  refine Space.isLocallyOfFiniteType_of_comp B S hS hR
    (isAlgebraicSpace_pullback B S hS qU qU hU hU hX) hX _ (pullback.fst qU qU ≫ qU) ?_
  rwa [← Category.assoc, relationMap_fst, ht]

/-- A morphism `a : R ⟶ U` over `X` is locally of finite type as soon as `R` is locally of
finite type over `X`. -/
theorem isLocallyOfFiniteType_of_comp_structure
    (qR : R ⟶ X) (qU : U ⟶ X) (a : R ⟶ U) (ha : a ≫ qU = qR)
    (hR : IsAlgebraicSpace B S hS R) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X)
    (hqR : Space.IsLocallyOfFiniteType B S hS qR) :
    Space.IsLocallyOfFiniteType B S hS a :=
  Space.isLocallyOfFiniteType_of_comp B S hS hR hU hX a qU (by rwa [ha])

/-- A fibre product of `R` with itself over a morphism out of `R` which is locally of finite
type is locally Noetherian, when `R` is locally of finite type over the locally Noetherian
`X`. -/
theorem isLocallyNoetherian_pullback_self
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (qR : R ⟶ X) (a b : R ⟶ P)
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P)
    (hX : IsAlgebraicSpace B S hS X)
    (hb : Space.IsLocallyOfFiniteType B S hS b)
    (hqR : Space.IsLocallyOfFiniteType B S hS qR)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V)) :
    Space.HasEtaleLocalProperty B S hS (pullback a b)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) := by
  have hpb : IsAlgebraicSpace B S hS (pullback a b) :=
    isAlgebraicSpace_pullback B S hS a b hR hR hP
  have hfst : Space.IsLocallyOfFiniteType B S hS (pullback.fst a b) :=
    Space.IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback a b) hR hP hb
  exact Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hpb hX
    (pullback.fst a b ≫ qR)
    (Space.isLocallyOfFiniteType_comp B S hS hpb hR hX _ qR hfst hqR) hXnoeth

/-- If `(t, s) : R ⟶ U ×_X U` is a monomorphism then `t` and `s` are jointly monic. -/
theorem jointlyMono₂_of_mono_relationMap (qU : U ⟶ X) (s t : R ⟶ U)
    (hcomm : t ≫ qU = s ≫ qU) (hmono : Mono (relationMap B S hS qU s t hcomm)) :
    JointlyMono₂ t s := by
  refine ⟨fun {Y} f g hft hfs ↦ (cancel_mono (relationMap B S hS qU s t hcomm)).mp ?_⟩
  refine pullback.hom_ext ?_ ?_
  · simpa only [Category.assoc, relationMap_fst] using hft
  · simpa only [Category.assoc, relationMap_snd] using hfs

/-! ### The equivalence-relation conclusion from the three factorizations -/

/-- Let `s, t : R ⟶ U` be
morphisms of algebraic spaces over `X` with `(t, s) : R ⟶ U ×_X U` a monomorphism. If the
relative diagonal of `U` over `X`, the swapped relation `(s, t)` and the composition morphism
`(t ∘ pr₀, s ∘ pr₁)` all factor through `(t, s)`, then `(t, s)` is an equivalence relation. -/
theorem isEquivalenceRelation_of_exists_factorizations
    (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU)
    (hmono : Mono (relationMap B S hS qU s t hcomm))
    (hrefl : ∃ v : U ⟶ R,
      v ≫ relationMap B S hS qU s t hcomm = pullback.diagonal qU)
    (hsymm : ∃ v : R ⟶ R,
      v ≫ relationMap B S hS qU s t hcomm = relationMap B S hS qU t s hcomm.symm)
    (htrans : ∃ v : pullback s t ⟶ R,
      v ≫ relationMap B S hS qU s t hcomm = compositionMap B S hS qU s t hcomm) :
    IsEquivalenceRelation t s := by
  obtain ⟨refl, hrefl⟩ := hrefl
  obtain ⟨inv, hinv⟩ := hsymm
  obtain ⟨ctr, hctr⟩ := htrans
  have hcomponents : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : Y ⟶ R)
      (f : Y ⟶ pullback qU qU), v ≫ relationMap B S hS qU s t hcomm = f →
      v ≫ t = f ≫ pullback.fst qU qU ∧ v ≫ s = f ≫ pullback.snd qU qU := by
    intro Y v f hv
    exact ⟨by rw [← hv, Category.assoc, relationMap_fst],
      by rw [← hv, Category.assoc, relationMap_snd]⟩
  obtain ⟨hrt, hrs⟩ := hcomponents refl _ hrefl
  obtain ⟨hit, his⟩ := hcomponents inv _ hinv
  obtain ⟨hct, hcs⟩ := hcomponents ctr _ hctr
  have hjoint : JointlyMono₂ t s :=
    jointlyMono₂_of_mono_relationMap B S hS qU s t hcomm hmono
  let hReflexive : ReflexiveRelation t s :=
    { toJointlyMono₂ := hjoint
      r := refl
      reflexivity₁ := by simpa using hrt
      reflexivity₂ := by simpa using hrs }
  let hSymmetric : SymmetricRelation t s :=
    { toJointlyMono₂ := hjoint
      s := inv
      symmetry₁ := by simpa using hit
      symmetry₂ := by simpa using his }
  let hTransitive : TransitiveRelation t s :=
    { toJointlyMono₂ := hjoint
      c := pullback.cone s t
      isLimit := pullback.isLimit s t
      t := ctr
      transitivity₁ := by simpa using hct
      transitivity₂ := by simpa using hcs }
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := hReflexive
      __ := hSymmetric
      __ := hTransitive }

/-- If the two projections of `R ×_{U ×_X U} R` agree on the open complement of `T` and on
the completion along `T`, and that fibre product is locally Noetherian, then
`(t, s) : R ⟶ U ×_X U` is a monomorphism. -/
theorem mono_relationMap_of_openComplement_and_completion
    (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU)
    (hR : IsAlgebraicSpace B S hS R) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS (pullback (relationMap B S hS qU s t hcomm)
      (relationMap B S hS qU s t hcomm))))
    (hT : IsClosed T)
    (hnoeth : Space.HasEtaleLocalProperty B S hS
      (pullback (relationMap B S hS qU s t hcomm) (relationMap B S hS qU s t hcomm))
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hopen : (Space.openSubspaceOfPoints B S hS
          (pullback (relationMap B S hS qU s t hcomm)
            (relationMap B S hS qU s t hcomm)) Tᶜ).ι ≫
        pullback.fst (relationMap B S hS qU s t hcomm) (relationMap B S hS qU s t hcomm) =
      (Space.openSubspaceOfPoints B S hS
          (pullback (relationMap B S hS qU s t hcomm)
            (relationMap B S hS qU s t hcomm)) Tᶜ).ι ≫
        pullback.snd (relationMap B S hS qU s t hcomm) (relationMap B S hS qU s t hcomm))
    (hcompletion :
      completionOfAlgebraicSpaceInclusion B S hS
            (isAlgebraicSpace_diagonalObj B S hS hR
              (isAlgebraicSpace_pullback B S hS qU qU hU hU hX)
              (relationMap B S hS qU s t hcomm)) T ≫
          upliftedMap B S hS
            (isAlgebraicSpace_diagonalObj B S hS hR
              (isAlgebraicSpace_pullback B S hS qU qU hU hU hX)
              (relationMap B S hS qU s t hcomm)) hR
            (pullback.fst (relationMap B S hS qU s t hcomm)
              (relationMap B S hS qU s t hcomm)) =
        completionOfAlgebraicSpaceInclusion B S hS
            (isAlgebraicSpace_diagonalObj B S hS hR
              (isAlgebraicSpace_pullback B S hS qU qU hU hU hX)
              (relationMap B S hS qU s t hcomm)) T ≫
          upliftedMap B S hS
            (isAlgebraicSpace_diagonalObj B S hS hR
              (isAlgebraicSpace_pullback B S hS qU qU hU hU hX)
              (relationMap B S hS qU s t hcomm)) hR
            (pullback.snd (relationMap B S hS qU s t hcomm)
              (relationMap B S hS qU s t hcomm))) :
    Mono (relationMap B S hS qU s t hcomm) :=
  mono_of_proj_eq_on_openComplement_and_completion B S hS hR
    (isAlgebraicSpace_pullback B S hS qU qU hU hU hX)
    (relationMap B S hS qU s t hcomm) T hT hnoeth hopen hcompletion

/-! ### The transitivity clause -/

/-- Let `s, t : R ⟶ U` be morphisms of algebraic
spaces over `X` and let `T ⊆ |R ×_{s, U, t} R|` be a closed subset with `R ×_{s, U, t} R`
locally Noetherian. Assume `(t, s) : R ⟶ U ×_X U` is a monomorphism locally of finite type.
If `(t ∘ pr₀, s ∘ pr₁)` factors through `(t, s)` over the open complement of `T` and over the
completion along `T`, then it factors through `(t, s)`. -/
theorem exists_composition_of_openComplement_and_completion
    (qU : U ⟶ X) (s t : R ⟶ U) (hcomm : t ≫ qU = s ≫ qU)
    (hR : IsAlgebraicSpace B S hS R) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X)
    (hjmono : Mono (relationMap B S hS qU s t hcomm))
    (hjft : Space.IsLocallyOfFiniteType B S hS (relationMap B S hS qU s t hcomm))
    (T : Set (Space.points B S hS (pullback s t))) (hT : IsClosed T)
    (hnoeth : Space.HasEtaleLocalProperty B S hS (pullback s t)
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hopen : ∃ v : (Space.openSubspaceOfPoints B S hS (pullback s t) Tᶜ).toFunctor ⟶ R,
      v ≫ relationMap B S hS qU s t hcomm =
        (Space.openSubspaceOfPoints B S hS (pullback s t) Tᶜ).ι ≫
          compositionMap B S hS qU s t hcomm)
    (hcompletion : ∃ v : completionOfAlgebraicSpace B S hS
        (isAlgebraicSpace_pullback B S hS s t hR hR hU) T ⟶ upliftedSheaf R hR,
      v ≫ upliftedMap B S hS hR (isAlgebraicSpace_pullback B S hS qU qU hU hU hX)
          (relationMap B S hS qU s t hcomm) =
        completionOfAlgebraicSpaceInclusion B S hS
            (isAlgebraicSpace_pullback B S hS s t hR hR hU) T ≫
          upliftedMap B S hS (isAlgebraicSpace_pullback B S hS s t hR hR hU)
            (isAlgebraicSpace_pullback B S hS qU qU hU hU hX)
            (compositionMap B S hS qU s t hcomm)) :
    ∃ c : pullback s t ⟶ R, c ≫ relationMap B S hS qU s t hcomm =
      compositionMap B S hS qU s t hcomm := by
  refine exists_factorization_of_openComplement_and_completion B S hS
    (isAlgebraicSpace_pullback B S hS s t hR hR hU)
    (isAlgebraicSpace_pullback B S hS qU qU hU hU hX) hR
    (compositionMap B S hS qU s t hcomm) (relationMap B S hS qU s t hcomm) T hT hnoeth
    hjmono hjft ?_ ?_
  · rw [openSubspacesOrderIso_symm_compl B S hS
      (isAlgebraicSpace_pullback B S hS s t hR hR hU) T hT]
    exact hopen
  · exact exists_factorization_completionSubfunctor_of_completion B S hS
      (isAlgebraicSpace_pullback B S hS s t hR hR hU)
      (isAlgebraicSpace_pullback B S hS qU qU hU hU hX) hR
      (compositionMap B S hS qU s t hcomm) (relationMap B S hS qU s t hcomm) T hcompletion

/-! ### Index bookkeeping for the spaces over `X` -/

/-- For a morphism over `X`, the inverse image of the inverse image of `T` is the inverse image
of `T` along the structure morphism. -/
theorem preimage_pointsMap_preimage_of_comp {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : W ⟶ Y) (q : Y ⟶ Z) (qW : W ⟶ Z) (hm : m ≫ q = qW)
    (T : Set (Space.points B S hS Z)) :
    Space.pointsMap B S hS W m ⁻¹' (Space.pointsMap B S hS Y q ⁻¹' T) =
      Space.pointsMap B S hS W qW ⁻¹' T := by
  rw [← Set.preimage_comp, ← Space.pointsMap_comp, hm]

/-- A morphism over `X` carries the complement of the inverse image of `T` into the complement
of the inverse image of `T`. -/
theorem compl_subset_preimage_compl {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : W ⟶ Y) (q : Y ⟶ Z) (qW : W ⟶ Z) (hm : m ≫ q = qW)
    (T : Set (Space.points B S hS Z)) :
    (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ ⊆
      Space.pointsMap B S hS W m ⁻¹' (Space.pointsMap B S hS Y q ⁻¹' T)ᶜ := by
  rw [Set.preimage_compl, preimage_pointsMap_preimage_of_comp B S hS m q qW hm T]

/-- A morphism over `X` carries the inverse image of `T` into the inverse image of `T`. -/
theorem preimage_subset_preimage_of_comp {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : W ⟶ Y) (q : Y ⟶ Z) (qW : W ⟶ Z) (hm : m ≫ q = qW)
    (T : Set (Space.points B S hS Z)) :
    Space.pointsMap B S hS W qW ⁻¹' T ⊆
      Space.pointsMap B S hS W m ⁻¹' (Space.pointsMap B S hS Y q ⁻¹' T) :=
  (preimage_pointsMap_preimage_of_comp B S hS m q qW hm T).ge

/-- A morphism out of the open complement of the inverse image of `T` which lies over the
structure morphisms factors through the open complement of the inverse image of `T` in its
target. -/
theorem exists_factorization_openComplement {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (qW : W ⟶ Z) (qY : Y ⟶ Z) (T : Set (Space.points B S hS Z))
    (m : (Space.openSubspaceOfPoints B S hS W
        (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ).toFunctor ⟶ Y)
    (hm : m ≫ qY = (Space.openSubspaceOfPoints B S hS W
      (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ).ι ≫ qW) :
    ∃ v : (Space.openSubspaceOfPoints B S hS W
        (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ).toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS Y (Space.pointsMap B S hS Y qY ⁻¹' T)ᶜ).toFunctor,
      v ≫ (Space.openSubspaceOfPoints B S hS Y
        (Space.pointsMap B S hS Y qY ⁻¹' T)ᶜ).ι = m := by
  refine exists_factorization_openSubspaceOfPoints B S hS m _ ?_
  rw [Set.range_subset_iff]
  intro x hmem
  have hmemrange : Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS W
        (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ).ι x ∈
      Set.range (Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS W
        (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ).ι) := ⟨x, rfl⟩
  rw [Space.range_pointsMap_ι_openSubspaceOfPoints] at hmemrange
  exact hmemrange ((Space.preimage_pointsMap_eq_of_comm B S hS hm T).subset hmem)

/-! ### Étaleness away from `T` -/

/-- If the restriction of a morphism over `X` to the open complements of the inverse images of
`T` is étale, then so is its restriction `AlgebraicGeometry.Space.openComplementRestriction` to
the open complement of the inverse image of `T` in its target. -/
theorem isEtale_openComplementRestriction_of_restrict
    {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y) (q : Y ⟶ Z) (qW : W ⟶ Z)
    (ha : a ≫ q = qW) (T : Set (Space.points B S hS Z))
    (h : Space.IsEtale B S hS (Space.openSubspaceOfPointsRestrict B S hS a _ _
      (compl_subset_preimage_compl B S hS a q qW ha T))) :
    Space.IsEtale B S hS (Space.openComplementRestriction B S hS a
      (Space.pointsMap B S hS Y q ⁻¹' T)) :=
  isEtale_openSubspaceOfPointsRestrict_of_eq B S hS a
    (by rw [Set.preimage_compl, preimage_pointsMap_preimage_of_comp B S hS a q qW ha T]) rfl
    (compl_subset_preimage_compl B S hS a q qW ha T) Set.Subset.rfl h

/-- A morphism over `X` whose restriction to the open complements of the inverse images of `T`
is étale is étale at every point of its source whose image lies outside the inverse image of
`T`. -/
theorem isEtaleAt_of_isEtale_openSubspaceOfPointsRestrict
    {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hY : IsAlgebraicSpace B S hS Y) (a : W ⟶ Y) (q : Y ⟶ Z) (qW : W ⟶ Z)
    (ha : a ≫ q = qW) (T : Set (Space.points B S hS Z)) (hT : IsClosed T)
    (h : Space.IsEtale B S hS (Space.openSubspaceOfPointsRestrict B S hS a _ _
      (compl_subset_preimage_compl B S hS a q qW ha T)))
    (x : Space.points B S hS W)
    (hx : Space.pointsMap B S hS W a x ∉ Space.pointsMap B S hS Y q ⁻¹' T) :
    Space.IsEtaleAt B S hS a x := by
  have hxmem : x ∈ (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ := fun hmem ↦
    hx ((preimage_pointsMap_preimage_of_comp B S hS a q qW ha T).ge hmem)
  obtain ⟨x', hx'⟩ : x ∈ Set.range (Space.pointsMap B S hS _
      (Space.openSubspaceOfPoints B S hS W (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ).ι) := by
    rw [Space.range_pointsMap_ι_openSubspaceOfPoints]
    exact hxmem
  refine ⟨Space.openSubspaceOfPoints B S hS W (Space.pointsMap B S hS W qW ⁻¹' T)ᶜ,
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hW _
      (hT.preimage (Space.continuous_pointsMap B S hS qW)).isOpen_compl, x', hx', ?_⟩
  show Space.IsEtale B S hS (Space.openSubspaceOfPointsRestrict B S hS a _ _
    (compl_subset_preimage_compl B S hS a q qW ha T) ≫
      (Space.openSubspaceOfPoints B S hS Y (Space.pointsMap B S hS Y q ⁻¹' T)ᶜ).ι)
  exact Space.isEtale_comp B S hS h (Space.isEtale_ι_of_isOpenSubspace
    (Space.isOpenSubspace_openSubspaceOfPoints B S hS hY _
      (hT.preimage (Space.continuous_pointsMap B S hS q)).isOpen_compl))

/-! ### Functoriality of the restriction morphisms of completions -/

/-- Functoriality of the restriction morphisms of completions, in the form which transports an
identity between composites of morphisms of presheaves to an identity between the induced
morphisms of completions. -/
theorem completionSheafRestrict_comp_eq {F₃ F₂ F₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F₃ ⟶ F₂) (b : F₂ ⟶ F₁) (c : F₃ ⟶ F₁) (habc : a ≫ b = c)
    (T₃ : Set (Space.points B S hS F₃)) (T₂ : Set (Space.points B S hS F₂))
    (T₁ : Set (Space.points B S hS F₁))
    (h₁ : T₃ ⊆ Space.pointsMap B S hS F₃ a ⁻¹' T₂)
    (h₂ : T₂ ⊆ Space.pointsMap B S hS F₂ b ⁻¹' T₁)
    (h₃ : T₃ ⊆ Space.pointsMap B S hS F₃ c ⁻¹' T₁) :
    Space.completionSheafRestrict B S hS a T₃ T₂ h₁ ≫
        Space.completionSheafRestrict B S hS b T₂ T₁ h₂ =
      Space.completionSheafRestrict B S hS c T₃ T₁ h₃ := by
  have hab : T₃ ⊆ Space.pointsMap B S hS F₃ (a ≫ b) ⁻¹' T₁ := by rwa [habc]
  rw [← Space.completionSheafRestrict_comp B S hS a b T₃ T₂ T₁ h₁ h₂ hab]
  exact Space.completionSheafRestrict_congr B S hS habc T₃ T₁ hab h₃

/-- The restriction morphism of completions along a source set presented as the inverse image
of the target set is the morphism of completions of Stacks 0AMC, read through the transport
along that presentation. -/
theorem completionSheafRestrict_eq_eqToHom_comp {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F' ⟶ F) (T' : Set (Space.points B S hS F')) (T : Set (Space.points B S hS F))
    (hT' : T' = Space.pointsMap B S hS F' f ⁻¹' T)
    (h : T' ⊆ Space.pointsMap B S hS F' f ⁻¹' T) :
    Space.completionSheafRestrict B S hS f T' T h =
      eqToHom (congrArg (Space.completionSheaf B S hS F') hT') ≫
        Space.completionSheafMap B S hS f T := by
  subst hT'
  simp [Space.completionSheafRestrict_self]

/-- Completion commutes with fibre products, for the restriction morphisms of completions along
index sets presented as inverse images. -/
theorem isPullback_completionSheafRestrict_of_isPullback
    {P X' X₁ Xb : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : P ⟶ X'} {q : P ⟶ X₁} {fa : X' ⟶ Xb} {ga : X₁ ⟶ Xb} (hp : IsPullback p q fa ga)
    (T : Set (Space.points B S hS Xb)) (TP : Set (Space.points B S hS P))
    (TX' : Set (Space.points B S hS X')) (TX₁ : Set (Space.points B S hS X₁))
    (hTX' : TX' = Space.pointsMap B S hS X' fa ⁻¹' T)
    (hTX₁ : TX₁ = Space.pointsMap B S hS X₁ ga ⁻¹' T)
    (hTPp : TP = Space.pointsMap B S hS P p ⁻¹' TX')
    (hTPq : TP = Space.pointsMap B S hS P q ⁻¹' TX₁)
    (hp' : TP ⊆ Space.pointsMap B S hS P p ⁻¹' TX')
    (hq' : TP ⊆ Space.pointsMap B S hS P q ⁻¹' TX₁)
    (hf' : TX' ⊆ Space.pointsMap B S hS X' fa ⁻¹' T)
    (hg' : TX₁ ⊆ Space.pointsMap B S hS X₁ ga ⁻¹' T) :
    IsPullback (Space.completionSheafRestrict B S hS p TP TX' hp')
      (Space.completionSheafRestrict B S hS q TP TX₁ hq')
      (Space.completionSheafRestrict B S hS fa TX' T hf')
      (Space.completionSheafRestrict B S hS ga TX₁ T hg') := by
  subst hTX' hTX₁ hTPp
  rw [Space.completionSheafRestrict_self, Space.completionSheafRestrict_self,
    Space.completionSheafRestrict_self,
    completionSheafRestrict_eq_eqToHom_comp B S hS q _ _ hTPq hq']
  exact Space.isPullback_completionSheafMap_of_isPullback B S hS hp T

/-! ### The equivalence-relation half of Stacks 0AR8 -/

/-- Let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be closed and let `s, t : R ⟶ U` be morphisms of algebraic spaces
over `X` with `R` and `U` locally of finite type over `X`. If the base change of `s` and `t` to
`X ∖ T` is an equivalence relation and the formal completion `(t_{/T}, s_{/T})` is an
equivalence relation, then `(t, s) : R ⟶ U ×_X U` is a monomorphism and an equivalence
relation.

The base change to `X ∖ T` is read as the restriction of `s` and `t` to the subspaces cut out
by the complements of the inverse images of `T`, which is that base change by
`AlgebraicGeometry.FormalSpace.isPullback_ι_openSubspaceOfPoints_compl`; the formal completion
is read as the restriction morphisms of completions of Stacks 0AMC along those inverse images. -/
theorem isEquivalenceRelation_of_openComplement_and_completionSheaf
    (hX : IsAlgebraicSpace B S hS X) (hR : IsAlgebraicSpace B S hS R)
    (hU : IsAlgebraicSpace B S hS U)
    (qR : R ⟶ X) (qU : U ⟶ X) (s t : R ⟶ U)
    (hs : s ≫ qU = qR) (ht : t ≫ qU = qR)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hqR : Space.IsLocallyOfFiniteType B S hS qR)
    (hqU : Space.IsLocallyOfFiniteType B S hS qU)
    (hopen : IsEquivalenceRelation
      (Space.openSubspaceOfPointsRestrict B S hS t _ _
        (compl_subset_preimage_compl B S hS t qU qR ht T))
      (Space.openSubspaceOfPointsRestrict B S hS s _ _
        (compl_subset_preimage_compl B S hS s qU qR hs T)))
    (hcompletion : IsEquivalenceRelation
      (Space.completionSheafRestrict B S hS t _ _
        (preimage_subset_preimage_of_comp B S hS t qU qR ht T))
      (Space.completionSheafRestrict B S hS s _ _
        (preimage_subset_preimage_of_comp B S hS s qU qR hs T))) :
    Mono (relationMap B S hS qU s t (ht.trans hs.symm)) ∧ IsEquivalenceRelation t s := by
  have hcomm : t ≫ qU = s ≫ qU := ht.trans hs.symm
  have hY : IsAlgebraicSpace B S hS (pullback qU qU) :=
    isAlgebraicSpace_pullback B S hS qU qU hU hU hX
  obtain ⟨eo⟩ := hopen.nonempty_equivalenceRelation
  obtain ⟨ec⟩ := hcompletion.nonempty_equivalenceRelation
  have htι : Space.openSubspaceOfPointsRestrict B S hS t _ _
        (compl_subset_preimage_compl B S hS t qU qR ht T) ≫
      (Space.openSubspaceOfPoints B S hS U (Space.pointsMap B S hS U qU ⁻¹' T)ᶜ).ι =
    (Space.openSubspaceOfPoints B S hS R (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ t := rfl
  have hsι : Space.openSubspaceOfPointsRestrict B S hS s _ _
        (compl_subset_preimage_compl B S hS s qU qR hs T) ≫
      (Space.openSubspaceOfPoints B S hS U (Space.pointsMap B S hS U qU ⁻¹' T)ᶜ).ι =
    (Space.openSubspaceOfPoints B S hS R (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ s := rfl
  have hrt : eo.r ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ t =
      (Space.openSubspaceOfPoints B S hS U (Space.pointsMap B S hS U qU ⁻¹' T)ᶜ).ι := by
    rw [← htι, ← Category.assoc, eo.reflexivity₁, Category.id_comp]
  have hrs : eo.r ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ s =
      (Space.openSubspaceOfPoints B S hS U (Space.pointsMap B S hS U qU ⁻¹' T)ᶜ).ι := by
    rw [← hsι, ← Category.assoc, eo.reflexivity₂, Category.id_comp]
  have hit : eo.s ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ t =
      (Space.openSubspaceOfPoints B S hS R (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ s := by
    rw [← htι, ← Category.assoc, eo.symmetry₁, hsι]
  have his : eo.s ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ s =
      (Space.openSubspaceOfPoints B S hS R (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ t := by
    rw [← hsι, ← Category.assoc, eo.symmetry₂, htι]
  have hct : eo.t ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ t =
      PullbackCone.fst eo.c ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ t := by
    rw [← htι, ← Category.assoc, eo.transitivity₁, Category.assoc]
  have hcts : eo.t ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ s =
      PullbackCone.snd eo.c ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι ≫ s := by
    rw [← hsι, ← Category.assoc, eo.transitivity₂, Category.assoc]
  have hjt : relationMap B S hS qU s t hcomm ≫ pullback.fst qU qU = t :=
    relationMap_fst B S hS qU s t hcomm
  have hjs : relationMap B S hS qU s t hcomm ≫ pullback.snd qU qU = s :=
    relationMap_snd B S hS qU s t hcomm
  have hjft : Space.IsLocallyOfFiniteType B S hS (relationMap B S hS qU s t hcomm) :=
    isLocallyOfFiniteType_relationMap B S hS qR qU s t hcomm ht hR hU hX hqR
  have hjqY : relationMap B S hS qU s t hcomm ≫ (pullback.fst qU qU ≫ qU) = qR := by
    rw [← Category.assoc, hjt, ht]
  set j := relationMap B S hS qU s t hcomm with hjdef
  have hTRclosed : IsClosed (Space.pointsMap B S hS R qR ⁻¹' T) :=
    hT.preimage (Space.continuous_pointsMap B S hS qR)
  have hTUclosed : IsClosed (Space.pointsMap B S hS U qU ⁻¹' T) :=
    hT.preimage (Space.continuous_pointsMap B S hS qU)
  have hRnoeth := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hR hX qR hqR hXnoeth
  have hUnoeth := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hU hX qU hqU hXnoeth
  have htft : Space.IsLocallyOfFiniteType B S hS t :=
    isLocallyOfFiniteType_of_comp_structure B S hS qR qU t ht hR hU hX hqR
  have hjTY : Space.pointsMap B S hS R qR ⁻¹' T =
      Space.pointsMap B S hS R j ⁻¹'
        (Space.pointsMap B S hS (pullback qU qU) (pullback.fst qU qU ≫ qU) ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS j (pullback.fst qU qU ≫ qU) qR hjqY T).symm
  have hfstU : Space.pointsMap B S hS (pullback qU qU) (pullback.fst qU qU ≫ qU) ⁻¹' T =
      Space.pointsMap B S hS (pullback qU qU) (pullback.fst qU qU) ⁻¹'
        (Space.pointsMap B S hS U qU ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS (pullback.fst qU qU) qU _ rfl T).symm
  have hsndU : Space.pointsMap B S hS (pullback qU qU) (pullback.fst qU qU ≫ qU) ⁻¹' T =
      Space.pointsMap B S hS (pullback qU qU) (pullback.snd qU qU) ⁻¹'
        (Space.pointsMap B S hS U qU ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS (pullback.snd qU qU) qU _
      pullback.condition.symm T).symm
  have hsqU := isPullback_completionSheafRestrict_of_isPullback B S hS
    (IsPullback.of_hasPullback qU qU) T
    (Space.pointsMap B S hS (pullback qU qU) (pullback.fst qU qU ≫ qU) ⁻¹' T)
    (Space.pointsMap B S hS U qU ⁻¹' T) (Space.pointsMap B S hS U qU ⁻¹' T) rfl rfl
    hfstU hsndU hfstU.subset hsndU.subset Set.Subset.rfl Set.Subset.rfl
  have hjfstc : Space.completionSheafRestrict B S hS j _ _ hjTY.subset ≫
      Space.completionSheafRestrict B S hS (pullback.fst qU qU) _ _ hfstU.subset =
    Space.completionSheafRestrict B S hS t _ _
      (preimage_subset_preimage_of_comp B S hS t qU qR ht T) :=
    completionSheafRestrict_comp_eq B S hS _ _ t hjt _ _ _ _ _ _
  have hjsndc : Space.completionSheafRestrict B S hS j _ _ hjTY.subset ≫
      Space.completionSheafRestrict B S hS (pullback.snd qU qU) _ _ hsndU.subset =
    Space.completionSheafRestrict B S hS s _ _
      (preimage_subset_preimage_of_comp B S hS s qU qR hs T) :=
    completionSheafRestrict_comp_eq B S hS _ _ s hjs _ _ _ _ _ _
  have hjointc : ∀ {W : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
      (a b : W ⟶ Space.completionSheaf B S hS (pullback qU qU)
        (Space.pointsMap B S hS (pullback qU qU) (pullback.fst qU qU ≫ qU) ⁻¹' T)),
      a ≫ Space.completionSheafRestrict B S hS (pullback.fst qU qU) _ _ hfstU.subset =
        b ≫ Space.completionSheafRestrict B S hS (pullback.fst qU qU) _ _ hfstU.subset →
      a ≫ Space.completionSheafRestrict B S hS (pullback.snd qU qU) _ _ hsndU.subset =
        b ≫ Space.completionSheafRestrict B S hS (pullback.snd qU qU) _ _ hsndU.subset →
      a = b := fun a b h₁ h₂ ↦ hsqU.hom_ext h₁ h₂
  have hfstt : pullback.fst j j ≫ t = pullback.snd j j ≫ t := by
    rw [← hjt, ← Category.assoc, ← Category.assoc, pullback.condition]
  have hfsts : pullback.fst j j ≫ s = pullback.snd j j ≫ s := by
    rw [← hjs, ← Category.assoc, ← Category.assoc, pullback.condition]
  have hAcond : pullback.snd j j ≫ qR = pullback.fst j j ≫ qR := by
    rw [← ht, ← Category.assoc, ← hfstt, Category.assoc]
  have hTAp : Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T =
      Space.pointsMap B S hS (pullback j j) (pullback.fst j j) ⁻¹'
        (Space.pointsMap B S hS R qR ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS (pullback.fst j j) qR _ rfl T).symm
  have hTAq : Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T =
      Space.pointsMap B S hS (pullback j j) (pullback.snd j j) ⁻¹'
        (Space.pointsMap B S hS R qR ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS (pullback.snd j j) qR _ hAcond T).symm
  have hmono : Mono j := by
    have hTAclosed : IsClosed (Space.pointsMap B S hS (pullback j j)
        (pullback.fst j j ≫ qR) ⁻¹' T) :=
      hT.preimage (Space.continuous_pointsMap B S hS _)
    have hTZ : Space.pointsMap B S hS R qR ⁻¹' T ⊆
        Space.pointsMap B S hS R (pullback.diagonal j) ⁻¹'
          (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T) :=
      preimage_subset_preimage_of_comp B S hS (pullback.diagonal j)
        (pullback.fst j j ≫ qR) qR
        (by rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]) T
    have hopenA : ∃ v : (Space.openSubspaceOfPoints B S hS (pullback j j)
        (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T)ᶜ).toFunctor ⟶ R,
        v ≫ pullback.diagonal j = (Space.openSubspaceOfPoints B S hS (pullback j j)
          (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T)ᶜ).ι ≫
            𝟙 (pullback j j) := by
      obtain ⟨a, ha⟩ := exists_factorization_openComplement B S hS
        (pullback.fst j j ≫ qR) qR T
        ((Space.openSubspaceOfPoints B S hS (pullback j j)
          (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T)ᶜ).ι ≫
            pullback.fst j j) (Category.assoc _ _ _)
      obtain ⟨b, hb⟩ := exists_factorization_openComplement B S hS
        (pullback.fst j j ≫ qR) qR T
        ((Space.openSubspaceOfPoints B S hS (pullback j j)
          (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T)ᶜ).ι ≫
            pullback.snd j j) (by rw [Category.assoc, hAcond])
      have hab : a = b := by
        refine eo.right_cancellation a b ?_ ?_
        · apply (cancel_mono (Space.openSubspaceOfPoints B S hS U
            (Space.pointsMap B S hS U qU ⁻¹' T)ᶜ).ι).mp
          rw [Category.assoc, Category.assoc, htι, ← Category.assoc, ← Category.assoc, ha, hb,
            Category.assoc, Category.assoc, hfstt]
        · apply (cancel_mono (Space.openSubspaceOfPoints B S hS U
            (Space.pointsMap B S hS U qU ⁻¹' T)ᶜ).ι).mp
          rw [Category.assoc, Category.assoc, hsι, ← Category.assoc, ← Category.assoc, ha, hb,
            Category.assoc, Category.assoc, hfsts]
      obtain ⟨v, hv⟩ := exists_factorization_diagonal j _
        (by rw [← ha, ← hb, hab] :
          (Space.openSubspaceOfPoints B S hS (pullback j j)
              (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T)ᶜ).ι ≫
            pullback.fst j j =
          (Space.openSubspaceOfPoints B S hS (pullback j j)
              (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T)ᶜ).ι ≫
            pullback.snd j j)
      exact ⟨v, by rw [hv, Category.comp_id]⟩
    have hcomplA : ∃ w : Space.completionSheaf B S hS (pullback j j)
        (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T) ⟶
        Space.completionSheaf B S hS R (Space.pointsMap B S hS R qR ⁻¹' T),
        w ≫ Space.completionSheafRestrict B S hS (pullback.diagonal j) _ _ hTZ =
          Space.completionSheafRestrict B S hS (𝟙 (pullback j j)) _ _ (by simp) := by
      have hsqA := isPullback_completionSheafRestrict_of_isPullback B S hS
        (IsPullback.of_hasPullback j j)
        (Space.pointsMap B S hS (pullback qU qU) (pullback.fst qU qU ≫ qU) ⁻¹' T)
        (Space.pointsMap B S hS (pullback j j) (pullback.fst j j ≫ qR) ⁻¹' T)
        (Space.pointsMap B S hS R qR ⁻¹' T) (Space.pointsMap B S hS R qR ⁻¹' T)
        hjTY hjTY hTAp hTAq hTAp.subset hTAq.subset hjTY.subset hjTY.subset
      have hdp : Space.completionSheafRestrict B S hS (pullback.diagonal j) _ _ hTZ ≫
          Space.completionSheafRestrict B S hS (pullback.fst j j) _ _ hTAp.subset = 𝟙 _ := by
        rw [completionSheafRestrict_comp_eq B S hS _ _ (𝟙 R) (pullback.diagonal_fst j) _ _ _
          hTZ hTAp.subset (by simp)]
        exact Space.completionSheafRestrict_id B S hS _ (by simp)
      have hdq : Space.completionSheafRestrict B S hS (pullback.diagonal j) _ _ hTZ ≫
          Space.completionSheafRestrict B S hS (pullback.snd j j) _ _ hTAq.subset = 𝟙 _ := by
        rw [completionSheafRestrict_comp_eq B S hS _ _ (𝟙 R) (pullback.diagonal_snd j) _ _ _
          hTZ hTAq.subset (by simp)]
        exact Space.completionSheafRestrict_id B S hS _ (by simp)
      have hpq : Space.completionSheafRestrict B S hS (pullback.fst j j) _ _ hTAp.subset =
          Space.completionSheafRestrict B S hS (pullback.snd j j) _ _ hTAq.subset := by
        refine ec.right_cancellation _ _ ?_ ?_
        · rw [completionSheafRestrict_comp_eq B S hS _ _ (pullback.fst j j ≫ t) rfl _ _ _
              hTAp.subset (preimage_subset_preimage_of_comp B S hS t qU qR ht T)
              (preimage_subset_preimage_of_comp B S hS (pullback.fst j j ≫ t) qU _
                (by rw [Category.assoc, ht]) T),
            completionSheafRestrict_comp_eq B S hS _ _ (pullback.snd j j ≫ t) rfl _ _ _
              hTAq.subset (preimage_subset_preimage_of_comp B S hS t qU qR ht T)
              (preimage_subset_preimage_of_comp B S hS (pullback.snd j j ≫ t) qU _
                (by rw [Category.assoc, ht, hAcond]) T)]
          exact Space.completionSheafRestrict_congr B S hS hfstt _ _ _ _
        · rw [completionSheafRestrict_comp_eq B S hS _ _ (pullback.fst j j ≫ s) rfl _ _ _
              hTAp.subset (preimage_subset_preimage_of_comp B S hS s qU qR hs T)
              (preimage_subset_preimage_of_comp B S hS (pullback.fst j j ≫ s) qU _
                (by rw [Category.assoc, hs]) T),
            completionSheafRestrict_comp_eq B S hS _ _ (pullback.snd j j ≫ s) rfl _ _ _
              hTAq.subset (preimage_subset_preimage_of_comp B S hS s qU qR hs T)
              (preimage_subset_preimage_of_comp B S hS (pullback.snd j j ≫ s) qU _
                (by rw [Category.assoc, hs, hAcond]) T)]
          exact Space.completionSheafRestrict_congr B S hS hfsts _ _ _ _
      obtain ⟨w, hw⟩ := exists_factorization_of_isPullback_diagonal hsqA
        (Space.completionSheafRestrict B S hS (pullback.diagonal j) _ _ hTZ) hdp hdq (𝟙 _)
        (by rw [Category.id_comp, Category.id_comp, hpq])
      exact ⟨w, by rw [hw, Space.completionSheafRestrict_id]⟩
    obtain ⟨v, hv⟩ := exists_factorization_of_openComplement_and_completionSheaf B S hS
      (isAlgebraicSpace_diagonalObj B S hS hR hY j) (isAlgebraicSpace_diagonalObj B S hS hR hY j)
      hR (𝟙 (pullback j j)) (pullback.diagonal j) _ _ _ (by simp) hTZ hTAclosed
      (isLocallyNoetherian_pullback_self B S hS qR j j hR hY hX hjft hqR hXnoeth) inferInstance
      (Space.presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS _
        (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS j hR))
      hopenA hcomplA
    exact mono_of_section_diagonal j v hv
  have hrefl : ∃ v : U ⟶ R, v ≫ j = pullback.diagonal qU := by
    refine exists_factorization_of_openComplement_and_completionSheaf B S hS hU hY hR
      (pullback.diagonal qU) j _ _ _
      (preimage_subset_preimage_of_comp B S hS (pullback.diagonal qU)
        (pullback.fst qU qU ≫ qU) qU
        (by rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]) T)
      hjTY.subset hTUclosed hUnoeth hmono hjft ?_ ?_
    · refine ⟨eo.r ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι, pullback.hom_ext ?_ ?_⟩
      · simp only [Category.assoc, hjt, hrt, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, hjs, hrs, pullback.diagonal_snd, Category.comp_id]
    · refine ⟨ec.r, hjointc _ _ ?_ ?_⟩
      · rw [Category.assoc, hjfstc, ec.reflexivity₁,
          completionSheafRestrict_comp_eq B S hS _ _ (𝟙 U) (pullback.diagonal_fst qU) _ _ _ _ _
            (by simp), Space.completionSheafRestrict_id]
      · rw [Category.assoc, hjsndc, ec.reflexivity₂,
          completionSheafRestrict_comp_eq B S hS _ _ (𝟙 U) (pullback.diagonal_snd qU) _ _ _ _ _
            (by simp), Space.completionSheafRestrict_id]
  have hsymm : ∃ v : R ⟶ R, v ≫ j = relationMap B S hS qU t s hcomm.symm := by
    refine exists_factorization_of_openComplement_and_completionSheaf B S hS hR hY hR
      (relationMap B S hS qU t s hcomm.symm) j _ _ _
      (preimage_subset_preimage_of_comp B S hS (relationMap B S hS qU t s hcomm.symm)
        (pullback.fst qU qU ≫ qU) qR
        (by rw [← Category.assoc, relationMap_fst, hs]) T)
      hjTY.subset hTRclosed hRnoeth hmono hjft ?_ ?_
    · refine ⟨eo.s ≫ (Space.openSubspaceOfPoints B S hS R
        (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι, pullback.hom_ext ?_ ?_⟩
      · simp only [Category.assoc, hjt, hit, relationMap_fst]
      · simp only [Category.assoc, hjs, his, relationMap_snd]
    · refine ⟨ec.s, hjointc _ _ ?_ ?_⟩
      · rw [Category.assoc, hjfstc, ec.symmetry₁,
          completionSheafRestrict_comp_eq B S hS _ _ s (relationMap_fst B S hS qU t s hcomm.symm)
            _ _ _ _ _ (preimage_subset_preimage_of_comp B S hS s qU qR hs T)]
      · rw [Category.assoc, hjsndc, ec.symmetry₂,
          completionSheafRestrict_comp_eq B S hS _ _ t (relationMap_snd B S hS qU t s hcomm.symm)
            _ _ _ _ _ (preimage_subset_preimage_of_comp B S hS t qU qR ht T)]
  have hcf : compositionMap B S hS qU s t hcomm ≫ pullback.fst qU qU = pullback.fst s t ≫ t :=
    pullback.lift_fst _ _ _
  have hcs : compositionMap B S hS qU s t hcomm ≫ pullback.snd qU qU = pullback.snd s t ≫ s :=
    pullback.lift_snd _ _ _
  have hDcond : pullback.snd s t ≫ qR = pullback.fst s t ≫ qR := by
    rw [← ht, ← Category.assoc, ← pullback.condition, Category.assoc, hs, ht]
  have hTDp : Space.pointsMap B S hS (pullback s t) (pullback.fst s t ≫ qR) ⁻¹' T =
      Space.pointsMap B S hS (pullback s t) (pullback.fst s t) ⁻¹'
        (Space.pointsMap B S hS R qR ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS (pullback.fst s t) qR _ rfl T).symm
  have hTDq : Space.pointsMap B S hS (pullback s t) (pullback.fst s t ≫ qR) ⁻¹' T =
      Space.pointsMap B S hS (pullback s t) (pullback.snd s t) ⁻¹'
        (Space.pointsMap B S hS R qR ⁻¹' T) :=
    (preimage_pointsMap_preimage_of_comp B S hS (pullback.snd s t) qR _ hDcond T).symm
  have htrans : ∃ v : pullback s t ⟶ R, v ≫ j = compositionMap B S hS qU s t hcomm := by
    refine exists_factorization_of_openComplement_and_completionSheaf B S hS
      (isAlgebraicSpace_pullback B S hS s t hR hR hU) hY hR
      (compositionMap B S hS qU s t hcomm) j _ _ _
      (preimage_subset_preimage_of_comp B S hS (compositionMap B S hS qU s t hcomm)
        (pullback.fst qU qU ≫ qU) (pullback.fst s t ≫ qR)
        (by rw [← Category.assoc, hcf, Category.assoc, ht]) T)
      hjTY.subset (hT.preimage (Space.continuous_pointsMap B S hS _))
      (isLocallyNoetherian_pullback_self B S hS qR s t hR hU hX htft hqR hXnoeth) hmono hjft ?_ ?_
    · obtain ⟨a, ha⟩ := exists_factorization_openComplement B S hS
        (pullback.fst s t ≫ qR) qR T
        ((Space.openSubspaceOfPoints B S hS (pullback s t)
          (Space.pointsMap B S hS (pullback s t) (pullback.fst s t ≫ qR) ⁻¹' T)ᶜ).ι ≫
            pullback.fst s t) (Category.assoc _ _ _)
      obtain ⟨b, hb⟩ := exists_factorization_openComplement B S hS
        (pullback.fst s t ≫ qR) qR T
        ((Space.openSubspaceOfPoints B S hS (pullback s t)
          (Space.pointsMap B S hS (pullback s t) (pullback.fst s t ≫ qR) ⁻¹' T)ᶜ).ι ≫
            pullback.snd s t) (by rw [Category.assoc, hDcond])
      have hcond : a ≫ Space.openSubspaceOfPointsRestrict B S hS s _ _
            (compl_subset_preimage_compl B S hS s qU qR hs T) =
          b ≫ Space.openSubspaceOfPointsRestrict B S hS t _ _
            (compl_subset_preimage_compl B S hS t qU qR ht T) := by
        apply (cancel_mono (Space.openSubspaceOfPoints B S hS U
          (Space.pointsMap B S hS U qU ⁻¹' T)ᶜ).ι).mp
        rw [Category.assoc, Category.assoc, hsι, htι, ← Category.assoc, ← Category.assoc, ha, hb,
          Category.assoc, Category.assoc, pullback.condition]
      refine ⟨PullbackCone.IsLimit.lift eo.isLimit a b hcond ≫ eo.t ≫
        (Space.openSubspaceOfPoints B S hS R
          (Space.pointsMap B S hS R qR ⁻¹' T)ᶜ).ι, pullback.hom_ext ?_ ?_⟩
      · simp only [Category.assoc, hjt, hct, PullbackCone.IsLimit.lift_fst_assoc,
          reassoc_of% ha, hcf]
      · simp only [Category.assoc, hjs, hcts, PullbackCone.IsLimit.lift_snd_assoc,
          reassoc_of% hb, hcs]
    · have hcondc : Space.completionSheafRestrict B S hS (pullback.fst s t) _ _ hTDp.subset ≫
            Space.completionSheafRestrict B S hS s _ _
              (preimage_subset_preimage_of_comp B S hS s qU qR hs T) =
          Space.completionSheafRestrict B S hS (pullback.snd s t) _ _ hTDq.subset ≫
            Space.completionSheafRestrict B S hS t _ _
              (preimage_subset_preimage_of_comp B S hS t qU qR ht T) := by
        rw [completionSheafRestrict_comp_eq B S hS _ _ (pullback.fst s t ≫ s) rfl _ _ _
            hTDp.subset _ (preimage_subset_preimage_of_comp B S hS (pullback.fst s t ≫ s) qU _
              (by rw [Category.assoc, hs]) T),
          completionSheafRestrict_comp_eq B S hS _ _ (pullback.snd s t ≫ t) rfl _ _ _
            hTDq.subset _ (preimage_subset_preimage_of_comp B S hS (pullback.snd s t ≫ t) qU _
              (by rw [Category.assoc, ht, hDcond]) T)]
        exact Space.completionSheafRestrict_congr B S hS pullback.condition _ _ _ _
      refine ⟨PullbackCone.IsLimit.lift ec.isLimit _ _ hcondc ≫ ec.t, hjointc _ _ ?_ ?_⟩
      · rw [Category.assoc, Category.assoc, hjfstc, ec.transitivity₁, ← Category.assoc,
          PullbackCone.IsLimit.lift_fst,
          completionSheafRestrict_comp_eq B S hS _ _ (pullback.fst s t ≫ t) rfl _ _ _
            hTDp.subset _ (preimage_subset_preimage_of_comp B S hS (pullback.fst s t ≫ t) qU _
              (by rw [Category.assoc, ht]) T),
          completionSheafRestrict_comp_eq B S hS _ _ (pullback.fst s t ≫ t) hcf _ _ _ _ _
            (preimage_subset_preimage_of_comp B S hS (pullback.fst s t ≫ t) qU _
              (by rw [Category.assoc, ht]) T)]
      · rw [Category.assoc, Category.assoc, hjsndc, ec.transitivity₂, ← Category.assoc,
          PullbackCone.IsLimit.lift_snd,
          completionSheafRestrict_comp_eq B S hS _ _ (pullback.snd s t ≫ s) rfl _ _ _
            hTDq.subset _ (preimage_subset_preimage_of_comp B S hS (pullback.snd s t ≫ s) qU _
              (by rw [Category.assoc, hs, hDcond]) T),
          completionSheafRestrict_comp_eq B S hS _ _ (pullback.snd s t ≫ s) hcs _ _ _ _ _
            (preimage_subset_preimage_of_comp B S hS (pullback.snd s t ≫ s) qU _
              (by rw [Category.assoc, hs, hDcond]) T)]
  exact ⟨hmono, isEquivalenceRelation_of_exists_factorizations B S hS qU s t hcomm hmono
    hrefl hsymm htrans⟩

/-! ### Stacks 0AR8 -/

/-- Let `S` be a scheme, let `X` be a locally Noetherian algebraic space over
`S`, let `T ⊆ |X|` be a closed subset and let `s, t : R ⟶ U` be two morphisms of algebraic
spaces over `X`. Assume

1. `R` and `U` are locally of finite type over `X`,
2. the base change of `s` and `t` to `X ∖ T` is an étale equivalence relation, and
3. the formal completion `(t_{/T}, s_{/T}) : R_{/T} ⟶ U_{/T} ×_{X_{/T}} U_{/T}` is an étale
   equivalence relation.

Then `(t, s) : R ⟶ U ×_X U` is an étale equivalence relation: it is a monomorphism, `t` and `s`
form an equivalence relation, and both are étale. -/
@[stacks 0AR8 "WHAT IS FORMALIZED: hypothesis (3) is read as saying that the formal completion \
`(t_{/T}, s_{/T})` is an *étale* equivalence relation — an equivalence relation whose two \
maps `s_{/T}` and `t_{/T}` are étale — and not merely an equivalence relation. THE LITERAL \
READING OF (3) IS FALSE: take `X = Spec k` and `T = |X|`, so that `X ∖ T` is empty and (2) is \
vacuous, and `U = 𝔸¹`, `R = U ×_X U`, `t = pr₀`, `s = pr₁`; then `X_{/T} = X`, `U_{/T} = U`, \
`R_{/T} = R`, so (3) says that the identity is an equivalence relation, (1) and (2) hold, and \
yet `s = pr₁ : 𝔸¹ × 𝔸¹ ⟶ 𝔸¹` is not étale, so the conclusion fails. THE ÉTALE READING IS THE \
ONE THE SOURCE'S OWN PROOF USES: \"Since the formal completions of the maps `s`, `t` are \
étale, we see that `s` and `t` are étale for example by More on Morphisms, Lemma 37.12.3\". \
Otherwise the statement is the tag's: hypothesis (2) is read as the restrictions of `s` and \
`t` to the subspaces cut out by the complements of the inverse images of `T`, which is the \
base change to `X ∖ T` by \
`AlgebraicGeometry.FormalSpace.isPullback_ι_openSubspaceOfPoints_compl`, and (3) as the \
restriction morphisms of the completions of Tag 0AMC along those inverse images. No further \
hypothesis is added and no part of the conclusion is dropped: the conclusion carries \
monomorphy of `(t, s)`, the equivalence-relation structure, and étaleness of both `s` and `t`"]
theorem isEtaleEquivalenceRelation_of_openComplement_and_completion
    (hX : IsAlgebraicSpace B S hS X) (hR : IsAlgebraicSpace B S hS R)
    (hU : IsAlgebraicSpace B S hS U)
    (qR : R ⟶ X) (qU : U ⟶ X) (s t : R ⟶ U)
    (hs : s ≫ qU = qR) (ht : t ≫ qU = qR)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (hqR : Space.IsLocallyOfFiniteType B S hS qR)
    (hqU : Space.IsLocallyOfFiniteType B S hS qU)
    (hopen : IsEquivalenceRelation
      (Space.openSubspaceOfPointsRestrict B S hS t _ _
        (compl_subset_preimage_compl B S hS t qU qR ht T))
      (Space.openSubspaceOfPointsRestrict B S hS s _ _
        (compl_subset_preimage_compl B S hS s qU qR hs T)))
    (hopent : Space.IsEtale B S hS (Space.openSubspaceOfPointsRestrict B S hS t _ _
      (compl_subset_preimage_compl B S hS t qU qR ht T)))
    (hopens : Space.IsEtale B S hS (Space.openSubspaceOfPointsRestrict B S hS s _ _
      (compl_subset_preimage_compl B S hS s qU qR hs T)))
    (hcompletion : IsEquivalenceRelation
      (Space.completionSheafRestrict B S hS t _ _
        (preimage_subset_preimage_of_comp B S hS t qU qR ht T))
      (Space.completionSheafRestrict B S hS s _ _
        (preimage_subset_preimage_of_comp B S hS s qU qR hs T)))
    (hcomplt : ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS t (Space.pointsMap B S hS U qU ⁻¹' T)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
          Space.IsEtaleULift.{u + 1} B S hS g.hom)
        (Space.completionSheafMap B S hS t (Space.pointsMap B S hS U qU ⁻¹' T)).hom hrep)
    (hcompls : ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS s (Space.pointsMap B S hS U qU ⁻¹' T)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
          Space.IsEtaleULift.{u + 1} B S hS g.hom)
        (Space.completionSheafMap B S hS s (Space.pointsMap B S hS U qU ⁻¹' T)).hom hrep) :
    Mono (relationMap B S hS qU s t (ht.trans hs.symm)) ∧ IsEquivalenceRelation t s ∧
      Space.IsEtale B S hS s ∧ Space.IsEtale B S hS t := by
  obtain ⟨hmono, hrel⟩ := isEquivalenceRelation_of_openComplement_and_completionSheaf B S hS
    hX hR hU qR qU s t hs ht T hT hXnoeth hqR hqU hopen hcompletion
  have hTUclosed : IsClosed (Space.pointsMap B S hS U qU ⁻¹' T) :=
    hT.preimage (Space.continuous_pointsMap B S hS qU)
  have hUnoeth := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hU hX qU hqU hXnoeth
  refine ⟨hmono, hrel, ?_, ?_⟩
  · exact isEtale_of_isEtale_completionSheafMap_space B S hS hR hU s
      (Space.pointsMap B S hS U qU ⁻¹' T) hTUclosed hUnoeth
      (isLocallyOfFiniteType_of_comp_structure B S hS qR qU s hs hR hU hX hqR)
      (isEtale_openComplementRestriction_of_restrict B S hS s qU qR hs T hopens) hcompls
  · exact isEtale_of_isEtale_completionSheafMap_space B S hS hR hU t
      (Space.pointsMap B S hS U qU ⁻¹' T) hTUclosed hUnoeth
      (isLocallyOfFiniteType_of_comp_structure B S hS qR qU t ht hR hU hX hqR)
      (isEtale_openComplementRestriction_of_restrict B S hS t qU qR ht T hopent) hcomplt

end Relation

end AlgebraicGeometry.FormalSpace

end
