module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupStrictTransformSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupStrictTransformSpaceEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOverAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace

/-!
# Auxiliary results for making a proper morphism an isomorphism near a closure

Cancellation properties of the second projection of a fibre product being an isomorphism, the
separation of two disjoint closed subsets of a spectral space by disjoint constructible closed
subsets, and permanence facts for blowups and open subspaces of algebraic spaces.

## Main results

* `Topology.exists_isConstructible_isClosed_supersets_of_disjoint`: two disjoint closed subsets
  of a compact, quasi-separated, prespectral space lie in disjoint constructible closed subsets.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong`:
  a blowup of a quasi-compact and quasi-separated algebraic space in a centre of finite
  presentation is quasi-compact and quasi-separated.
* `CategoryTheory.Limits.IsPullback.of_cube`: a face of a cube of cartesian squares is cartesian.

## References

* [Stacks Project, Tag 0F47](https://stacks.math.columbia.edu/tag/0F47)
* [Stacks Project, Tag 0A4G](https://stacks.math.columbia.edu/tag/0A4G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Isomorphisms over a base change -/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasPullbacks C]

/-- The second projection of a fibre product is an isomorphism as soon as that of some pullback
square of the same cospan is. -/
theorem isIso_pullbackSnd_of_isPullback {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hs : IsIso snd) : IsIso (pullback.snd f g) := by
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- If the base change of `g` along `ι` is an isomorphism, so is its base change along any
`h ≫ ι`. -/
theorem isIso_pullbackSnd_comp_of_isIso {P Q O R : C} (g : P ⟶ Q) (ι : O ⟶ Q) (h : R ⟶ O)
    (hι : IsIso (pullback.snd g ι)) : IsIso (pullback.snd g (h ≫ ι)) := by
  have hp := IsPullback.of_hasPullback (pullback.snd g ι) h
  exact isIso_pullbackSnd_of_isPullback (hp.paste_horiz (IsPullback.of_hasPullback g ι))
    (hp.isIso_snd_of_isIso hι)

/-- Transport of the isomorphism property of a second projection along equalities of the two
morphisms of the cospan. -/
theorem isIso_pullbackSnd_of_eq {P Q O : C} {g g' : P ⟶ Q} {ι ι' : O ⟶ Q} (hg : g = g')
    (hι : ι = ι') (h : IsIso (pullback.snd g ι)) : IsIso (pullback.snd g' ι') :=
  hg ▸ hι ▸ h

/-- A form of `CategoryTheory.Limits.isIso_pullbackSnd_comp_of_isIso` for a morphism given to be
equal to a composite. -/
theorem isIso_pullbackSnd_of_eq_comp {P Q O R : C} (g : P ⟶ Q) (ι : O ⟶ Q) {ι' : R ⟶ Q}
    (h : R ⟶ O) (heq : ι' = h ≫ ι) (hι : IsIso (pullback.snd g ι)) :
    IsIso (pullback.snd g ι') := by
  subst heq
  exact isIso_pullbackSnd_comp_of_isIso g ι h hι

/-- Base change along `ι` of `g` is an isomorphism if base change along `e ≫ ι` is, for an
isomorphism `e`. -/
theorem isIso_pullbackSnd_of_isIso_comp {P Q O R : C} (g : P ⟶ Q) (ι : O ⟶ Q) (e : R ≅ O)
    (hι : IsIso (pullback.snd g (e.hom ≫ ι))) : IsIso (pullback.snd g ι) :=
  isIso_pullbackSnd_of_eq_comp g (e.hom ≫ ι) e.inv (by simp) hι

/-- Base change along `ι` of `e ≫ g` is an isomorphism if base change of `g` is, for an
isomorphism `e`. -/
theorem isIso_pullbackSnd_iso_comp {P P' Q O : C} (e : P' ≅ P) (g : P ⟶ Q) (ι : O ⟶ Q)
    (hι : IsIso (pullback.snd g ι)) : IsIso (pullback.snd (e.hom ≫ g) ι) := by
  refine isIso_pullbackSnd_of_isPullback (fst := pullback.fst g ι ≫ e.inv)
    (snd := pullback.snd g ι) ?_ hι
  refine IsPullback.of_iso (IsPullback.of_hasPullback g ι) (Iso.refl _) e.symm (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

/-- If `w` is the base change of `f` along `v`, the base change of `w` along `t` is an
isomorphism as soon as the base change of `f` along `t ≫ v` is. -/
theorem isIso_pullbackSnd_of_isPullback_of_isIso_comp {X₀ X Y₀ Y R : C} {u : X₀ ⟶ X}
    {w : X₀ ⟶ Y₀} {f : X ⟶ Y} {v : Y₀ ⟶ Y} (hsq : IsPullback u w f v) (t : R ⟶ Y₀)
    (h : IsIso (pullback.snd f (t ≫ v))) : IsIso (pullback.snd w t) := by
  have s := (IsPullback.of_hasPullback w t).paste_horiz hsq
  rw [← s.isoPullback_hom_snd]
  infer_instance

omit [HasPullbacks C] in
/-- A face of a cube of cartesian squares: in the cube
```
P₀ --can--> P
|  \         |  \
|   Y'₀ --m--|-> Y'
X₀ --u--> X   |
   \  |     \  |
    Y₀ --v--> Y
```
with `P₀ = X₀ ×_{Y₀} Y'₀`, `P = X ×_Y Y'`, `X₀ = X ×_Y Y₀` and `Y'₀ = Y₀ ×_Y Y'`, if the face
over `u` is cartesian then so is the face over `m`. -/
theorem IsPullback.of_cube {P₀ P X₀ X Y₀ Y Y'₀ Y' : C} {fst₀ : P₀ ⟶ X₀} {snd₀ : P₀ ⟶ Y'₀}
    {fst : P ⟶ X} {snd : P ⟶ Y'} {w : X₀ ⟶ Y₀} {c₀ : Y'₀ ⟶ Y₀} {f : X ⟶ Y} {c : Y' ⟶ Y}
    {u : X₀ ⟶ X} {v : Y₀ ⟶ Y} {m : Y'₀ ⟶ Y'} {can : P₀ ⟶ P}
    (hP₀ : fst₀ ≫ w = snd₀ ≫ c₀) (hP : fst ≫ f = snd ≫ c) (hC : IsPullback u w f v)
    (hB : IsPullback c₀ m v c) (hcan : IsPullback can fst₀ fst u) (hcs : can ≫ snd = snd₀ ≫ m) :
    IsPullback can snd₀ snd m := by
  have h := hcan.paste_vert hC
  rw [hP₀, hP] at h
  exact IsPullback.of_bot h hcs hB.flip

end CategoryTheory.Limits

/-! ### Separating two disjoint closed sets by constructible ones -/

namespace Topology

/-- Two disjoint closed subsets of a compact, quasi-separated, prespectral space are contained
in disjoint constructible closed subsets. -/
theorem exists_isConstructible_isClosed_supersets_of_disjoint {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X] {T T' : Set X}
    (hT : IsClosed T) (hT' : IsClosed T') (hd : Disjoint T T') :
    ∃ Tc T'c : Set X, IsClosed Tc ∧ IsClosed T'c ∧ IsConstructible Tc ∧ IsConstructible T'c ∧
      T ⊆ Tc ∧ T' ⊆ T'c ∧ Disjoint Tc T'c := by
  obtain ⟨W, hWc, hWo, hT'W, hWT⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    hT'.isCompact hT.isOpen_compl (Set.subset_compl_iff_disjoint_left.2 hd)
  obtain ⟨W', hW'c, hW'o, hW'W, hW'T'⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    hWo.isClosed_compl.isCompact hT'.isOpen_compl (Set.compl_subset_compl.2 hT'W)
  refine ⟨Wᶜ, W'ᶜ, hWo.isClosed_compl, hW'o.isClosed_compl,
    (hWc.isConstructible hWo).compl, (hW'c.isConstructible hW'o).compl,
    Set.subset_compl_comm.1 hWT, Set.subset_compl_comm.1 hW'T', ?_⟩
  exact Set.disjoint_compl_right_iff_subset.2 hW'W

end Topology

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Preliminaries -/

/-- The source of the blowup of a quasi-compact and quasi-separated algebraic space in a closed
subspace of finite presentation is quasi-compact and quasi-separated. -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong
    (hZ : B.Contains (⊤_ Scheme.{u})) {X X' : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {Zc : ClosedSubspaces B S hS X.1} (hfp : IsFinitePresentation B S hS Zc.1.ι) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Zc b) :
    IsQuasiCompactSpace B S hS X'.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ X'.1 := by
  have hP := isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Zc b hfp hb
  exact ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc hP.2.1.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X'.2 hXqs
      (isQuasiSeparated_of_isSeparated B S hS hP.1)⟩

/-- The base change of `g` along a smaller open subspace is an isomorphism if it is one along a
larger one. -/
theorem isIso_pullbackSnd_of_le {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : P ⟶ Q)
    {U U' : Subfunctor Q} (hUU' : U' ≤ U) (hU : IsIso (pullback.snd g U.ι)) :
    IsIso (pullback.snd g U'.ι) :=
  isIso_pullbackSnd_of_eq_comp g U.ι _ (Subfunctor.homOfLe_ι hUU').symm hU

/-- An open subspace whose points lie among those of another open subspace is contained in it
(Stacks 03BZ). -/
theorem le_of_subspacePointSet_subset {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {U U' : Subfunctor F} (hU : IsOpenSubspace B S hS U)
    (hU' : IsOpenSubspace B S hS U')
    (h : subspacePointSet B S hS F U ⊆ subspacePointSet B S hS F U') : U ≤ U' :=
  ((openSubspacesOrderIso B S hS F hF).le_iff_le (x := ⟨U, hU⟩) (y := ⟨U', hU'⟩)).1 h

/-- An algebraic space with an open immersion into another whose image is compact is
quasi-compact. -/
theorem isQuasiCompactSpace_of_isOpenImmersion_of_isCompact {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (i : F ⟶ G) (hi : IsOpenImmersion B S hS i)
    (hc : IsCompact (Set.range (pointsMap B S hS F i))) : IsQuasiCompactSpace B S hS F := by
  have : Mono i := mono_of_isOpenImmersion B S hS i hi
  have hemb : Topology.IsOpenEmbedding (pointsMap B S hS F i) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS _) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hi)
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hF).2 ⟨?_⟩
  refine hemb.isEmbedding.isCompact_iff.2 ?_
  rwa [Set.image_univ]

/-- The points of the range subfunctor of a monomorphism are the image of its map on points. -/
theorem subspacePointSet_range {A X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : A ⟶ X) [Mono f] :
    subspacePointSet B S hS X (Subfunctor.range f) = Set.range (pointsMap B S hS A f) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨z', rfl⟩ := pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange f) z
    exact ⟨z', by rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨pointsMap B S hS _ (Subfunctor.toRange f) z, ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]

/-- If two subfunctors are related by `A = B'.preimage can`, the square formed by their
inclusions and `can` is cartesian. -/
theorem exists_isPullback_of_eq_preimage {P₀ P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (can : P₀ ⟶ P) {A : Subfunctor P₀} {B' : Subfunctor P} (h : A = B'.preimage can) :
    ∃ φ : A.toFunctor ⟶ B'.toFunctor, IsPullback φ A.ι B'.ι can := by
  subst h
  exact ⟨_, Subfunctor.isPullback_preimage can B'⟩

end AlgebraicGeometry.Space
