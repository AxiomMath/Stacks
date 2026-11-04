module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Functor.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DensePreimageQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparatedEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Factoring a morphism through a surjective flat morphism given a dense open

Let `B` be an algebraic space over a scheme `S` contained in a big fppf site, and let
`f : X ⟶ Y` and `g : X ⟶ Z` be morphisms of algebraic spaces over `B` with `Y ⟶ B` separated
and `g` surjective, flat and locally of finite presentation. If there is a scheme-theoretically
dense open subspace `V ⊆ Z` over which `f` already descends — that is, the restriction of `f` to
`g⁻¹(V)` factors through `V` — then `f` factors through `g` over `B`. This is Stacks 0AEL.

Since `g` is surjective, flat and locally of finite presentation it is locally surjective for
the big fppf topology, so `Z` is the quotient of `X` by the kernel pair `R = X ×_Z X` as a
sheaf, and the factorization exists exactly when the two composites `R ⟶ X ⟶ Y` agree. The
projection `R ⟶ Z` is again flat and locally of finite presentation, so the inverse image of `V`
in `R` is scheme-theoretically dense; the two composites agree over that inverse image by
hypothesis, and Stacks 084N promotes agreement over a scheme-theoretically dense open to
agreement everywhere because `Y ⟶ B` is separated.

The engine behind the density of the inverse image of `V` in `R` is the scheme-level statement
that a flat morphism locally of finite presentation pulls scheme-theoretically dense opens back
to scheme-theoretically dense opens. The quasi-finite case is Stacks 0832; the finiteness
hypothesis is removed here by Stacks 05IE, which after an affine elementary étale localization of
source and target makes the regular functions upstairs a projective module over the regular
functions downstairs. A global function vanishing on the inverse image of the dense open is then
killed, coordinate by coordinate in a free module containing that projective module, by a power
of every function whose basic open lies in the dense open, hence is zero.

## Main results

* `AlgebraicGeometry.Space.exists_factorization_of_dense_open` is **Stacks 0AEL**.

## Implementation notes

The open subspace `V ⊆ Z` is a subfunctor of `Z`, and its inverse image in `X` is presented as
the fibre product of `g` with the inclusion `V ⟶ Z`, so hypothesis (3) of the source is the
existence of a morphism `v : V ⟶ Y` over `B` with `g⁻¹(V) ⟶ X ⟶ Y` equal to `g⁻¹(V) ⟶ V ⟶ Y`.
The conclusion records both the factorization and its compatibility with the structure
morphisms to `B`.

## References

* [Stacks Project, Tag 0AEL](https://stacks.math.columbia.edu/tag/0AEL)
* [Stacks Project, Tag 0832](https://stacks.math.columbia.edu/tag/0832)
* [Stacks Project, Tag 0833](https://stacks.math.columbia.edu/tag/0833)
* [Stacks Project, Tag 05IE](https://stacks.math.columbia.edu/tag/05IE)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry.Space

/-! ### Scheme-theoretic density of the inverse image of a dense open -/

/-! ### Descent of a morphism along the kernel pair -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme-theoretic closure of a scheme-theoretically dense open subspace is the whole
space: this is the density condition of Stacks 0834 tested at the identity. -/
private theorem schemeTheoreticClosure_eq_top_of_dense
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (hdense : IsSchemeTheoreticallyDense B S hS U) :
    schemeTheoreticClosure B S hS U = ⊤ := by
  simpa only [Subfunctor.preimage_id] using hdense hX (𝟙 X) (fun _ _ hφ => by simpa using hφ)

/-- Flatness and local finite presentation pass to the base change of a morphism of algebraic
spaces. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_of_isPullback
    {W Z X Y : AlgebraicSpaces B S hS} {p : W ⟶ Z} {q : W ⟶ X} {f : Z ⟶ Y} {g : X ⟶ Y}
    (sq : IsPullback p q f g) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    IsFlat B S hS q.hom ∧ IsLocallyOfFinitePresentation B S hS q.hom := by
  have := isFlat_isStableUnderBaseChange B S hS
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  exact ⟨MorphismProperty.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFlat B S hS f.hom) sq hflat,
    MorphismProperty.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFinitePresentation B S hS f.hom) sq hlfp⟩

/-- A surjective, flat morphism of algebraic spaces over `S` which is locally of finite
presentation is locally surjective for the big fppf topology: it is representable by algebraic
spaces, and each of surjectivity, flatness and local finite presentation is inherited by its
representable base changes. -/
private theorem isLocallySurjective_of_surjective_flat_lfp
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z) (g : X ⟶ Z)
    (hsurj : IsSurjective B S hS g) (hflat : IsFlat B S hS g)
    (hlfp : IsLocallyOfFinitePresentation B S hS g) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g := by
  have := isFlat_isStableUnderBaseChange B S hS
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  apply isLocallySurjective_of_isRepresentableByAlgebraicSpaces B S hS hX.isSheaf hZ.isSheaf g
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hX hZ g)
  all_goals
    intro U ξ
    have hpb := (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk ξ :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk g : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)).flip
  · exact (isFlat_and_isLocallyOfFinitePresentation_of_isPullback B S hS hpb hflat hlfp).1
  · exact (isFlat_and_isLocallyOfFinitePresentation_of_isPullback B S hS hpb hflat hlfp).2
  · exact isSurjective_of_isPullback B S hS hpb hsurj

/-- A morphism of presheaves into a sheaf which equalizes the two projections of the kernel pair
of a locally surjective morphism factors uniquely through that morphism, compatibly with a given
morphism to a common base.

The range of the locally surjective morphism is an effective epimorphic image of the source, so
the morphism descends to that range; the range sheafifies to the whole target precisely because
the morphism is locally surjective, and the descended morphism extends over the sheafification by
the sheaf property. Uniqueness of that extension gives the compatibility over the base. -/
private theorem exists_factorization_of_kernelPair
    {C : Type*} [Category.{v} C] (J : GrothendieckTopology C)
    {X Y Z T : Cᵒᵖ ⥤ Type u}
    (hY : Presheaf.IsSheaf J Y) (hT : Presheaf.IsSheaf J T)
    (f : X ⟶ Y) (g : X ⟶ Z) (pY : Y ⟶ T) (pZ : Z ⟶ T)
    (hg : Presheaf.IsLocallySurjective J g)
    (hbase : f ≫ pY = g ≫ pZ)
    (heq : pullback.fst g g ≫ f = pullback.snd g g ≫ f) :
    ∃ h : Z ⟶ Y, g ≫ h = f ∧ h ≫ pY = pZ := by
  let R := Subfunctor.range g
  let q := Subfunctor.toRange g
  have hcompat : ∀ {W : Cᵒᵖ ⥤ Type u} (a b : W ⟶ X),
      a ≫ q = b ≫ q → a ≫ f = b ≫ f := by
    intro W a b hab
    have hab' : a ≫ g = b ≫ g := by
      simpa [q, R] using congrArg (fun k => k ≫ R.ι) hab
    have h := congrArg (fun k => pullback.lift a b hab' ≫ k) heq
    simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h
  have := IsRegularEpiCategory.regularEpiOfEpi q
  let l : R.toFunctor ⟶ Y := EffectiveEpi.desc q f hcompat
  have hl : q ≫ l = f := EffectiveEpi.fac q f hcompat
  let j := Subfunctor.homOfLe (R.le_sheafify J)
  let k := (R.sheafify J).ι
  let l' := R.sheafifyLift l ((isSheaf_iff_isSheaf_of_type J Y).mp hY)
  have hj : j ≫ l' = l := R.to_sheafifyLift l _
  have : IsIso k := (R.sheafify J).eq_top_iff_isIso.mp
    ((Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' J g).mp hg)
  have hqjk : q ≫ j ≫ k = g := by simp [q, j, k, R]
  let h := inv k ≫ l'
  have hgh : g ≫ h = f := by
    rw [← hqjk]
    dsimp [h]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc, hj] using hl
  refine ⟨h, hgh, ?_⟩
  apply (cancel_epi k).mp
  have hunique : l' ≫ pY = k ≫ pZ := by
    apply R.to_sheafify_lift_unique ((isSheaf_iff_isSheaf_of_type J T).mp hT)
    apply (cancel_epi q).mp
    show q ≫ j ≫ l' ≫ pY = q ≫ j ≫ k ≫ pZ
    rw [reassoc_of% hj, reassoc_of% hl, reassoc_of% hqjk, hbase]
  simpa [h] using hunique

/-- **Stacks 0AEL.** Let `f : X ⟶ Y` and `g : X ⟶ Z` be morphisms of algebraic spaces over an
algebraic space `T` with `Y ⟶ T` separated and `g` surjective, flat and locally of finite
presentation. If there is a scheme-theoretically dense open subspace `V ⊆ Z` such that the
restriction of `f` to `g⁻¹(V)` factors through `V` over `T`, then `f` factors through `g`
over `T`. -/
@[stacks 0AEL]
theorem exists_factorization_of_dense_open
    {T X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (pX : X ⟶ T) (pY : Y ⟶ T) (pZ : Z ⟶ T) (f : X ⟶ Y) (g : X ⟶ Z)
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pX)
    (hsep : IsSeparated B S hS pY)
    (hsurj : IsSurjective B S hS g) (hflat : IsFlat B S hS g)
    (hlfp : IsLocallyOfFinitePresentation B S hS g)
    (V : Subfunctor Z) (hV : IsOpenSubspace B S hS V)
    (hdense : IsSchemeTheoreticallyDense B S hS V)
    (hfactor : ∃ v : V.toFunctor ⟶ Y,
      (v ≫ pY = V.ι ≫ pZ) ∧
      (pullback.fst g V.ι ≫ f = pullback.snd g V.ι ≫ v)) :
    ∃ h : Z ⟶ Y, (g ≫ h = f) ∧ (h ≫ pY = pZ) := by
  let R := pullback g g
  let r : R ⟶ Z := pullback.fst g g ≫ g
  have hR : IsAlgebraicSpace B S hS R := isAlgebraicSpace_pullback B S hS g g hX hX hZ
  have hpb := (AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk g : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
    (ObjectProperty.homMk g : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)).flip
  obtain ⟨hflatR', hlfpR'⟩ :=
    isFlat_and_isLocallyOfFinitePresentation_of_isPullback B S hS hpb hflat hlfp
  have hflatR : IsFlat B S hS r := isFlat_comp B S hS hR hX hZ _ g hflatR' hflat
  have hlfpR : IsLocallyOfFinitePresentation B S hS r :=
    isLocallyOfFinitePresentation_comp B S hS hR hX hZ _ g hlfpR' hlfp
  obtain ⟨v, hv, hfv⟩ := hfactor
  let U := V.preimage r
  let a : U.toFunctor ⟶ pullback g V.ι :=
    pullback.lift (U.ι ≫ pullback.fst g g) (V.fromPreimage r)
      (by simpa only [U, r, Category.assoc] using (V.fromPreimage_ι r).symm)
  let b : U.toFunctor ⟶ pullback g V.ι :=
    pullback.lift (U.ι ≫ pullback.snd g g) (V.fromPreimage r)
      (by simpa only [U, r, Category.assoc, pullback.condition] using (V.fromPreimage_ι r).symm)
  have hlocal : U.ι ≫ (pullback.fst g g ≫ f) =
      U.ι ≫ (pullback.snd g g ≫ f) := by
    have ha := congrArg (fun k => a ≫ k) hfv
    have hb := congrArg (fun k => b ≫ k) hfv
    simp only [a, b, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] at ha hb
    exact ha.trans hb.symm
  have heq : pullback.fst g g ≫ f = pullback.snd g g ≫ f := by
    apply eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top B S hS hT hR hY
      (r ≫ pZ) pY _ _ _ _ U (isOpenSubspace_preimage B S hS r V hZ hR hV) hlocal
      (schemeTheoreticClosure_eq_top_of_dense B S hS hR U
        (isSchemeTheoreticallyDense_preimage_of_isFlat B S hS hR hZ r hflatR hlfpR V hV hdense))
      hsep
    · simp [r, Category.assoc, hf, hg]
    · simp only [Category.assoc, hf, r, ← hg]
      exact congrArg (fun k => k ≫ pZ) (pullback.condition (f := g) (g := g)).symm
  exact exists_factorization_of_kernelPair
    (BigFppfOver.topology B S hS) hY.isSheaf hT.isSheaf f g pY pZ
    (isLocallySurjective_of_surjective_flat_lfp B S hS hX hZ g hsurj hflat hlfp)
    (hf.trans hg.symm) heq

end AlgebraicGeometry.Space

end
