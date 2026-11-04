module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting

/-!
# Level sets of a weighting that factors through an étale morphism

Let `f : X ⟶ Y` be a morphism of schemes and let `w : X → ℤ` be a weighting of `f`. We show
that if `f` factors as a closed immersion followed by an étale morphism, then `w` is in fact
locally constant, so that each of its level sets is open and closed and in particular locally
constructible.

This is the final step of the argument for Stacks Tag 0F3G, where the general locally
quasi-finite case is reduced — by Zariski's main theorem and a finite locally free base change —
to the case of a morphism which is an immersion.

## Main results

* `AlgebraicGeometry.IsWeighting.isLocallyConstant_of_isClosedImmersion_etale`: a weighting of a
  morphism that factors as a closed immersion followed by an étale morphism is locally constant.
* `AlgebraicGeometry.IsWeighting.isLocallyConstant_of_locally_isClosedImmersion_etale`: the same
  conclusion when such a factorization exists only locally on the source.
* `AlgebraicGeometry.IsWeighting.isLocallyConstant_of_isImmersion` and
  `AlgebraicGeometry.IsWeighting.isLocallyConstant_of_etale`: the two special cases obtained by
  taking the étale morphism to be an open immersion, respectively the closed immersion to be the
  identity.
* `AlgebraicGeometry.isLocallyConstructible_weighting_levelSet_of_isImmersion` and
  `AlgebraicGeometry.isLocallyConstructible_weighting_levelSet_of_etale`: the level sets of such a
  weighting are locally constructible.

## Implementation notes

The defining property of a weighting is applied to the étale base change `g : V ⟶ Y` itself,
with the finite open piece of `X ×_Y V` taken to be the graph of the given factorization
`π : X ⟶ V`. That graph is the section `pullback.lift (𝟙 X) π` of the projection
`pullback.fst f g`, which is étale because `g` is; being also a split monomorphism, the section
is flat, locally of finite presentation and a monomorphism, hence an open immersion by
`AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`. The resulting weighted fibre sum along the
closed immersion `π` is computed by a single term, because `π` is injective on points and its
residue field extensions are trivial, so that the sum is `w` transported along `π`.

## References

* [Stacks Project, Tag 0F3G](https://stacks.math.columbia.edu/tag/0F3G)
-/

public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- A field extension whose structure map is bijective has separable degree one. -/
private lemma finSepDegree_eq_one_of_bijective {K L : Type u} [Field K] [Field L] [Algebra K L]
    (h : Function.Bijective (algebraMap K L)) : Field.finSepDegree K L = 1 := by
  rw [← Field.finSepDegree_eq_of_equiv _ _ _ (AlgEquiv.ofBijective (Algebra.ofId K L)
    (by simpa [Algebra.ofId] using h)), Field.finSepDegree_self]

/-- A closed immersion induces an isomorphism on residue fields. -/
private lemma residueFieldMap_bijective {X V : Scheme.{u}} (π : X ⟶ V)
    [IsClosedImmersion π] (x : X) : Function.Bijective (π.residueFieldMap x) := by
  have hst : Function.Surjective (π.stalkMap x) := π.stalkMap_surjective x
  have hcomp : Function.Surjective (V.residue (π x) ≫ π.residueFieldMap x) := by
    rw [Scheme.residue_residueFieldMap]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (X.residue_surjective x).comp hst
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hcomp
  exact ⟨(π.residueFieldMap x).hom.injective, hcomp.of_comp⟩

/-- Along a closed immersion the separable-degree weighted fibre sum of `w` is `w` itself,
transported to the image. -/
private lemma separableDegreeWeightedFiberSum_apply {X V : Scheme.{u}} (π : X ⟶ V)
    [IsClosedImmersion π] (w : X → ℤ) (x : X) :
    separableDegreeWeightedFiberSum π w (π x) = w x := by
  have hinj : Function.Injective π.base := π.isClosedEmbedding.injective
  unfold separableDegreeWeightedFiberSum
  rw [finsum_eq_single _ x (fun u hu => by
    have hne : ¬ (π u = π x) := fun h => hu (hinj h)
    simp [hne]), ite_eq_left rfl,
    @finSepDegree_eq_one_of_bijective (V.residueField (π x)) (X.residueField x) _ _
      ((π.residueFieldMap x).hom.toAlgebra)
      (by rw [RingHom.algebraMap_toAlgebra]; exact residueFieldMap_bijective π x)]
  simp

/-- A level set of a locally constant integer-valued function is open and closed, hence locally
constructible. -/
private lemma isLocallyConstructible_levelSet {T : Type*} [TopologicalSpace T] {w : T → ℤ}
    (hw : IsLocallyConstant w) (n : ℤ) : IsLocallyConstructible {x : T | w x = n} :=
  IsRetrocompact.isLocallyConstructible (hw.isOpen_fiber n)
    (by intro U hU _; exact hU.inter_left (hw.isClosed_fiber n))

/-- If `f : X ⟶ Y` factors as a closed immersion `π : X ⟶ V` followed by an étale morphism
`g : V ⟶ Y`, then every weighting of `f` is locally constant. -/
theorem IsWeighting.isLocallyConstant_of_isClosedImmersion_etale {X Y V : Scheme.{u}}
    {f : X ⟶ Y} {w : X → ℤ} (hw : IsWeighting f w) (π : X ⟶ V) (g : V ⟶ Y)
    [IsClosedImmersion π] [Etale g] (hcomm : π ≫ g = f) : IsLocallyConstant w := by
  have comm : (𝟙 X) ≫ f = π ≫ g := by rw [Category.id_comp, hcomm]
  set l := pullback.lift (𝟙 X) π comm
  have hfst : l ≫ pullback.fst f g = 𝟙 X := pullback.lift_fst _ _ _
  have : IsSplitMono l := IsSplitMono.mk' ⟨pullback.fst f g, hfst⟩
  have hEl : Etale l :=
    MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) l (pullback.fst f g)
      inferInstance (by rw [hfst]; infer_instance)
  have hoi : IsOpenImmersion l := IsOpenImmersion.of_flat_of_mono l
  have hlc := hw (𝟙 X) π g comm inferInstance hoi inferInstance
  have hw' : w = (separableDegreeWeightedFiberSum π w) ∘ π := by
    funext x
    exact (separableDegreeWeightedFiberSum_apply π w x).symm
  rw [hw']
  refine IsLocallyConstant.comp_continuous ?_ π.continuous
  simpa using hlc

/-- If every point of `X` has an open neighbourhood `U` such that `U ⟶ Y` factors as a closed
immersion followed by an étale morphism, then every weighting of `f : X ⟶ Y` is locally
constant. -/
theorem IsWeighting.isLocallyConstant_of_locally_isClosedImmersion_etale {X Y : Scheme.{u}}
    {f : X ⟶ Y} {w : X → ℤ} (hw : IsWeighting f w)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (V : Scheme.{u}) (π : U.toScheme ⟶ V) (g : V ⟶ Y),
      IsClosedImmersion π ∧ Etale g ∧ π ≫ g = U.ι ≫ f) :
    IsLocallyConstant w := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, hxU, V, π, g, h₁, h₂, hcomm⟩ := h x
  have hwI : IsWeighting (U.ι ≫ f) (w ∘ U.ι) := hw.comp_isOpenImmersion U.ι
  have hwU : IsLocallyConstant (w ∘ (U.ι : U.toScheme → X)) :=
    hwI.isLocallyConstant_of_isClosedImmersion_etale π g hcomm
  obtain ⟨W, hWopen, hxW, hW⟩ := hwU.exists_open ⟨x, hxU⟩
  refine ⟨U.ι.base '' W, U.ι.isOpenEmbedding.isOpenMap _ hWopen, ⟨_, hxW, rfl⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hW z hz

/-- A weighting of an immersion is locally constant. -/
theorem IsWeighting.isLocallyConstant_of_isImmersion {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsImmersion f] {w : X → ℤ} (hw : IsWeighting f w) : IsLocallyConstant w :=
  hw.isLocallyConstant_of_isClosedImmersion_etale f.liftCoborder f.coborderRange.ι
    f.liftCoborder_ι

/-- A weighting of an étale morphism is locally constant. -/
theorem IsWeighting.isLocallyConstant_of_etale {X Y : Scheme.{u}} {f : X ⟶ Y}
    [Etale f] {w : X → ℤ} (hw : IsWeighting f w) : IsLocallyConstant w :=
  hw.isLocallyConstant_of_isClosedImmersion_etale (𝟙 X) f (Category.id_comp f)

/-- **Stacks Project, Tag 0F3G**, for a morphism that factors as a closed immersion followed by
an étale morphism: every level set of a weighting is locally constructible in the source. -/
theorem isLocallyConstructible_weighting_levelSet_of_isClosedImmersion_etale
    {X Y V : Scheme.{u}} {f : X ⟶ Y} {w : X → ℤ} (hw : IsWeighting f w) (π : X ⟶ V) (g : V ⟶ Y)
    [IsClosedImmersion π] [Etale g] (hcomm : π ≫ g = f) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} :=
  isLocallyConstructible_levelSet
    (hw.isLocallyConstant_of_isClosedImmersion_etale π g hcomm) n

/-- **Stacks Project, Tag 0F3G**, for a morphism that factors locally on the source as a closed
immersion followed by an étale morphism: every level set of a weighting is locally constructible
in the source. -/
theorem isLocallyConstructible_weighting_levelSet_of_locally_isClosedImmersion_etale
    {X Y : Scheme.{u}} {f : X ⟶ Y} {w : X → ℤ} (hw : IsWeighting f w)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (V : Scheme.{u}) (π : U.toScheme ⟶ V) (g : V ⟶ Y),
      IsClosedImmersion π ∧ Etale g ∧ π ≫ g = U.ι ≫ f) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} :=
  isLocallyConstructible_levelSet
    (hw.isLocallyConstant_of_locally_isClosedImmersion_etale h) n

/-- **Stacks Project, Tag 0F3G**, for an immersion: every level set of a weighting is locally
constructible in the source. -/
theorem isLocallyConstructible_weighting_levelSet_of_isImmersion {X Y : Scheme.{u}}
    {f : X ⟶ Y} [IsImmersion f] {w : X → ℤ} (hw : IsWeighting f w) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} :=
  isLocallyConstructible_levelSet hw.isLocallyConstant_of_isImmersion n

/-- **Stacks Project, Tag 0F3G**, for an étale morphism: every level set of a weighting is
locally constructible in the source. -/
theorem isLocallyConstructible_weighting_levelSet_of_etale {X Y : Scheme.{u}}
    {f : X ⟶ Y} [Etale f] {w : X → ℤ} (hw : IsWeighting f w) (n : ℤ) :
    IsLocallyConstructible {x : X | w x = n} :=
  isLocallyConstructible_levelSet hw.isLocallyConstant_of_etale n

end AlgebraicGeometry
