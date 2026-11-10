module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralUniversallyInjectivePushforward

/-!
# Essential image of the pushforward along an integral universally injective morphism

For an integral universally injective morphism of schemes `f : X ⟶ Y`, an abelian sheaf on
`Y_étale` lies in the essential image of the direct image along `f` exactly when its support is
contained in `f(X)`, equivalently when its restriction to the open complement of `f(X)` vanishes.
The case of a closed immersion is proved directly.

## Main definitions

* `smallEtaleSupportAb`: The support of an abelian sheaf on the small étale site, the set of
  points at which some geometric stalk is nonzero.

## Main results

* `smallEtalePushforwardAb_essImage_iff_of_isClosedImmersion`: An abelian sheaf is a direct image
  along a closed immersion exactly when its restriction to the open complement vanishes.
* `isZero_smallEtalePullbackAb_iff_smallEtaleSupportAb_subset_compl`: An abelian sheaf restricts
  to zero on an open subscheme exactly when its support is disjoint from it.
* `smallEtalePushforwardAb_essImage_iff_support_of_integral_universallyInjective`: The essential
  image of the abelian direct image along an integral universally injective morphism consists of
  the sheaves with support in `f(X)`.
* `smallEtalePushforward_fullyFaithful_essImage_leftInverse_of_integral_universallyInjective`:
  The direct images of sheaves of sets and of abelian sheaves along an integral universally
  injective morphism are fully faithful, with the stated essential images and with the inverse
  image as a left inverse.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- The inverse image of abelian sheaves along the inclusion of an open subscheme, read as the
left adjoint of the direct image along base change, is restriction along composition with that
inclusion. -/
private def abelianInverseImageOpenIso {W : Scheme.{u}} (U : W.Opens) :
    (smallEtaleBaseChange U.ι).sheafPullback Ab.{u + 1}
        (smallEtaleTopology W) (smallEtaleTopology U.toScheme) ≅
      etaleRestriction.{u, u + 1} U.ι :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange U.ι) Ab.{u + 1}
      (smallEtaleTopology W) (smallEtaleTopology U.toScheme) ≪≫
    etaleAbelianInverseImageRestrictionIso.{u, u + 1} U.ι

/-- An abelian sheaf on `W_étale` is a direct image along a closed immersion `j : Z ⟶ W` exactly
when its restriction to an open subscheme `U` complementary to the image of `j` vanishes, that
is, exactly when its support is contained in `j(Z)`. -/
@[stacks 04CA "part (2): essential image"]
public theorem smallEtalePushforwardAb_essImage_iff_of_isClosedImmersion {Z W : Scheme.{u}}
    (j : Z ⟶ W) [IsClosedImmersion j] (U : W.Opens) (hU : (U : Set W) = (Set.range j.base)ᶜ)
    (G : Sheaf (smallEtaleTopology W) Ab.{u + 1}) :
    (smallEtalePushforwardAb j).essImage G ↔
      IsZero (((smallEtaleBaseChange U.ι).sheafPullback Ab.{u + 1}
        (smallEtaleTopology W) (smallEtaleTopology U.toScheme)).obj G) := by
  have hij : Set.range U.ι.base = (Set.range j.base)ᶜ := by rwa [Scheme.Opens.range_ι]
  constructor
  · rintro ⟨H, ⟨e⟩⟩
    refine IsZero.of_iso ?_ ((abelianInverseImageOpenIso.{u} U).app G)
    exact (isZero_etaleRestriction_etaleAbelianDirectImage.{u, u + 1} j U.ι hij H).of_iso
      ((etaleRestriction.{u, u + 1} U.ι).mapIso e).symm
  · intro hz
    let adj := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} j
    have hclosed : IsIso ((etaleAbelianInverseImage.{u, u + 1} j).map (adj.unit.app G)) :=
      isIso_etaleAbelianInverseImage_map_unit.{u, u + 1} j G
    have hopen : IsIso ((etaleAbelianInverseImage.{u, u + 1} U.ι).map (adj.unit.app G)) := by
      have hsrc : IsZero ((etaleAbelianInverseImage.{u, u + 1} U.ι).obj G) :=
        IsZero.of_iso hz ((Functor.sheafPullbackConstruction.sheafPullbackIso
          (smallEtaleBaseChange U.ι) Ab.{u + 1} (smallEtaleTopology W)
          (smallEtaleTopology U.toScheme)).symm.app G)
      have htgt : IsZero ((etaleAbelianInverseImage.{u, u + 1} U.ι).obj
          ((etaleAbelianDirectImage.{u, u + 1} j).obj
            ((etaleAbelianInverseImage.{u, u + 1} j).obj G))) :=
        IsZero.of_iso (isZero_etaleRestriction_etaleAbelianDirectImage.{u, u + 1} j U.ι hij _)
          ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} U.ι).app _)
      have heq : (etaleAbelianInverseImage.{u, u + 1} U.ι).map (adj.unit.app G) =
          (hsrc.iso htgt).hom := hsrc.eq_of_src _ _
      rw [heq]
      infer_instance
    have : IsIso (adj.unit.app G) :=
      isIso_of_isIso_etaleAbelianInverseImage.{u, u + 1} j U.ι hij (adj.unit.app G)
    exact adj.mem_essImage_of_unit_isIso G

/-! ### The support of an abelian sheaf -/

/-- The support of an abelian sheaf on the small étale site of a scheme: the set of points of the
scheme at which some geometric stalk of the sheaf is nonzero. -/
public def smallEtaleSupportAb {Y : Scheme.{u}} (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    Set Y :=
  {y | ∃ s : GeometricPoint Y, s.LiesOver y ∧ ¬ IsZero ((smallEtaleStalkAb s.hom).obj F)}

/-- An abelian sheaf on the small étale site of `Y` restricts to zero on an open subscheme `U`
exactly when its support is disjoint from `U`. -/
public theorem isZero_smallEtalePullbackAb_iff_smallEtaleSupportAb_subset_compl {Y : Scheme.{u}}
    (U : Y.Opens) (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    IsZero ((smallEtalePullbackAb U.ι).obj F) ↔ smallEtaleSupportAb F ⊆ (U : Set Y)ᶜ := by
  constructor
  · intro hz y hy hyU
    obtain ⟨s, hs, hns⟩ := hy
    apply hns
    have hrange : Set.range s.hom.base ⊆ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      rwa [Subsingleton.elim t default, hs]
    have hstalk : IsZero ((smallEtaleStalkAb
        (IsOpenImmersion.lift U.ι s.hom hrange ≫ U.ι)).obj F) :=
      IsZero.of_iso
        ((smallEtaleStalkAb (IsOpenImmersion.lift U.ι s.hom hrange)).map_isZero hz)
        ((smallEtalePullbackStalkAbIso U.ι (IsOpenImmersion.lift U.ι s.hom hrange)).app F).symm
    rwa [IsOpenImmersion.lift_fac _ _ hrange] at hstalk
  · intro hsupp
    refine isZero_of_geometricStalkAb_family
      (fun t : U.toScheme => U.toScheme.algClosedPointHom t) ?_ fun t => ?_
    · ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨x, default, Scheme.algClosedPointHom_apply _ x _⟩
    · refine IsZero.of_iso ?_
        ((smallEtalePullbackStalkAbIso U.ι (U.toScheme.algClosedPointHom t)).app F)
      by_contra hns
      have hmem : U.ι.base t ∈ smallEtaleSupportAb F :=
        ⟨⟨_, U.toScheme.algClosedPointHom t ≫ U.ι⟩, by
          simp [GeometricPoint.LiesOver], hns⟩
      exact hsupp hmem (by rw [← Scheme.Opens.range_ι]; exact ⟨t, rfl⟩)

/-! ### The proposition -/

section WholeStatement

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]

/-- An abelian sheaf on `Y_étale` lies in the essential image of direct image along an integral
universally injective morphism exactly when its restriction to the open complement of `f(X)`
vanishes. -/
@[stacks 04FZ "part (2): essential image, with the closed-immersion case supplied by Tag 04CA"]
public theorem smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective'
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtalePushforwardAb f).essImage F ↔
      IsZero (((smallEtaleBaseChange (openComplementRange f).ι).sheafPullback Ab.{u + 1}
        (smallEtaleTopology Y)
        (smallEtaleTopology (openComplementRange f).toScheme)).obj F) :=
  smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective f
    (fun j _ U hU G => smallEtalePushforwardAb_essImage_iff_of_isClosedImmersion j U hU G) F

/-- An abelian sheaf on `Y_étale` is a direct image along an integral universally injective
morphism exactly when its support is contained in `f(X)`. -/
public theorem smallEtalePushforwardAb_essImage_iff_support_of_integral_universallyInjective
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtalePushforwardAb f).essImage F ↔ smallEtaleSupportAb F ⊆ Set.range f.base := by
  have hcompl : (((openComplementRange f : Y.Opens) : Set Y))ᶜ = Set.range f.base := by
    change ((Set.range f.base)ᶜ)ᶜ = Set.range f.base
    exact compl_compl _
  rw [smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective' f F,
    isZero_smallEtalePullbackAb_iff_smallEtaleSupportAb_subset_compl, hcompl]

/-- Let `f : X ⟶ Y` be a morphism of schemes which is integral and universally injective.
Then (1) `f_{small, *} : Sh(X_étale) ⟶ Sh(Y_étale)` is fully faithful and its essential image is
those sheaves of sets on `Y_étale` whose restriction to `Y \ f(X)` is isomorphic to `*`, and (2)
`f_{small, *} : Ab(X_étale) ⟶ Ab(Y_étale)` is fully faithful and its essential image is those
abelian sheaves on `Y_étale` whose support is contained in `f(X)`; and in both cases
`f_{small}^{-1}` is a left inverse to `f_{small, *}`.

The four conjuncts are, in order: part (1), part (2), and the trailing clause for each of the
two sheaf categories. The complement `Y \ f(X)` is the open subscheme `openComplementRange f`,
open because an integral morphism is universally closed; being isomorphic to `*` is being a
terminal object of the category of sheaves of sets on that complement; and the support of an
abelian sheaf is `smallEtaleSupportAb`, the set of points of `Y` at which some geometric stalk
of the sheaf is nonzero. -/
@[stacks 04FZ]
public theorem
    smallEtalePushforward_fullyFaithful_essImage_leftInverse_of_integral_universallyInjective :
    (((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology Y) (smallEtaleTopology X)).Full ∧
        ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology Y) (smallEtaleTopology X)).Faithful ∧
        ∀ F : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v)),
          ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
              (smallEtaleTopology Y) (smallEtaleTopology X)).essImage F ↔
            Nonempty (IsTerminal
              ((smallEtaleInverseImage.{u, v} (openComplementRange f).ι).obj F))) ∧
      ((smallEtalePushforwardAb f).Full ∧ (smallEtalePushforwardAb f).Faithful ∧
        ∀ F : Sheaf (smallEtaleTopology Y) Ab.{u + 1},
          (smallEtalePushforwardAb f).essImage F ↔
            smallEtaleSupportAb F ⊆ Set.range f.base) ∧
      Nonempty ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (smallEtaleTopology Y) (smallEtaleTopology X) ⋙
          smallEtaleInverseImage.{u, v} f ≅
            𝟭 (Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))) ∧
      Nonempty (smallEtalePushforwardAb f ⋙ (smallEtaleBaseChange f).sheafPullback Ab.{u + 1}
            (smallEtaleTopology Y) (smallEtaleTopology X) ≅
          𝟭 (Sheaf (smallEtaleTopology X) Ab.{u + 1})) :=
  ⟨⟨(smallEtalePushforwardFullyFaithful_of_integral_universallyInjective.{u, v} f).full,
      (smallEtalePushforwardFullyFaithful_of_integral_universallyInjective.{u, v} f).faithful,
      smallEtalePushforward_essImage_iff_of_integral_universallyInjective.{u, v} f⟩,
    ⟨(smallEtalePushforwardAbFullyFaithful_of_integral_universallyInjective f).full,
      (smallEtalePushforwardAbFullyFaithful_of_integral_universallyInjective f).faithful,
      smallEtalePushforwardAb_essImage_iff_support_of_integral_universallyInjective f⟩,
    ⟨smallEtalePushforwardCompInverseImageIso_of_integral_universallyInjective.{u, v} f⟩,
    ⟨smallEtalePushforwardAbCompPullbackIso_of_integral_universallyInjective f⟩⟩

end WholeStatement

end Stacks.EtaleCohomology

end
