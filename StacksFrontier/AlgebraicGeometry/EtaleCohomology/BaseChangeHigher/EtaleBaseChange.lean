module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.HigherBaseChangeDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.LadderAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite

/-!
# Base change along open immersions and universal homeomorphisms, in all degrees

Let

```
X' <--h-- Y
|f'       |e
S  <--g-- T
```

be a commutative square of schemes and `q ≥ 0`. This file proves that the base change map
`(f')⁻¹ R^q g_* ⟶ R^q h_* e⁻¹` of [Stacks, Tag 0F02] is an isomorphism in every degree in two
situations: when the square is cartesian and `f'` is an open immersion, and when `f'` is the
identity and `e` is a universal homeomorphism. As an application, invertibility of the base
change map can be tested over the affine opens of `S`.

The argument is the same in both cases. In degree zero the base change map is the mate
`(f')⁻¹ g_* ⟶ (f')⁻¹ g_* e_* e⁻¹ ≅ (f')⁻¹ (f')_* h_* e⁻¹ ⟶ h_* e⁻¹`, so it is invertible as soon
as `(f')⁻¹ g_*` inverts the unit of `e` and the counit of `f'` is invertible. Higher degrees
follow by dimension shifting: if `e⁻¹` preserves injective objects, an embedding `F ⊂ I` into an
injective sheaf gives a comparison ladder between the two long exact sequences whose fourth
term vanishes on both rows, and the four lemma and a diagram chase carry invertibility from
degree `q` to degree `q + 1`.

For an open immersion `j` the inverse image is restriction along `j`, which is left adjoint to
`j_*` through the adjunction of the small étale sites; its counit is invertible because
composition with a monomorphism is fully faithful, so `j_*` is fully faithful, and restriction
preserves injective objects. The unit of `e` is inverted by `(f')⁻¹ g_*` because restriction
along `f'` commutes with the direct images around the cartesian square and `e⁻¹` inverts the
unit of `e`. For a universal homeomorphism `i` the inverse image is an equivalence of the small
étale topoi ([Stacks, Tag 03SI]), so its unit is invertible and it preserves injective objects.

## Main results

* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_zero` — dimension shifting:
  invertibility in degree zero and preservation of injectives by `e⁻¹` give invertibility in
  all degrees.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isOpenImmersion` — base change
  along an open immersion, in all degrees.
* `Stacks.EtaleCohomology.isEquivalence_smallEtalePullbackAb_of_universalHomeomorphism` — the
  inverse image along a universal homeomorphism is an equivalence of abelian étale topoi.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_universalHomeomorphism` — the
  comparison `R^q g_* ⟶ R^q (i ≫ g)_* i⁻¹` along a universal homeomorphism `i` is invertible
  in all degrees.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_forall_isAffine` — invertibility
  of the base change map can be checked after base change to the affine opens of `S`.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section DegreeZero

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The underived base change map, unfolded.** It is the mate
`(f')⁻¹ g_* ⟶ (f')⁻¹ g_* e_* e⁻¹ ≅ (f')⁻¹ (f')_* h_* e⁻¹ ⟶ h_* e⁻¹`. -/
theorem smallEtaleBaseChangeAb_app_eq (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtaleBaseChangeAb f' g h e w).app G =
      (smallEtalePullbackAb f').map
          ((smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app G)) ≫
        (smallEtalePullbackAb f').map
          ((smallEtaleSquarePushforwardIso f' g h e w).hom.app ((smallEtalePullbackAb e).obj G)) ≫
        (smallEtaleAdjunctionAb f').counit.app
          ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj G)) := by
  rw [smallEtaleBaseChangeAb_eq_mate]
  simp [Stacks.Cohomology.BaseChange.mate]

/-- **A criterion for the underived base change map to be invertible.** It is invertible at
`G` as soon as `(f')⁻¹ g_*` inverts the unit of `e` at `G` and the counit of `f'` is invertible
at `h_* e⁻¹ G`. -/
theorem isIso_smallEtaleBaseChangeAb_app (G : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hunit : IsIso ((smallEtalePullbackAb f').map
      ((smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app G))))
    (hcounit : IsIso ((smallEtaleAdjunctionAb f').counit.app
      ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj G)))) :
    IsIso ((smallEtaleBaseChangeAb f' g h e w).app G) := by
  rw [smallEtaleBaseChangeAb_app_eq]
  infer_instance

/-- **In degree zero the base change map on higher direct images is invertible exactly when
the underived base change map is.** The two differ by the identifications of the left exact
direct images with their degree-zero right derived functors. -/
theorem isIso_higherBaseChangeMapAb_zero_app_iff (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e w 0).app G) ↔
      IsIso ((smallEtaleBaseChangeAb f' g h e w).app G) := by
  have key := map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero f' g h e w G
  have : PreservesFiniteLimits (smallEtalePushforwardAb g) :=
    have := (smallEtaleAdjunctionAb g).rightAdjoint_preservesLimits
    inferInstance
  have : PreservesFiniteLimits (smallEtalePushforwardAb h) :=
    have := (smallEtaleAdjunctionAb h).rightAdjoint_preservesLimits
    inferInstance
  have : IsIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) G) :=
    Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit _ _
  have : IsIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb h)
      ((smallEtalePullbackAb e).obj G)) :=
    Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit _ _
  rw [← isIso_comp_left_iff ((smallEtalePullbackAb f').map
      (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) G ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.app G)),
    key, isIso_comp_right_iff]

end DegreeZero

section DimensionShifting

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **Dimension shifting for the base change map.** If the base change map of a commutative
square is invertible in degree zero on every sheaf and `e⁻¹` carries injective sheaves to
injective sheaves, then the base change map is invertible in every degree on every sheaf.

The induction embeds `F` into an injective sheaf `I` with quotient `Q`. In the comparison ladder
of the two long exact sequences the terms `(f')⁻¹R^{q+1} g_* I` and `R^{q+1} h_* e⁻¹ I` vanish,
`e⁻¹ I` being injective; the four lemma gives injectivity in degree `q + 1` and the surjectivity
of the lower connecting map gives surjectivity. -/
theorem isIso_higherBaseChangeMapAb_app_of_isIso_zero
    (h0 : ∀ G : Sheaf (smallEtaleTopology T) Ab.{u + 1},
      IsIso ((higherBaseChangeMapAb f' g h e w 0).app G))
    (hinj : ∀ (I : Sheaf (smallEtaleTopology T) Ab.{u + 1}), Injective I →
      Injective ((smallEtalePullbackAb e).obj I)) :
    ∀ (q : ℕ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
      IsIso ((higherBaseChangeMapAb f' g h e w q).app G) := by
  intro q
  induction q with
  | zero => exact h0
  | succ q ih =>
    intro F
    let SC := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : SC.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
    have hI : IsZero ((higherBaseChangeSource f' g (q + 1)).obj SC.X₂) :=
      Functor.map_isZero (smallEtalePullbackAb f')
        (Functor.isZero_rightDerived_obj_injective_succ _ _ _)
    have : Injective ((smallEtalePullbackAb e).obj SC.X₂) :=
      hinj _ (inferInstanceAs (Injective (Injective.under F)))
    have hI' : IsZero ((higherBaseChangeTarget h e (q + 1)).obj SC.X₂) :=
      Functor.isZero_rightDerived_obj_injective_succ _ _ _
    let L := higherBaseChangeLadder f' g h e w q hS hI
    have hδt : Epi L.δtarget := L.exact_target_comp.epi_f (hI'.eq_of_tgt _ 0)
    have hepi : Epi ((higherBaseChangeMapAb f' g h e w (q + 1)).app F) := by
      have : Epi ((higherBaseChangeMapAb f' g h e w q).app SC.X₃ ≫ L.δtarget) := epi_comp _ _
      rw [L.comm] at this
      exact epi_of_epi L.δsource _
    have hmono : Mono ((higherBaseChangeMapAb f' g h e w (q + 1)).app F) :=
      Stacks.Cohomology.BaseChange.mono_of_ladder L.zero_source L.zero_target
        ((higherBaseChangeMapAb f' g h e w q).naturality SC.g).symm L.comm L.exact_target
        L.epi_δsource inferInstance inferInstance
    exact isIso_of_mono_of_epi _

/-- The base change map is invertible in all degrees once `e⁻¹` preserves injectives, `(f')⁻¹ g_*`
inverts the unit of `e` and the counit of `f'` is invertible on `h_* e⁻¹`. -/
private theorem isIso_higherBaseChangeMapAb_app_of_unit_of_counit
    [(smallEtalePullbackAb e).PreservesInjectiveObjects]
    (hunit : ∀ G : Sheaf (smallEtaleTopology T) Ab.{u + 1}, IsIso ((smallEtalePullbackAb f').map
      ((smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app G))))
    [∀ G : Sheaf (smallEtaleTopology T) Ab.{u + 1}, IsIso ((smallEtaleAdjunctionAb f').counit.app
      ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj G)))]
    (q : ℕ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e w q).app G) :=
  isIso_higherBaseChangeMapAb_app_of_isIso_zero f' g h e w (fun G ↦
    (isIso_higherBaseChangeMapAb_zero_app_iff f' g h e w G).2
      (isIso_smallEtaleBaseChangeAb_app f' g h e w G (hunit G) inferInstance))
    (fun _ hI ↦ (smallEtalePullbackAb e).injective_obj_of_injective hI) q G

end DimensionShifting

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **Restriction along an étale morphism is the inverse image.** For `j : U ⟶ X` étale,
restriction of abelian sheaves along `j` is left adjoint to `j_*` through the adjunction of
composition with `j` and base change along `j` on the small étale sites, so it is canonically
isomorphic to the inverse image `j⁻¹`. -/
def smallEtalePullbackAbIsoEtaleRestriction :
    smallEtalePullbackAb j ≅ etaleRestriction.{u, 0} j :=
  (smallEtaleAdjunctionAb j).leftAdjointUniq
    ((smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := Ab.{u + 1})
      (smallEtaleTopology U) (smallEtaleTopology X))

/-- The inverse image along an étale morphism preserves injective abelian sheaves: it is
restriction, whose left adjoint, extension by zero, preserves monomorphisms. -/
instance smallEtalePullbackAb_preservesInjectiveObjects :
    (smallEtalePullbackAb j).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    have := hI
    exact Injective.of_iso ((smallEtalePullbackAbIsoEtaleRestriction j).app I).symm
      (Functor.injective_obj (etaleRestriction.{u, 0} j) I)

variable [Mono j]

/-- The counit of the restriction/direct-image adjunction along an étale monomorphism is
invertible: on sections it is the restriction along the unit of composition with `j` and base
change along `j`, which is invertible because composition with a monomorphism is fully
faithful. -/
theorem isIso_smallEtaleRestrictionAdjunctionAb_counit :
    IsIso ((smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := Ab.{u + 1})
      (smallEtaleTopology U) (smallEtaleTopology X)).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf (smallEtaleTopology U) Ab.{u + 1}),
    NatTrans.isIso_iff_isIso_app]
  intro V
  simp only [Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft, Adjunction.op]
  change IsIso (_ ≫ P.obj.map (((smallEtaleComposeBaseChangeAdj j).unit.app V.unop).op) ≫ _)
  have i1 : IsIso (P.obj.map ((smallEtaleComposeBaseChangeAdj j).unit.app V.unop).op) :=
    inferInstance
  have i2 : IsIso (((smallEtaleCompose j).op.associator (smallEtaleBaseChange j).op
    P.obj).inv.app V) := Iso.isIso_inv (((smallEtaleCompose j).op.associator
      (smallEtaleBaseChange j).op P.obj).app V)
  have i3 : IsIso (P.obj.leftUnitor.hom.app V) := Iso.isIso_hom (P.obj.leftUnitor.app V)
  exact IsIso.comp_isIso' i2 (IsIso.comp_isIso' i1 i3)

/-- **The direct image along an étale monomorphism is fully faithful.** -/
def smallEtalePushforwardAbFullyFaithful : (smallEtalePushforwardAb j).FullyFaithful :=
  have := isIso_smallEtaleRestrictionAdjunctionAb_counit j
  ((smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := Ab.{u + 1})
    (smallEtaleTopology U) (smallEtaleTopology X)).fullyFaithfulROfIsIsoCounit

/-- The direct image of abelian sheaves along an étale monomorphism is full. -/
instance smallEtalePushforwardAb_full : (smallEtalePushforwardAb j).Full :=
  (smallEtalePushforwardAbFullyFaithful j).full

/-- The direct image of abelian sheaves along an étale monomorphism is faithful. -/
instance smallEtalePushforwardAb_faithful : (smallEtalePushforwardAb j).Faithful :=
  (smallEtalePushforwardAbFullyFaithful j).faithful

end OpenImmersion

section OpenImmersionSquare

variable {X' Y S T : Scheme.{u}} {f' : X' ⟶ S} {g : T ⟶ S} {h : Y ⟶ X'} {e : Y ⟶ T}

/-- In a cartesian square with `f'` an étale monomorphism, `(f')⁻¹ g_*` inverts the unit of
`e`: restriction along `f'` commutes with the two direct images around the square, and `e⁻¹`
inverts the unit of `e` because `e_*` is fully faithful. -/
theorem isIso_smallEtalePullbackAb_map_map_unit (sq : IsPullback h e f' g) [Etale f'] [Mono f']
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((smallEtalePullbackAb f').map
      ((smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app G))) := by
  have : Etale e := MorphismProperty.of_isPullback sq inferInstance
  have : Mono e := MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _)
    sq (MorphismProperty.monomorphisms.infer_property _)
  set η := (smallEtaleAdjunctionAb e).unit.app G
  have h2 : IsIso ((etaleRestriction.{u, 0} e).map η) :=
    (NatIso.isIso_map_iff (smallEtalePullbackAbIsoEtaleRestriction e) η).1 inferInstance
  have h3 : IsIso ((etaleRestrictionAt e Ab.{u + 1} ⋙
      (smallEtaleBaseChange h).sheafPushforwardContinuous Ab.{u + 1}
        X'.smallEtaleTopology Y.smallEtaleTopology).map η) := by
    change IsIso ((smallEtalePushforwardAb h).map ((etaleRestriction.{u, 0} e).map η))
    infer_instance
  have h4 := (NatIso.isIso_map_iff (etaleRestrictionPushforwardIsoOfIsPullback Ab.{u + 1} sq)
    η).1 h3
  have h5 : IsIso ((etaleRestriction.{u, 0} f').map ((smallEtalePushforwardAb g).map η)) := h4
  exact (NatIso.isIso_map_iff (smallEtalePullbackAbIsoEtaleRestriction f') _).2 h5

/-- **Base change along an open immersion, in all degrees.** For a cartesian square

```
X' <--h-- Y
|f'       |e
S  <--g-- T
```

with `f'` an étale monomorphism — for instance an open immersion — the base change map
`(f')⁻¹ R^q g_* ⟶ R^q h_* e⁻¹` is an isomorphism for every `q` and every abelian sheaf on the
small étale site of `T`. -/
theorem isIso_higherBaseChangeMapAb_app_of_etale_of_mono (sq : IsPullback h e f' g) [Etale f']
    [Mono f'] (q : ℕ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app G) := by
  have : Etale e := MorphismProperty.of_isPullback sq inferInstance
  exact isIso_higherBaseChangeMapAb_app_of_unit_of_counit f' g h e sq.w
    (isIso_smallEtalePullbackAb_map_map_unit sq) q G

/-- **Base change along an open immersion, in all degrees**: the case of an open immersion of
`isIso_higherBaseChangeMapAb_app_of_etale_of_mono`. -/
theorem isIso_higherBaseChangeMapAb_app_of_isOpenImmersion (sq : IsPullback h e f' g)
    [IsOpenImmersion f'] (q : ℕ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app G) :=
  isIso_higherBaseChangeMapAb_app_of_etale_of_mono sq q G

end OpenImmersionSquare

section UniversalHomeomorphism

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [UniversalHomeomorphism i]

/-- Direct image of abelian sheaves along a universal homeomorphism is an equivalence of the
small étale topoi: base change along it is a dense subsite inclusion. -/
theorem isEquivalence_smallEtalePushforwardAb_of_universalHomeomorphism :
    (smallEtalePushforwardAb i).IsEquivalence :=
  have := isDenseSubsite_of_universalHomeomorphism i
  inferInstanceAs
    ((smallEtaleBaseChange i).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology X) (smallEtaleTopology Z)).IsEquivalence

/-- **Inverse image of abelian sheaves along a universal homeomorphism is an equivalence of
the small étale topoi** ([Stacks, Tag 03SI]): it is left adjoint to the direct image, which is
an equivalence. -/
theorem isEquivalence_smallEtalePullbackAb_of_universalHomeomorphism :
    (smallEtalePullbackAb i).IsEquivalence := by
  have := isEquivalence_smallEtalePushforwardAb_of_universalHomeomorphism i
  exact Functor.isEquivalence_of_iso (Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb i)
    (smallEtalePushforwardAb i).asEquivalence.symm.toAdjunction).symm

/-- **The comparison along a universal homeomorphism, in all degrees.** For a universal
homeomorphism `i : Z ⟶ X` and `g : X ⟶ S`, the base change map
`R^q g_* ⟶ R^q (i ≫ g)_* i⁻¹` of the square with inverse-image legs `𝟙 S` and `i` is an
isomorphism for every `q`: `i⁻¹` is an equivalence, so its unit is invertible and it preserves
injective sheaves. -/
theorem isIso_higherBaseChangeMapAb_app_of_universalHomeomorphism {S : Scheme.{u}} (g : X ⟶ S)
    (b : S ⟶ S) (hb : b = 𝟙 S) (gi : Z ⟶ S) (w : gi ≫ b = i ≫ g) (q : ℕ)
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb b g gi i w q).app G) := by
  have := isEquivalence_smallEtalePullbackAb_of_universalHomeomorphism i
  have : (smallEtalePushforwardAb b).IsEquivalence :=
    Functor.isEquivalence_of_iso (smallEtalePushforwardAbIdOf b hb).symm
  exact isIso_higherBaseChangeMapAb_app_of_unit_of_counit b g gi i w
    (fun _ ↦ inferInstance) q G

end UniversalHomeomorphism

section Localization

/-- **Every abelian sheaf on the small étale site of an empty scheme is zero**: every object of
the site has empty underlying scheme, so it is covered by the empty sieve and the sheaf condition
makes its sections terminal. -/
private theorem isZero_of_isEmpty {T : Scheme.{u}} [IsEmpty T]
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) : IsZero G := by
  refine IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) G
    (Functor.isZero _ fun U ↦ ?_)
  have : IsEmpty U.unop.left := ⟨fun x ↦ (IsEmpty.false (α := T) (U.unop.hom x)).elim⟩
  have H : (⊥ : Sieve U.unop) ∈ smallEtaleTopology T U.unop :=
    (mem_smallEtaleTopology_iff ⊥).mpr fun w ↦ isEmptyElim w
  exact (G.isTerminalOfBotCover U.unop H).isZero

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)

/-- **The base change map over an empty base of the sheaf is invertible**: both sides vanish. -/
theorem isIso_higherBaseChangeMapAb_app_of_isEmpty [IsEmpty T] (w : h ≫ f' = e ≫ g) (q : ℕ)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e w q).app G) := by
  have : IsEmpty Y := ⟨fun y ↦ isEmptyElim (e y)⟩
  have hR : ∀ {A B : Scheme.{u}} [IsEmpty A] (k : A ⟶ B)
      (M : Sheaf (smallEtaleTopology A) Ab.{u + 1}),
      IsZero (((smallEtalePushforwardAb k).rightDerived q).obj M) := by
    intro A B _ k M
    have hM := isZero_of_isEmpty M
    have : Injective M := hM.injective
    cases q with
    | zero =>
      exact ((smallEtalePushforwardAb k).map_isZero hM).of_iso
        (asIso ((smallEtalePushforwardAb k).toRightDerivedZero.app M)).symm
    | succ q => exact Functor.isZero_rightDerived_obj_injective_succ _ _ _
  have hs : IsZero ((smallEtalePullbackAb f').obj
      (((smallEtalePushforwardAb g).rightDerived q).obj G)) :=
    Functor.map_isZero _ (hR g G)
  have ht : IsZero (((smallEtalePushforwardAb h).rightDerived q).obj
      ((smallEtalePullbackAb e).obj G)) := hR h _
  exact ⟨⟨ht.to_ _, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩

/-- The base change map depends on the two inverse-image legs only through the morphisms
themselves: equal legs give base change maps that are invertible together. -/
theorem isIso_higherBaseChangeMapAb_app_congr {u u' : X' ⟶ S} {v v' : Y ⟶ T} (hu : u = u')
    (hv : v = v') (w : h ≫ u = v ≫ g) (w' : h ≫ u' = v' ≫ g) (q : ℕ)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb u g h v w q).app G) ↔
      IsIso ((higherBaseChangeMapAb u' g h v' w' q).app G) := by
  subst hu hv
  rfl

private theorem isIso_of_isIso_comp_comp {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X}
    {b : X ⟶ Y} {c : Y ⟶ Z} [IsIso a] [IsIso c] (_ : IsIso (a ≫ b ≫ c)) : IsIso b :=
  have := IsIso.of_isIso_comp_left a (b ≫ c)
  IsIso.of_isIso_comp_right b c

/-- A morphism of abelian sheaves whose inverse image along an open immersion `p` is invertible
is invertible on the stalk at every geometric point factoring through `p`. -/
private theorem isIso_smallEtaleStalkAb_map_of_isIso_pullbackAb {W X : Scheme.{u}} (p : W ⟶ X)
    [IsOpenImmersion p] (x : GeometricPoint X) (hx : Set.range x.hom ⊆ Set.range p)
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G)
    [IsIso ((smallEtalePullbackAb p).map φ)] : IsIso ((smallEtaleStalkAb x.hom).map φ) := by
  have hst := (NatIso.isIso_map_iff (smallEtalePullbackStalkAbIso p
    (IsOpenImmersion.lift p x.hom hx)) φ).1
    (inferInstanceAs (IsIso ((smallEtaleStalkAb _).map ((smallEtalePullbackAb p).map φ))))
  rwa [IsOpenImmersion.lift_fac] at hst

/-- **Invertibility of the base change map is local on the base.** For a cartesian square

```
X' <--h-- Y
|f'       |e
S  <--g-- T
```

the base change map `(f')⁻¹ R^r g_* F ⟶ R^r h_* e⁻¹ F` is an isomorphism as soon as, for every
affine open `V ⊆ S` over which `T` is nonempty, the base change map of the restricted square
`X' ×_S V ← T ×_S V` is an isomorphism on the restriction of `F`. This is the step *"we may
replace `S` by an affine open"* of [Stacks, Tag 0F07].

Invertibility is checked on the stalks at the geometric points of `X'`; such a point factors
through `X' ×_S V` for an affine open `V` containing its image, and there the restriction of the
base change map is, by pasting with the base change squares along the open immersions
`X' ×_S V ⟶ X'` and `T ×_S V ⟶ T`, the base change map over `V`, those two squares contributing
isomorphisms in every degree. -/
theorem isIso_higherBaseChangeMapAb_app_of_forall_isAffine (sq : IsPullback h e f' g)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (r : ℕ)
    (H : ∀ (V X_V T₀ Y₀ : Scheme.{u}) (v : V ⟶ S) (_hv : IsOpenImmersion v) (_hV : IsAffine V)
      (pv : X_V ⟶ X') (fV : X_V ⟶ V) (_hpv : IsPullback pv fV f' v) (t₀ : T₀ ⟶ T)
      (g₀ : T₀ ⟶ V) (_hsq : IsPullback t₀ g₀ g v) (h₀ : Y₀ ⟶ X_V) (e₀ : Y₀ ⟶ T₀)
      (sq₀ : IsPullback h₀ e₀ fV g₀) (_hne : Nonempty T₀),
      IsIso ((higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).app ((smallEtalePullbackAb t₀).obj F))) :
    IsIso ((higherBaseChangeMapAb f' g h e sq.w r).app F) := by
  refine (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun x ↦ ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f' (x.hom (default : Spec (.of x.residueField)))) (U := ⊤) trivial
  have := hU
  let v := U.ι
  let pv := (f' ⁻¹ᵁ U).ι
  let fV := f' ∣_ U
  have hpv : IsPullback pv fV f' v := (isPullback_morphismRestrict f' U).flip
  let t₀ := (g ⁻¹ᵁ U).ι
  let g₀ := g ∣_ U
  have hsq : IsPullback t₀ g₀ g v := (isPullback_morphismRestrict g U).flip
  let h₀ := pullback.fst fV g₀
  let e₀ := pullback.snd fV g₀
  have sq₀ : IsPullback h₀ e₀ fV g₀ := IsPullback.of_hasPullback fV g₀
  have hV : IsIso ((higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).app
      ((smallEtalePullbackAb t₀).obj F)) := by
    by_cases hne : Nonempty (g ⁻¹ᵁ U).toScheme
    · exact H _ _ _ _ v inferInstance hU pv fV hpv t₀ g₀ hsq h₀ e₀ sq₀ hne
    · have : IsEmpty (g ⁻¹ᵁ U).toScheme := not_nonempty_iff.mp hne
      exact isIso_higherBaseChangeMapAb_app_of_isEmpty _ _ _ _ _ _ _
  have hw : (h₀ ≫ pv) ≫ f' = (e₀ ≫ t₀) ≫ g := by
    rw [Category.assoc, Category.assoc, hpv.w, hsq.w, ← Category.assoc, sq₀.w, Category.assoc]
  let pY := sq.lift (h₀ ≫ pv) (e₀ ≫ t₀) hw
  have hpYe : pY ≫ e = e₀ ≫ t₀ := sq.lift_snd _ _ _
  have hout : IsPullback h₀ (pY ≫ e) (pv ≫ f') g := by
    rw [hpYe, hpv.w]
    exact sq₀.paste_vert hsq.flip
  have sq₂ : IsPullback h₀ pY pv h := IsPullback.of_bot hout (sq.lift_fst _ _ _).symm sq
  have hrect : IsIso ((higherBaseChangeMapAb (pv ≫ f') g h₀ (pY ≫ e)
      (smallEtaleRectangle_comm g h h₀ f' pv e pY sq.w sq₂.w) r).app F) := by
    rw [isIso_higherBaseChangeMapAb_app_congr g h₀ hpv.w hpYe _
      (smallEtaleRectangle_comm g g₀ h₀ v fV t₀ e₀ hsq.w.symm sq₀.w),
      higherBaseChangeMapAb_paste_app g g₀ h₀ v fV t₀ e₀ hsq.w.symm sq₀.w r F]
    have := isIso_higherBaseChangeMapAb_app_of_isOpenImmersion hsq.flip r F
    infer_instance
  rw [higherBaseChangeMapAb_paste_app g h h₀ f' pv e pY sq.w sq₂.w r F] at hrect
  have h₂ :=
    isIso_higherBaseChangeMapAb_app_of_isOpenImmersion sq₂ r ((smallEtalePullbackAb e).obj F)
  have : IsIso ((smallEtalePullbackAb pv).map
      ((higherBaseChangeMapAb f' g h e sq.w r).app F)) := isIso_of_isIso_comp_comp hrect
  refine isIso_smallEtaleStalkAb_map_of_isIso_pullbackAb pv x ?_ _
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y default, Scheme.Opens.range_ι]
  exact hxU

end Localization

end Stacks.EtaleCohomology

end
