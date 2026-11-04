module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ModuleCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# Maps of constructible sheaves of modules on a limit of schemes are detected at a stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms and let `Λ` be a Noetherian ring. Two maps of
constructible sheaves of `Λ`-modules on `(X_i)_étale` whose inverse images to `X_étale` agree
already agree after inverse image to some later stage. This is the faithfulness assertion of
Tag 09YU for module coefficients, the case the source uses for clause (3) of Tag 0GL2.

The argument is the one of the source, run on the support of the image rather than on the
equalizer. The image of the difference of the two maps is constructible, because the
constructible sheaves of `Λ`-modules form a weak Serre subcategory by Tag 03RZ (3) and the image
is the kernel of the projection to a cokernel; its support is therefore constructible by Tag
09YS (3). Inverse image to `X` is exact, so it kills that image, and hence every geometric stalk
of the image above a point in the image of `X` vanishes: the support misses the image of `X`. By
Tag 05F4 it then misses the image of a sufficiently late stage, where Tag 03PU turns the
vanishing of all geometric stalks into the vanishing of the inverse image of the image sheaf, so
the inverse image of the difference factors through a zero object.

## Main results

* `AlgebraicGeometry.isZero_of_forall_isZero_etaleStalk_module` — a sheaf of `Λ`-modules on a
  small étale site all of whose geometric stalks vanish is zero, the vanishing case of Tag 03PU
  for module coefficients.
* `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleModuleSheaf` — **Tag 09YU, clause
  (3), the faithfulness assertion.**

## Implementation notes

The coefficient universe is fixed to `ModuleCat.{u + 1} Λ` with `Λ : Type (u + 1)`, which is the
universe at which Tag 03PU for module coefficients
(`AlgebraicGeometry.isLocallySurjective_of_surjective_etaleStalkMap_module`) is available. Tag
03RZ (3), Tag 09YS (3) and the exactness of inverse image are all stated at coefficient
universes built from a free parameter, and instance search cannot specialise those `max`
expressions by itself; the ambient instances they need are therefore named at the fixed
coefficient universe and the results themselves are applied with their universes given
explicitly. This is the same device as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SpecializationClosedSupportColimit`.

The two ambient conditions appearing in the signature of
`AlgebraicGeometry.IsConstructibleModuleSheaf` — that direct image between small étale sites is
a right adjoint, and that presheaves of modules on a slice can be weakly sheafified — hold at
this coefficient universe, and the main statement needs no binder for either: they are the
instances `AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCatSelf` and
`AlgebraicGeometry.SmallEtale.hasWeakSheafifyOver_moduleCatSelf`, the specialisations to
`ModuleCat.{u + 1} Λ` of the generic statements at `ModuleCat.{max (u + 1) w} Λ`.

Only the faithfulness assertion of Tag 09YU is proved. Its fullness and essential surjectivity
assertions need the identification of the sections of a colimit of sheaves on an inverse system
of sites at module coefficients, which the library has only for sheaves of sets, so neither is
available here.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

section Image

/-- A functor that kills the image of a morphism kills the morphism. -/
private theorem map_eq_zero_of_isZero_obj_abelianImage {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (T : C ⥤ D) {F G : C} (φ : F ⟶ G)
    (h : IsZero (T.obj (Abelian.image φ))) : T.map φ = 0 := by
  rw [← Abelian.image.fac φ, Functor.map_comp, h.eq_zero_of_src (T.map (Abelian.image.ι φ)),
    comp_zero]

/-- **An exact functor kills the image of a morphism it kills.** The functor carries the
epimorphism onto and the monomorphism out of the image to an epimorphism and a monomorphism whose
composite is the image of the morphism, so the monomorphism out of the image of the image is
zero. -/
private theorem isZero_obj_abelianImage_of_map_eq_zero {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (T : C ⥤ D) [T.PreservesMonomorphisms] [T.PreservesEpimorphisms]
    {F G : C} (φ : F ⟶ G) (h : T.map φ = 0) :
    IsZero (T.obj (Abelian.image φ)) := by
  have hmono : Mono (T.map (Abelian.image.ι φ)) := T.map_mono _
  have hepi : Epi (T.map (Abelian.factorThruImage φ)) := T.map_epi _
  have hcomp : T.map (Abelian.factorThruImage φ) ≫ T.map (Abelian.image.ι φ) = 0 := by
    rw [← T.map_comp, Abelian.image.fac, h]
  have hz : T.map (Abelian.image.ι φ) = 0 := zero_of_epi_comp _ hcomp
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← cancel_mono (T.map (Abelian.image.ι φ)), Category.id_comp, hz, zero_comp]

end Image

section Coefficients

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- Sheafification of presheaves of `Λ`-modules on the small étale site inverts exactly the
locally bijective morphisms, at the coefficient universe `u + 1`. This is what turns local
surjectivity of a map of sheaves of modules into an epimorphism. -/
private instance smallEtaleWEqualsLocallyBijectiveSelf_moduleCat (S : Scheme.{u})
    (hS : B.Contains S) :
    (SmallEtale.topology B S hS).WEqualsLocallyBijective (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, u + 1}
    (SmallEtale.topology B S hS) Λ

/-- **Stacks 03PU for sheaves of modules, the vanishing case.** A sheaf of `Λ`-modules on the
small étale site of `S` whose stalk at every geometric point of `S` vanishes is zero.

The zero map from the zero sheaf is surjective on every geometric stalk, the target of each of
those maps being a zero module, so it is locally surjective by Tag 03PU and therefore an
epimorphism; an epimorphism out of a zero object forces the identity of its target to
vanish. -/
@[stacks 03PU "module coefficients, the vanishing case of the isomorphism criterion: a sheaf of \
modules whose geometric stalks all vanish is zero"]
public theorem isZero_of_forall_isZero_etaleStalk_module (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ))
    (h : ∀ t : GeometricPoint S, IsZero (etaleStalk B S hS t F.obj)) :
    IsZero F := by
  have hsurj : ∀ t : GeometricPoint S, Function.Surjective
      ((etaleStalkPresheafFunctor B S hS t (ModuleCat.{u + 1} Λ)).map
        (0 : (0 : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)) ⟶ F).hom) := by
    intro t y
    have hsub : Subsingleton
        ((etaleStalkPresheafFunctor B S hS t (ModuleCat.{u + 1} Λ)).obj F.obj) :=
      ModuleCat.subsingleton_of_isZero (h t)
    exact ⟨0, hsub.elim _ _⟩
  have hls := isLocallySurjective_of_surjective_etaleStalkMap_module B Λ S hS
    (0 : (0 : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)) ⟶ F) hsurj
  have hepi : Epi (0 : (0 : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)) ⟶ F) := by
    have := hls
    infer_instance
  refine (IsZero.iff_id_eq_zero F).2 ?_
  refine (cancel_epi (0 : (0 : Sheaf (SmallEtale.topology B S hS)
    (ModuleCat.{u + 1} Λ)) ⟶ F)).mp ?_
  rw [comp_zero, Category.comp_id]

end Coefficients

section Descent

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Stacks 09YU, clause (3), the faithfulness assertion.** Let `X = lim X_i` be the limit of a
directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms and let `Λ` be a Noetherian ring. Two maps of constructible sheaves of `Λ`-modules on
`(X_i)_étale` whose inverse images to `X_étale` agree agree after inverse image to some later
stage.

The image of the difference of the two maps is constructible by Tag 03RZ (3), so its support is
constructible by Tag 09YS (3); inverse image to `X` is exact and kills the difference, hence the
image, so by Tag 03Q1 that support misses the image of `X` and by Tag 05F4 the image of a later
stage, where Tag 03PU makes the inverse image of the image sheaf zero. -/
@[stacks 09YU "clause (3), the faithfulness assertion"]
public theorem smallEtaleStagesFaithful_isConstructibleModuleSheaf (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) := by
  intro i F G hF hG a b hab
  have : Nonempty I := ⟨i⟩
  have : CompactSpace (Dg.obj (op i)).obj := hqc i
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  have hAB : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have hprod : HasProducts.{u} (ModuleCat.{u + 1} Λ) := fun _ => ModuleCat.hasLimitsOfShape
  -- inverse image to the vertex is exact and additive
  have hprojFL : PreservesFiniteLimits
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i) :=
    preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  have : PreservesLimitsOfShape WalkingCospan
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i) :=
    hprojFL.preservesFiniteLimits _
  have hprojFC : PreservesFiniteColimits
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i) :=
    preservesFiniteColimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  have : PreservesColimitsOfShape WalkingSpan
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i) :=
    hprojFC.preservesFiniteColimits _
  have hprojAdd : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).Additive :=
    additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  -- the image of the difference is constructible
  let P : ObjectProperty (Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) (ModuleCat.{u + 1} Λ)) :=
    fun H => IsConstructibleModuleSheaf B (Dg.obj (op i)) Λ H
  let _ : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B _ Λ
  have hE : P (Abelian.image (a - b)) :=
    P.prop_kernel (cokernel.π (a - b)) hG (P.prop_cokernel (a - b) hF hG)
  -- its support is constructible and misses the image of the vertex
  set L : Set (Dg.obj (op i)).obj :=
    {x | ∃ t : GeometricPoint (Dg.obj (op i)).obj, t.LiesOver x ∧
      ¬ IsZero (etaleStalk B (Dg.obj (op i)).obj (Dg.obj (op i)).property t
        (Abelian.image (a - b)).obj)} with hLdef
  have hLc : Topology.IsConstructible L :=
    isConstructible_support_moduleSheaf.{u + 1, u, u + 1} B (Dg.obj (op i)) Λ _ hE
  set p : B.obj c.pt hX ⟶ Dg.obj (op i) := ObjectProperty.homMk (c.π.app (op i)) with hp
  have hpi : B.inclusion.map p = c.π.app (op i) := rfl
  have hzeroproj : IsZero ((smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj
      (Abelian.image (a - b))) := by
    refine isZero_obj_abelianImage_of_map_eq_zero _ (a - b) ?_
    rw [Functor.map_sub, hab, sub_self]
  have hlim : Set.range ⇑(c.π.app (op i)) ⊆ Lᶜ := by
    rintro y ⟨y', rfl⟩ ⟨t, htz, hnt⟩
    refine hnt ?_
    have hbase : ((GeometricPoint.ofPoint c.pt y').map (B.inclusion.map p)).hom default =
        t.hom default := by
      refine Eq.trans ?_ htz.symm
      simp only [GeometricPoint.map_hom, hpi]
      simp
    refine IsZero.of_iso ?_ ((etaleStalkPresheafFunctorIsoOfEqBase B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property hbase (ModuleCat.{u + 1} Λ)).app
        (Abelian.image (a - b)).obj).symm
    refine IsZero.of_iso (Functor.map_isZero
      ((geometricPointSitePoint B c.pt hX (GeometricPoint.ofPoint c.pt y')).sheafFiber
        (A := ModuleCat.{u + 1} Λ)) hzeroproj) ?_
    exact (etaleStalkSmallEtalePullObjIso B p (GeometricPoint.ofPoint c.pt y')
      (ModuleCat.{u + 1} Λ) (Abelian.image (a - b))).symm
  -- so it misses the image of a later stage
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (eventually_range_transition_subset_of_isLocallyConstructible
      (descentSituationOfBigEtaleCone B Dg c hc haff hqc hqs i) Lᶜ
      hLc.compl.isLocallyConstructible hlim)
  obtain ⟨j, hij, hj₀j⟩ := directed_of (· ≤ ·) i j₀
  obtain ⟨hbj, hsub⟩ := hj₀ j hj₀j
  refine ⟨j, hij, ?_⟩
  -- at that stage the inverse image of the image sheaf is zero
  have hzE : IsZero ((smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hij).obj
      (Abelian.image (a - b))) := by
    refine isZero_of_forall_isZero_etaleStalk_module B Λ (Dg.obj (op j)).obj
      (Dg.obj (op j)).property _ fun s => ?_
    have hmem : (B.inclusion.map (Dg.map (homOfLE hij).op)).base (s.hom.base default) ∈ Lᶜ :=
      hsub ⟨s.hom.base default, rfl⟩
    have ht : IsZero (etaleStalk B (Dg.obj (op i)).obj (Dg.obj (op i)).property
        (s.map (B.inclusion.map (Dg.map (homOfLE hij).op)))
        (Abelian.image (a - b)).obj) := by
      by_contra hne
      refine hmem ⟨s.map (B.inclusion.map (Dg.map (homOfLE hij).op)), ?_, hne⟩
      simp only [GeometricPoint.LiesOver, GeometricPoint.map_hom]
      simp
    exact IsZero.of_iso ht (etaleStalkSmallEtalePullObjIso B
      (Dg.map (homOfLE hij).op) s (ModuleCat.{u + 1} Λ) (Abelian.image (a - b)))
  have htrAdd : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hij).Additive :=
    additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  have hφ := map_eq_zero_of_isZero_obj_abelianImage _ (a - b) hzE
  rwa [Functor.map_sub, sub_eq_zero] at hφ

end Descent

end AlgebraicGeometry

end
