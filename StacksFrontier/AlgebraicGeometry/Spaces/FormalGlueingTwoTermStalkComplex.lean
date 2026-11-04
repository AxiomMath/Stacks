module

public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafStalkAnyGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionChartBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportVanishing
import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties
import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Formal glueing: the two-term complex of stalks along a closed subspace

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let `Z ⊆ X` be a closed
subspace such that `f^{-1}Z ⟶ Z` is integral and universally injective. Write `V = Y ∖ f^{-1}Z`
and let `j' : V ⟶ Y` be the inclusion. For a geometric point `ȳ` of `Y` with image
`x̄ = f(ȳ)` and an abelian sheaf `G` on the small étale site of `Y`, the map of two-term
complexes
```
((f_*G)_x̄ ⟶ (f_*(j'_*(G|_V)))_x̄) ⟶ (G_ȳ ⟶ (j'_*(G|_V))_ȳ)
```
given by the canonical comparison `(f_*(-))_x̄ ⟶ (-)_ȳ` induces an isomorphism on kernels and
an injection on cokernels. This is **Stacks 0AER**.

## The argument

Both clauses rest on one statement about the comparison `α : (f_*(-))_x̄ ⟶ (-)_ȳ`: it is
invertible at every abelian sheaf supported on `|f^{-1}Z|`, which is
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support_of_isPullback`,
the degree-zero case of Stacks 0AEQ. The horizontal map `φ : G ⟶ j'_*(G|_V)` becomes invertible
after restriction to `V`, so its kernel and its cokernel are supported on `|f^{-1}Z|`.

For the kernels this is immediate: both `f_*(-)_x̄` and `(-)_ȳ` are left exact, so the induced
map of kernels is `α` at `ker φ` read through the two kernel comparisons.

For the cokernels, `α` at `coker φ` is invertible as well, so the induced map of cokernels is a
monomorphism as soon as the cokernel comparison for `f_*(-)_x̄` is one, and that holds as soon
as `f_*(-)_x̄` turns the epimorphism `G ⟶ im φ` into an epimorphism. The kernel of that
epimorphism is again supported on `|f^{-1}Z|`, hence embeds into an *injective* abelian sheaf
`J` supported on `|f^{-1}Z|` — the direct image of an injective resolution step on `f^{-1}Z`.
The cokernel of that embedding is supported on `|f^{-1}Z|` too, so `α` is invertible at both
`J` and that cokernel; since `(-)_ȳ` is exact, `f_*(-)_x̄` therefore turns `J ⟶ coker` into an
epimorphism, and a kernel embedded in an injective object makes the whole square
```
G ⟶ im φ
↓      ↓
J ⟶ coker
```
cartesian, so a left exact functor carries `G ⟶ im φ` to an epimorphism.

## Main definitions

* `AlgebraicGeometry.Space.openComplementPreimageSpace` and
  `AlgebraicGeometry.Space.openComplementPreimageι`: the open complement `V = Y ∖ f^{-1}Z` and
  its inclusion `j' : V ⟶ Y`.
* `AlgebraicGeometry.Space.smallEtaleAbelianRestrictionPushforward` and
  `AlgebraicGeometry.Space.smallEtaleAbelianRestrictionUnit`: the sheaf `j'_*(G|_V)` and the
  canonical map `G ⟶ j'_*(G|_V)`.

## Main results

* `AlgebraicGeometry.Space.isIso_kernelMap_and_mono_cokernelMap_pushforwardStalkMap`
  is **Stacks 0AER**.

## References

* [Stacks Project, Tag 0AER](https://stacks.math.columbia.edu/tag/0AER)
* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u

/-- The map induced on kernels by a natural transformation between two kernel-preserving
functors is invertible as soon as the transformation is invertible at the kernel. -/
private theorem isIso_kernelMap_of_isIso_app_kernel {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] {F G : C ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G) {A A' : C} (f : A ⟶ A')
    [HasKernel f] [HasKernel (F.map f)] [HasKernel (G.map f)]
    [PreservesLimit (parallelPair f 0) F] [PreservesLimit (parallelPair f 0) G]
    [IsIso (α.app (kernel f))] :
    IsIso (kernel.map (F.map f) (G.map f) (α.app A) (α.app A') (α.naturality f)) := by
  have h : kernelComparison f F ≫
      kernel.map (F.map f) (G.map f) (α.app A) (α.app A') (α.naturality f) =
      α.app (kernel f) ≫ kernelComparison f G := by
    apply (cancel_mono (kernel.ι (G.map f))).1
    simp only [Category.assoc, kernel.map, kernel.lift_ι, kernelComparison_comp_ι,
      kernelComparison_comp_ι_assoc]
    exact α.naturality (kernel.ι f)
  have : IsIso (kernelComparison f F ≫
      kernel.map (F.map f) (G.map f) (α.app A) (α.app A') (α.naturality f)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (kernelComparison f F) _

/-- The map induced on cokernels by a natural transformation is a monomorphism as soon as the
cokernel comparison of the source functor is one and the transformation is a monomorphism at
the cokernel. -/
private theorem mono_cokernelMap_of_mono_comparison {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] {F G : C ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G) {A A' : C} (f : A ⟶ A')
    [HasCokernel f] [HasCokernel (F.map f)] [HasCokernel (G.map f)]
    [Mono (cokernelComparison f F)] [Mono (α.app (cokernel f))] :
    Mono (cokernel.map (F.map f) (G.map f) (α.app A) (α.app A') (α.naturality f)) := by
  have h : cokernel.map (F.map f) (G.map f) (α.app A) (α.app A') (α.naturality f) ≫
      cokernelComparison f G = cokernelComparison f F ≫ α.app (cokernel f) := by
    apply (cancel_epi (cokernel.π (F.map f))).1
    simp only [← Category.assoc, cokernel.map, cokernel.π_desc, π_comp_cokernelComparison]
    simpa only [Category.assoc, π_comp_cokernelComparison] using
      (α.naturality (cokernel.π f)).symm
  have : Mono (cokernel.map (F.map f) (G.map f) (α.app A) (α.app A')
      (α.naturality f) ≫ cokernelComparison f G) := by
    rw [h]
    infer_instance
  exact mono_of_mono _ (cokernelComparison f G)

/-- A left exact functor has monomorphic cokernel comparison at a morphism whose
epi-mono factorisation it keeps epimorphic. -/
private theorem mono_cokernelComparison_of_epi_factorThruImage {C : Type u₁} [Category.{v₁} C]
    [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {A A' : C} (f : A ⟶ A') [Epi (F.map (factorThruImage f))] :
    Mono (cokernelComparison f F) := by
  let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hT : T.Exact := T.exact_of_g_is_cokernel (cokernelIsCokernel f)
  let T' := ShortComplex.mk (image.ι f) (cokernel.π f)
    (by rw [← cancel_epi (factorThruImage f), image.fac_assoc, cokernel.condition, comp_zero])
  have hT' : T'.Exact := T'.exact_of_f_is_kernel hT.isLimitImage'
  have hmap : (T'.map F).Exact := hT'.map_of_mono_of_preservesKernel F inferInstance inferInstance
  let φ : T.map F ⟶ T'.map F :=
    { τ₁ := F.map (factorThruImage f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [T, T']
        rw [Category.comp_id, ← F.map_comp, image.fac]
      comm₂₃ := by simp [T, T'] }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hmap).mono_cokernelDesc

/-- **The unit of an adjunction with invertible counit becomes invertible after applying the
left adjoint.** By the triangle identity it is the inverse of the counit there. -/
private theorem isIso_map_unit_of_isIso_counit {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.counit] (A : C) :
    IsIso (L.map (adj.unit.app A)) := by
  rw [IsIso.eq_inv_of_inv_hom_id (adj.left_triangle_components A)]
  infer_instance

/-- An object of the essential image of a monomorphism- and injective-preserving functor
embeds into an injective object of that essential image. -/
private theorem exists_injective_presentation_in_essImage {C : Type u₁} [Category.{v₁} C]
    [EnoughInjectives C] {D : Type u₂} [Category.{v₂} D] (R : C ⥤ D) [R.PreservesMonomorphisms]
    [R.PreservesInjectiveObjects] (P : D) (hP : R.essImage P) :
    ∃ J : D, Injective J ∧ R.essImage J ∧ ∃ e : P ⟶ J, Mono e := by
  obtain ⟨Q, ⟨e⟩⟩ := hP
  obtain ⟨I⟩ := EnoughInjectives.presentation Q
  have := I.injective
  have := I.mono
  exact ⟨R.obj I.J, inferInstance, ⟨I.J, ⟨Iso.refl _⟩⟩, e.inv ≫ R.map I.f, inferInstance⟩

/-- **An epimorphism whose kernel is embedded in an injective object sits in a cartesian
square.** For an epimorphism `p` and a monomorphism `i` of its kernel into an injective object,
`p` and the cokernel projection of `i` are the two legs of a pullback square. -/
private theorem isPullback_of_mono_kernel_lift {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {A A' J : C} (p : A ⟶ A') [Epi p] (i : kernel p ⟶ J) [Mono i] (a : A ⟶ J)
    (ha : kernel.ι p ≫ a = i) :
    IsPullback a p (cokernel.π i)
      (Abelian.epiDesc p (a ≫ cokernel.π i)
        (by rw [← Category.assoc, ha, cokernel.condition])) := by
  let b := Abelian.epiDesc p (a ≫ cokernel.π i)
    (by rw [← Category.assoc, ha, cokernel.condition])
  have w : a ≫ cokernel.π i = p ≫ b := (Abelian.comp_epiDesc _ _ _).symm
  let l := pullback.lift a p w
  have hl₁ : l ≫ pullback.fst _ _ = a := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd _ _ = p := pullback.lift_snd _ _ _
  have : Mono l := Preadditive.mono_of_cancel_zero _ (by
    intro T z hz
    have hzp : z ≫ p = 0 := by rw [← hl₂, ← Category.assoc, hz, zero_comp]
    have hza : z ≫ a = 0 := by rw [← hl₁, ← Category.assoc, hz, zero_comp]
    let k := kernel.lift p z hzp
    have hk : k ≫ i = 0 := by rw [← ha, ← Category.assoc, kernel.lift_ι, hza]
    have hk0 : k = 0 := (cancel_mono i).mp (by simpa using hk)
    simpa only [k, kernel.lift_ι, zero_comp] using congrArg (fun t => t ≫ kernel.ι p) hk0)
  have : Epi l := by
    rw [epi_iff_surjective_up_to_refinements]
    intro T z
    obtain ⟨T', e, he, t, ht⟩ := surjective_up_to_refinements_of_epi p
      (z ≫ pullback.snd (cokernel.π i) b)
    have hw : (e ≫ z ≫ pullback.fst (cokernel.π i) b - t ≫ a) ≫ cokernel.π i = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc z, ← Category.assoc e, ht, Category.assoc t a, w, Category.assoc,
        sub_self]
    let k := Abelian.monoLift i _ hw
    refine ⟨T', e, he, t + k ≫ kernel.ι p, ?_⟩
    apply pullback.hom_ext
    · simp only [Preadditive.add_comp, Category.assoc, hl₁, ha]
      rw [Abelian.monoLift_comp]
      abel
    · simp only [Preadditive.add_comp, Category.assoc, hl₂, kernel.condition, comp_zero,
        add_zero]
      exact ht
  have : IsIso l := isIso_of_mono_of_epi l
  exact IsPullback.of_iso (IsPullback.of_hasPullback (cokernel.π i) b)
    (asIso l).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [← hl₁]) (by simp [← hl₂]) (by simp) (by simp [b])

/-- **A left exact functor keeps an epimorphism epimorphic once it does so for an injective
presentation of its kernel.** -/
private theorem epi_map_of_injective_kernel_embedding {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [PreservesFiniteLimits F]
    {A A' J : C} (p : A ⟶ A') [Epi p] [Injective J] (i : kernel p ⟶ J) [Mono i]
    [Epi (F.map (cokernel.π i))] : Epi (F.map p) :=
  Abelian.epi_snd_of_isLimit _ _ ((isPullback_of_mono_kernel_lift p i
    (Injective.factorThru i (kernel.ι p)) (Injective.comp_factorThru _ _)).map F).isLimit

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The open complement of the inverse image of a closed subspace -/

/-- The open complement `V = Y ∖ f^{-1}Z` of the inverse image of a closed subspace `Z ⊆ X`
along `f : Y ⟶ X`, as an algebraic space over `S`. -/
def openComplementPreimageSpace (f : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1) :
    AlgebraicSpaces B S hS :=
  ⟨(openComplementOfClosedSubspace B S hS Y ⟨Z.1.preimage f.hom,
      isClosedSubspace_preimage B S hS f.hom Z.1 X.property Y.property Z.2⟩).1.toFunctor,
    (openComplementOfClosedSubspace B S hS Y ⟨Z.1.preimage f.hom,
      isClosedSubspace_preimage B S hS f.hom Z.1 X.property Y.property Z.2⟩).2.1⟩

/-- The inclusion `j' : V ⟶ Y` of the open complement `V = Y ∖ f^{-1}Z`. -/
def openComplementPreimageι (f : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1) :
    openComplementPreimageSpace B S hS f Z ⟶ Y :=
  ObjectProperty.homMk (openComplementOfClosedSubspace B S hS Y ⟨Z.1.preimage f.hom,
    isClosedSubspace_preimage B S hS f.hom Z.1 X.property Y.property Z.2⟩).1.ι

/-- The inclusion of the open complement of `f^{-1}Z` is an open immersion. -/
theorem isOpenImmersion_openComplementPreimageι (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    IsOpenImmersion B S hS (openComplementPreimageι B S hS f Z).hom :=
  (openComplementOfClosedSubspace B S hS Y ⟨Z.1.preimage f.hom,
    isClosedSubspace_preimage B S hS f.hom Z.1 X.property Y.property Z.2⟩).2.2

/-- The inclusion of the open complement of `f^{-1}Z` is relatively representable, so that the
direct and inverse images of abelian sheaves along it are available. -/
theorem relativelyRepresentable_openComplementPreimageι (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    yoneda.relativelyRepresentable (openComplementPreimageι B S hS f Z).hom :=
  (isOpenImmersion_openComplementPreimageι B S hS f Z).rep

/-- The points of the open complement of `f^{-1}Z` are exactly the points of `Y` outside
`|f^{-1}Z|`. -/
theorem range_pointsMap_openComplementPreimageι (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) :
    Set.range (pointsMap B S hS (openComplementPreimageSpace B S hS f Z).1
        (openComplementPreimageι B S hS f Z).hom) =
      (Set.range (pointsMap B S hS (Z.1.preimage f.hom).toFunctor
        (Z.1.preimage f.hom).ι))ᶜ :=
  subspacePointSet_openComplement B S hS Y ⟨Z.1.preimage f.hom,
    isClosedSubspace_preimage B S hS f.hom Z.1 X.property Y.property Z.2⟩

/-! ### The two-term complex -/

/-- The direct image `j'_*(G|_V)` along the inclusion of the open complement
`V = Y ∖ f^{-1}Z`, the right-hand term of the two-term complexes of Stacks 0AER. -/
def smallEtaleAbelianRestrictionPushforward (f : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (G : abelianSheaves.{u + 1} B S hS Y) : abelianSheaves.{u + 1} B S hS Y :=
  (smallEtaleAbelianPushforward.{u + 1} B S hS (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)).obj
    ((smallEtaleAbelianInverseImage B S hS (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)).obj G)

/-- The canonical map `G ⟶ j'_*(G|_V)`, the horizontal map of the two-term complexes of
Stacks 0AER: the unit of the adjunction between the inverse image and the direct image of
abelian sheaves along the inclusion `j' : V ⟶ Y` of the open complement of `f^{-1}Z`. -/
def smallEtaleAbelianRestrictionUnit (f : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (G : abelianSheaves.{u + 1} B S hS Y) :
    G ⟶ smallEtaleAbelianRestrictionPushforward B S hS f Z G :=
  (smallEtaleAbelianInverseImageAdjunction B S hS (openComplementPreimageι B S hS f Z)
    (relativelyRepresentable_openComplementPreimageι B S hS f Z)).unit.app G

/-- The canonical map `G ⟶ j'_*(G|_V)` is the unit of the adjunction along `j'`. -/
theorem smallEtaleAbelianRestrictionUnit_eq (f : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (G : abelianSheaves.{u + 1} B S hS Y) :
    smallEtaleAbelianRestrictionUnit B S hS f Z G =
      (smallEtaleAbelianInverseImageAdjunction B S hS (openComplementPreimageι B S hS f Z)
        (relativelyRepresentable_openComplementPreimageι B S hS f Z)).unit.app G :=
  rfl

/-! ### Stacks 0AER -/


variable {Z W V : AlgebraicSpaces B S hS}

/-- The two clauses of Stacks 0AER, for a cartesian square, an open subspace and a map of
abelian sheaves which becomes invertible on that open subspace, all given as data. -/
private theorem isIso_kernelMap_and_mono_cokernelMap_of_isIso_inverseImage (f : Y ⟶ X)
    (hfr : yoneda.relativelyRepresentable f.hom) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom) (hf'inj : UniversallyInjective B S hS f'.hom)
    (sq : IsPullback f' i' i f) (j : V ⟶ Y)
    (hjr : yoneda.relativelyRepresentable j.hom)
    (hcompl : (Set.range (pointsMap B S hS W.1 i'.hom))ᶜ ⊆
      Set.range (pointsMap B S hS V.1 j.hom))
    (y : GeometricPoint B S hS Y.1) (G H : abelianSheaves.{u + 1} B S hS Y) (u : G ⟶ H)
    (hLu : IsIso ((smallEtaleAbelianInverseImage B S hS j hjr).map u)) :
    IsIso (kernel.map
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map u)
        ((smallEtaleAbelianStalk B S hS y).map u)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app G)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app H)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).naturality u)) ∧
      Mono (cokernel.map
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map u)
        ((smallEtaleAbelianStalk B S hS y).map u)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app G)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app H)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).naturality u)) := by
  have hLex : PreservesFiniteLimits (smallEtaleAbelianInverseImage B S hS j hjr) :=
    preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS j hjr
  have hLcol : PreservesColimits (smallEtaleAbelianInverseImage B S hS j hjr) :=
    (smallEtaleAbelianInverseImageAdjunction B S hS j hjr).leftAdjoint_preservesColimits
  have hLadd : (smallEtaleAbelianInverseImage B S hS j hjr).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hFlim : PreservesFiniteLimits (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) :=
    comp_preservesFiniteLimits _ _
  have hFadd : (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).Additive := inferInstance
  -- The comparison is invertible at every abelian sheaf supported on `|W|`.
  have hα : ∀ P : abelianSheaves.{u + 1} B S hS Y,
      supportOfSheaf B S hS Y.1 P ⊆ Set.range (pointsMap B S hS W.1 i'.hom) →
      IsIso ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app P) := fun P hP =>
    isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support_of_isPullback B S hS f hfr i hi
      i' hi' f' hf'int hf'inj sq y P hP
  -- The kernel of a morphism with monic restriction to `V` is supported on `|W|`.
  have hsuppker : ∀ {A A' : abelianSheaves.{u + 1} B S hS Y} (g : A ⟶ A'),
      Mono ((smallEtaleAbelianInverseImage B S hS j hjr).map g) →
      supportOfSheaf B S hS Y.1 (kernel g) ⊆ Set.range (pointsMap B S hS W.1 i'.hom) :=
    fun g _ => supportOfSheaf_subset_of_isZero_smallEtaleAbelianInverseImage B S hS j hjr _
      hcompl _ ((isZero_kernel_of_mono _).of_iso
        (asIso (kernelComparison g (smallEtaleAbelianInverseImage B S hS j hjr))))
  have hLumono : Mono ((smallEtaleAbelianInverseImage B S hS j hjr).map u) := inferInstance
  have hmonoLp : Mono ((smallEtaleAbelianInverseImage B S hS j hjr).map
      (factorThruImage u)) :=
    mono_of_mono_fac (h := (smallEtaleAbelianInverseImage B S hS j hjr).map u)
      (by rw [← Functor.map_comp, image.fac])
  have hsuppC : supportOfSheaf B S hS Y.1 (cokernel u) ⊆
      Set.range (pointsMap B S hS W.1 i'.hom) :=
    supportOfSheaf_subset_of_isZero_smallEtaleAbelianInverseImage B S hS j hjr _ hcompl _
      ((isZero_cokernel_of_epi ((smallEtaleAbelianInverseImage B S hS j hjr).map u)).of_iso
        (asIso (cokernelComparison u (smallEtaleAbelianInverseImage B S hS j hjr))).symm)
  have hαK := hα _ (hsuppker u hLumono)
  have hαC := hα _ hsuppC
  refine ⟨isIso_kernelMap_of_isIso_app_kernel
    (smallEtaleAbelianPushforwardStalkMap B S hS f hfr y) u, ?_⟩
  -- An injective presentation of `ker (G ⟶ im u)` among the sheaves supported on `|W|`.
  have hessKp : (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).essImage
      (kernel (factorThruImage u)) := by
    have hiso := isIso_unit_app_of_supportOfSheaf_subset B S hS i' hi' _
      (hsuppker _ hmonoLp)
    exact ⟨(smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj (kernel (factorThruImage u)),
      ⟨(asIso ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app
        (kernel (factorThruImage u)))).symm⟩⟩
  have hRinj := preservesInjectiveObjects_smallEtaleAbelianPushforward B S hS i' hi'.rep
  obtain ⟨J, hJinj, hJess, e, hemono⟩ := exists_injective_presentation_in_essImage
    (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep) _ hessKp
  have := hJinj
  have := hemono
  have hsuppJ : supportOfSheaf B S hS Y.1 J ⊆ Set.range (pointsMap B S hS W.1 i'.hom) :=
    supportOfSheaf_subset_of_essImage B S hS i' hi' J hJess
  have hlocsurj : Sheaf.IsLocallySurjective (cokernel.π e) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := cokernel.π e)).2 inferInstance
  have hsuppCe : supportOfSheaf B S hS Y.1 (cokernel e) ⊆
      Set.range (pointsMap B S hS W.1 i'.hom) := fun x hx =>
    hsuppJ (supportOfSheaf_subset_of_isLocallySurjective B S hS Y.1 Y.property
      (cokernel.π e) hx)
  have hαJ := hα J hsuppJ
  have hαCe := hα _ hsuppCe
  -- The geometric stalk at `ȳ` is exact, so the comparison transports the epimorphism.
  have hsh : PreservesColimitsOfShape WalkingSpan (smallEtaleAbelianStalk B S hS y) :=
    PreservesFiniteColimits.preservesFiniteColimits _
  have hepiT : Epi ((smallEtaleAbelianStalk B S hS y).map (cokernel.π e)) :=
    preserves_epi_of_preservesColimit _ _
  have hepi1 : Epi ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (cokernel.π e) ≫
        (smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app (cokernel e)) := by
    rw [(smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).naturality (cokernel.π e)]
    infer_instance
  have hepi2 : Epi ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (cokernel.π e)) :=
    (epi_comp_iff_of_isIso _ _).mp hepi1
  have hepiF : Epi ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
      smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map (factorThruImage u)) :=
    epi_map_of_injective_kernel_embedding
      (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) (factorThruImage u) e
  have hmonocc : Mono (cokernelComparison u
      (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y))) :=
    mono_cokernelComparison_of_epi_factorThruImage
      (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)) u
  exact mono_cokernelMap_of_mono_comparison
    (smallEtaleAbelianPushforwardStalkMap B S hS f hfr y) u

/-- **Stacks 0AER.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and
let `Z ⊆ X` be a closed subspace such that `f^{-1}Z ⟶ Z` is integral and universally
injective. Let `ȳ` be a geometric point of `Y`, let `x̄ = f(ȳ)` and let `G` be an abelian sheaf
on the small étale site of `Y`. Writing `V = Y ∖ f^{-1}Z` and `j' : V ⟶ Y` for the inclusion,
the map of two-term complexes
```
((f_*G)_x̄ ⟶ (f_*(j'_*(G|_V)))_x̄) ⟶ (G_ȳ ⟶ (j'_*(G|_V))_ȳ)
```
given by the canonical comparison of
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap` induces an isomorphism on
kernels and an injection on cokernels. -/
@[stacks 0AER "isomorphism on kernels and injection on cokernels of the two-term stalk complexes"]
theorem isIso_kernelMap_and_mono_cokernelMap_pushforwardStalkMap (f : Y ⟶ X)
    (hfr : yoneda.relativelyRepresentable f.hom) (Z : ClosedSubspaces B S hS X.1)
    (hint : IsIntegralHom B S hS (Z.1.fromPreimage f.hom))
    (hinj : UniversallyInjective B S hS (Z.1.fromPreimage f.hom))
    (y : GeometricPoint B S hS Y.1) (G : abelianSheaves.{u + 1} B S hS Y) :
    IsIso (kernel.map
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianStalk B S hS y).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app G)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app
          (smallEtaleAbelianRestrictionPushforward B S hS f Z G))
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).naturality
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))) ∧
      Mono (cokernel.map
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f hfr ⋙
            smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianStalk B S hS y).map
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app G)
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).app
          (smallEtaleAbelianRestrictionPushforward B S hS f Z G))
        ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr y).naturality
          (smallEtaleAbelianRestrictionUnit B S hS f Z G))) := by
  have hWc : IsClosedSubspace B S hS (Z.1.preimage f.hom) :=
    isClosedSubspace_preimage B S hS f.hom Z.1 X.property Y.property Z.2
  have hff := fullyFaithfulSmallEtaleRestrictionOfIsOpenImmersion B S hS
    (openComplementPreimageι B S hS f Z) (isOpenImmersion_openComplementPreimageι B S hS f Z)
    AddCommGrpCat.{u + 1}
  have := hff.full
  have := hff.faithful
  have hcounit : IsIso (smallEtaleAbelianInverseImageAdjunction B S hS
      (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful
      (h := smallEtaleAbelianInverseImageAdjunction B S hS
        (openComplementPreimageι B S hS f Z)
        (relativelyRepresentable_openComplementPreimageι B S hS f Z))
  have hLu : IsIso ((smallEtaleAbelianInverseImage B S hS
      (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)).map
        (smallEtaleAbelianRestrictionUnit B S hS f Z G)) :=
    isIso_map_unit_of_isIso_counit (smallEtaleAbelianInverseImageAdjunction B S hS
      (openComplementPreimageι B S hS f Z)
      (relativelyRepresentable_openComplementPreimageι B S hS f Z)) G
  exact isIso_kernelMap_and_mono_cokernelMap_of_isIso_inverseImage B S hS f hfr
    (ObjectProperty.homMk Z.1.ι :
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) Z.2.2
    (ObjectProperty.homMk (Z.1.preimage f.hom).ι :
      (⟨(Z.1.preimage f.hom).toFunctor, hWc.1⟩ : AlgebraicSpaces B S hS) ⟶ Y) hWc.2
    (ObjectProperty.homMk (Z.1.fromPreimage f.hom) :
      (⟨(Z.1.preimage f.hom).toFunctor, hWc.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) hint hinj
    (IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f.hom Z.1))
    (openComplementPreimageι B S hS f Z)
    (relativelyRepresentable_openComplementPreimageι B S hS f Z)
    (range_pointsMap_openComplementPreimageι B S hS f Z).symm.subset
    y G _ (smallEtaleAbelianRestrictionUnit B S hS f Z G) hLu

end AlgebraicGeometry.Space

end
