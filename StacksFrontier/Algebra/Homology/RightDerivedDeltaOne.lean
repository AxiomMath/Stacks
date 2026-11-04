module

public import Mathlib.Algebra.Homology.Refinements
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge

/-!
# The degree-one connecting morphism of a right derived functor

Let `Q : B ⥤ D` be an additive functor between abelian categories, with `B` having enough
injectives, and let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence in `B`.  There is then a
canonical morphism

  `Q X₃ ⟶ R¹Q X₁`,

the degree-one connecting morphism of the long exact sequence of the right derived functors of
`Q`.  Mathlib has the long exact sequence of right derived functors in the *functor* variable
(for a short exact sequence of functors which is exact on injectives, see
`StacksFrontier/Algebra/Homology/DerivedFunctorLongExact.lean`), but not in the *object* variable,
which is what is needed here.

## Construction

No horseshoe lemma is involved.  Let `J` be the chosen injective resolution of `X₁` and write
`C = coker (X₁ ⟶ J⁰)`.  Since `X₁ ⟶ X₂` is a monomorphism and `J⁰` is injective, the
augmentation extends to a morphism `r : X₂ ⟶ J⁰`; composing with `J⁰ ⟶ C` kills `X₁`, hence
descends along `X₂ ⟶ X₃` to a morphism `X₃ ⟶ C`.  Applying `Q` and following with the class map
`Q C ⟶ H¹(Q J) = R¹Q X₁` gives the connecting morphism.  The construction visibly depends on the
choice of `r`, but the class map kills the image of `Q J⁰`, and two choices of `r` differ by a
morphism factoring through `J⁰`, so the result does not.

## Main definitions

* `Stacks.Cohomology.RightDerivedDeltaOne.coaugClass`: for a morphism `a : Z ⟶ K⁰` killed by the
  first differential of a cochain complex `K`, the class map `Q (coker a) ⟶ H¹(Q K)`.
* `Stacks.Cohomology.RightDerivedDeltaOne.deltaOne`: the connecting morphism
  `Q X₃ ⟶ R¹Q X₁`.

## Main results

* `Stacks.Cohomology.RightDerivedDeltaOne.exact_coaugClass`: when `Q` is left exact and
  `0 ⟶ Z ⟶ K⁰ ⟶ K¹` is exact, the class map `Q (coker a) ⟶ H¹(Q K)` has as its image exactly the
  kernel of the comparison `H¹(Q K) ⟶ Q (H¹ K)`.
* `Stacks.Cohomology.RightDerivedDeltaOne.exact_map_g_deltaOne` and
  `Stacks.Cohomology.RightDerivedDeltaOne.epi_deltaOne`: the piece
  `Q X₂ ⟶ Q X₃ ⟶ R¹Q X₁ ⟶ 0` of the long exact sequence, when `X₂` is injective and `Q` is left
  exact.  Both hypotheses are artefacts of the construction above rather than of the statement:
  the retraction `J⁰ ⟶ X₂` it chases through exists because `X₂` is injective, and the
  identification of `Q (coker (X₁ ⟶ J⁰))` with `Z¹(Q J)` needs `Q` to preserve kernels.  In the
  intended application `X₂` is a term of a complex of injectives and `Q` is `Γ(Y, -)`.
* `Stacks.Cohomology.RightDerivedDeltaOne.deltaOne_comp_edge_app_one`: the connecting morphism of
  `0 ⟶ P X ⟶ (P I)⁰ ⟶ coker ⟶ 0`, followed by the degree-one edge morphism of the composite
  `Q ∘ P`, is the class map of that same cokernel.
* `Stacks.Cohomology.RightDerivedDeltaOne.exact_edge_secondEdge`: **the five-term exact sequence
  of a composite of right derived functors is exact in the middle**, i.e.
  `R¹Q (P X) ⟶ R¹(Q ∘ P) X ⟶ Q (R¹P X)` is exact.  This is the last of the three exactness
  statements of [Stacks, Tag 01F2] in low degrees.  Only `deltaOne_comp_edge_app_one` and
  `exact_coaugClass` enter its proof: the class map factors through the edge morphism, so their
  images agree without any surjectivity statement.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedDeltaOne

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

/-- **Exactness transfers along a factorisation of the first map.**  If `U ⟶ V ⟶ W` is exact and
the morphism `U ⟶ V` factors through `f : W' ⟶ V`, which is itself killed by `g : V ⟶ W`, then
`W' ⟶ V ⟶ W` is exact: the image of `f` contains the image of `U ⟶ V`, hence the kernel of `g`,
and is contained in it because `f ≫ g = 0`. -/
theorem exact_of_factor_of_exact {U V W W' : D} {f : W' ⟶ V} {g : V ⟶ W} (hfg : f ≫ g = 0)
    {ε : U ⟶ V} (δ : U ⟶ W') (hδ : δ ≫ f = ε) (hεg : ε ≫ g = 0)
    (h : (ShortComplex.mk ε g hεg).Exact) :
    (ShortComplex.mk f g hfg).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  obtain ⟨T', π, hπ, y, hy⟩ := h.exact_up_to_refinements x hx
  have hyδ : (y ≫ δ) ≫ f = y ≫ ε := by rw [assoc, hδ]
  exact ⟨T', π, hπ, y ≫ δ, hy.trans hyδ.symm⟩

section Coaug

variable (Q : B ⥤ D) [Q.Additive] {Z : B} {K : CochainComplex B ℕ} (a : Z ⟶ K.X 0)
  (ha : a ≫ K.d 0 1 = 0)

/-- The morphism `coker a ⟶ K¹` induced by the first differential of `K`, for `a : Z ⟶ K⁰` a
morphism killed by that differential. -/
def coaugToOne : cokernel a ⟶ K.X 1 :=
  cokernel.desc a (K.d 0 1) ha

/-- The projection onto `coker a` followed by `coaugToOne a ha` is the differential `K⁰ ⟶ K¹`. -/
@[reassoc (attr := simp)]
theorem π_comp_coaugToOne : cokernel.π a ≫ coaugToOne a ha = K.d 0 1 :=
  cokernel.π_desc _ _ _

/-- The morphism `coker a ⟶ K¹` is killed by the second differential of `K`. -/
@[reassoc]
theorem coaugToOne_comp_d : coaugToOne a ha ≫ K.d 1 2 = 0 := by
  rw [← cancel_epi (cokernel.π a), comp_zero, π_comp_coaugToOne_assoc, K.d_comp_d]

/-- `coker a`, viewed as a cycle of `K` in degree one. -/
def cyclesOfCoaug : cokernel a ⟶ K.cycles 1 :=
  K.liftCycles (coaugToOne a ha) 2 (by simp) (coaugToOne_comp_d a ha)

/-- The morphism `coker a ⟶ Z¹ K` followed by the inclusion of cycles is `coaugToOne a ha`. -/
@[reassoc (attr := simp)]
theorem cyclesOfCoaug_i : cyclesOfCoaug a ha ≫ K.iCycles 1 = coaugToOne a ha :=
  K.liftCycles_i _ _ _ _

/-- The projection onto `coker a` followed by `cyclesOfCoaug a ha` is the map `K⁰ ⟶ Z¹ K`
induced by the first differential. -/
@[reassoc]
theorem π_comp_cyclesOfCoaug : cokernel.π a ≫ cyclesOfCoaug a ha = K.toCycles 0 1 := by
  rw [← cancel_mono (K.iCycles 1), assoc, cyclesOfCoaug_i, π_comp_coaugToOne,
    HomologicalComplex.toCycles_i]

/-- The cycles of `K` coming from `coker a` vanish in `H¹ K`. -/
@[reassoc]
theorem cyclesOfCoaug_comp_homologyπ : cyclesOfCoaug a ha ≫ K.homologyπ 1 = 0 := by
  rw [← cancel_epi (cokernel.π a), comp_zero, π_comp_cyclesOfCoaug_assoc,
    HomologicalComplex.toCycles_comp_homologyπ]

/-- **The class map `Q (coker a) ⟶ H¹(Q K)`**: `Q` applied to `coker a ⟶ Z¹ K`, read through the
comparison of cycles, followed by the projection onto homology.  No exactness hypothesis on `a` or
on `Q` is needed to define it. -/
def coaugClass : Q.obj (cokernel a) ⟶
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 1 :=
  Q.map (cyclesOfCoaug a ha) ≫ RightDerivedCoEdge.mapCycles Q K 1 ≫
    HomologicalComplex.homologyπ _ 1

/-- The defining formula for the class map. -/
theorem coaugClass_eq : coaugClass Q a ha = Q.map (cyclesOfCoaug a ha) ≫
    RightDerivedCoEdge.mapCycles Q K 1 ≫ HomologicalComplex.homologyπ _ 1 :=
  rfl

/-- The comparison `Q (coker a) ⟶ Z¹ (Q K)` carries the image of `Q K⁰` onto the boundaries. -/
@[reassoc]
theorem map_π_comp_cyclesOfCoaug_comp_mapCycles :
    Q.map (cokernel.π a) ≫ Q.map (cyclesOfCoaug a ha) ≫ RightDerivedCoEdge.mapCycles Q K 1 =
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).toCycles 0 1 := by
  rw [← cancel_mono (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles 1), assoc,
    assoc, RightDerivedCoEdge.mapCycles_i, HomologicalComplex.toCycles_i, ← Q.map_comp,
    ← Q.map_comp, cyclesOfCoaug_i, π_comp_coaugToOne]
  rfl

/-- The class map kills the image of `Q K⁰`. -/
@[reassoc]
theorem map_π_comp_coaugClass :
    Q.map (cokernel.π a) ≫ coaugClass Q a ha = 0 := by
  rw [coaugClass_eq, RightDerivedCoEdge.comp_comp_comp_eq _ _ _ _ _
      (map_π_comp_cyclesOfCoaug_comp_mapCycles Q a ha),
    HomologicalComplex.toCycles_comp_homologyπ]

section LeftExact

variable [PreservesFiniteLimits Q]

/-- The class map is killed by the comparison `H¹(Q K) ⟶ Q (H¹ K)`, because `coker a ⟶ Z¹ K` is
killed by the projection onto `H¹ K`. -/
@[reassoc]
theorem coaugClass_comp_homologyToMapHomology :
    coaugClass Q a ha ≫ RightDerivedCoEdge.homologyToMapHomology Q K 1 = 0 := by
  rw [coaugClass_eq, assoc, assoc,
    RightDerivedCoEdge.mapCycles_comp_homologyπ_comp_homologyToMapHomology, ← Q.map_comp,
    cyclesOfCoaug_comp_homologyπ, Q.map_zero]

end LeftExact

end Coaug

section CoaugExact

variable (Q : B ⥤ D) [Q.Additive] {Z : B} {K : CochainComplex B ℕ} (a : Z ⟶ K.X 0)
  (ha : a ≫ K.d 0 1 = 0) [Mono a] (hex : (ShortComplex.mk a (K.d 0 1) ha).Exact)

include hex in
/-- **`coker a ⟶ K¹` is a monomorphism** when `0 ⟶ Z ⟶ K⁰ ⟶ K¹` is exact: the quotient of `K⁰`
by the kernel of the first differential injects into `K¹`. -/
theorem mono_coaugToOne : Mono (coaugToOne a ha) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T t ht
  obtain ⟨T', π, hπ, p, hp⟩ := surjective_up_to_refinements_of_epi (cokernel.π a) t
  have : Mono (ShortComplex.mk a (K.d 0 1) ha).f := ‹Mono a›
  have h0 : p ≫ (ShortComplex.mk a (K.d 0 1) ha).g = 0 := by
    show p ≫ K.d 0 1 = 0
    rw [← π_comp_coaugToOne a ha, ← assoc, ← hp, assoc, ht, comp_zero]
  obtain ⟨u, hu⟩ := hex.lift' p h0
  refine zero_of_epi_comp π ?_
  rw [hp, ← hu]
  show (u ≫ a) ≫ cokernel.π a = 0
  rw [assoc, cokernel.condition, comp_zero]

include hex in
/-- `coker a ⟶ Z¹ K` is a monomorphism. -/
theorem mono_cyclesOfCoaug : Mono (cyclesOfCoaug a ha) := by
  have : Mono (cyclesOfCoaug a ha ≫ K.iCycles 1) := by
    rw [cyclesOfCoaug_i]
    exact mono_coaugToOne a ha hex
  exact mono_of_mono _ (K.iCycles 1)

include hex in
/-- **`0 ⟶ coker a ⟶ Z¹ K ⟶ H¹ K ⟶ 0` is short exact.**  The cokernel of `a` is the group of
boundaries of `K` in degree one, and the homology is the cycles modulo the boundaries. -/
theorem shortExact_cyclesOfCoaug :
    (ShortComplex.mk (cyclesOfCoaug a ha) (K.homologyπ 1)
      (cyclesOfCoaug_comp_homologyπ a ha)).ShortExact where
  exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    obtain ⟨T', π, hπ, x₁, hx₁⟩ :=
      (K.comp_homologyπ_eq_zero_iff_up_to_refinements 0 1 (by simp) x).1 hx
    refine ⟨T', π, hπ, x₁ ≫ cokernel.π a, ?_⟩
    show π ≫ x = (x₁ ≫ cokernel.π a) ≫ cyclesOfCoaug a ha
    rw [hx₁, assoc, π_comp_cyclesOfCoaug]
  mono_f := mono_cyclesOfCoaug a ha hex
  epi_g := inferInstance

variable [PreservesFiniteLimits Q]

include hex in
/-- **The image of the class map is exactly the kernel of the comparison
`H¹(Q K) ⟶ Q (H¹ K)`** when `Q` is left exact and `0 ⟶ Z ⟶ K⁰ ⟶ K¹` is exact.  A class of
`H¹(Q K)` killed by the comparison is, after a refinement, a cycle whose image in `Q (Z¹ K)` lies
in `Q (coker a)`, because `Q` preserves the kernel of `Z¹ K ⟶ H¹ K`. -/
theorem exact_coaugClass :
    (ShortComplex.mk (coaugClass Q a ha)
      (RightDerivedCoEdge.homologyToMapHomology Q K 1)
      (coaugClass_comp_homologyToMapHomology Q a ha)).Exact := by
  have hSE := shortExact_cyclesOfCoaug a ha hex
  have hmono : Mono (Q.map (cyclesOfCoaug a ha)) :=
    mono_of_isLimit_fork (KernelFork.mapIsLimit _ hSE.fIsKernel Q)
  have hmapExact := hSE.exact.map_of_mono_of_preservesKernel Q hSE.mono_f inferInstance
  have : Mono ((ShortComplex.mk (cyclesOfCoaug a ha) (K.homologyπ 1)
      (cyclesOfCoaug_comp_homologyπ a ha)).map Q).f := hmono
  have h2 : (ComplexShape.up ℕ).next 1 = 2 := by simp
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  obtain ⟨T₁, π₁, hπ₁, z, hz, hfac⟩ :=
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      K).eq_liftCycles_homologyπ_up_to_refinements x 2 h2
  have hxz : x ≫ RightDerivedCoEdge.homologyToMapHomology Q K 1 = 0 := hx
  have hw : (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).liftCycles z 2 h2 hz ≫
      (RightDerivedCoEdge.mapCyclesIso Q K 1).inv) ≫ Q.map (K.homologyπ 1) = 0 := by
    rw [assoc, ← RightDerivedCoEdge.homologyπ_comp_homologyToMapHomology, ← assoc, ← hfac, assoc,
      hxz, comp_zero]
  obtain ⟨v, hv⟩ := hmapExact.lift' _ hw
  have hv' : v ≫ Q.map (cyclesOfCoaug a ha) =
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).liftCycles z 2 h2 hz ≫
        (RightDerivedCoEdge.mapCyclesIso Q K 1).inv := hv
  have key : v ≫ coaugClass Q a ha =
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).liftCycles z 2 h2 hz ≫
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ 1 := by
    rw [coaugClass_eq, ← assoc, hv', assoc, ← RightDerivedCoEdge.mapCyclesIso_hom,
      Iso.inv_hom_id_assoc]
  exact ⟨T₁, π₁, hπ₁, v, hfac.trans key.symm⟩

/-- The augmentation of an injective resolution is a monomorphism: it is the kernel of the first
differential of the resolution. -/
theorem mono_augOf {W : B} (J : InjectiveResolution W) :
    Mono (RightDerivedCoEdge.augOf J) :=
  mono_of_isLimit_fork J.isLimitKernelFork

/-- **`coker (W ⟶ J⁰) ⟶ Z¹ J` is an isomorphism** for an injective resolution `J` of `W`: the
sequence `0 ⟶ coker ⟶ Z¹ J ⟶ H¹ J ⟶ 0` is short exact and `J` has no first homology. -/
theorem isIso_cyclesOfCoaug_augOf {W : B} (J : InjectiveResolution W) :
    IsIso (cyclesOfCoaug (RightDerivedCoEdge.augOf J) (RightDerivedCoEdge.augOf_comp_d J)) :=
  have := mono_augOf J
  (shortExact_cyclesOfCoaug _ _ (RightDerivedCoEdge.exact_augOf J)).isIso_f_iff.2
    (RightDerivedCoEdge.isZero_homology_succ J 0)

/-- **The class map of the augmentation of an injective resolution is an epimorphism** when `Q` is
left exact: the comparison `coker (W ⟶ J⁰) ⟶ Z¹ J` is an isomorphism, `Q` preserves cycles, and
the projection onto homology is an epimorphism. -/
theorem epi_coaugClass_augOf (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q] {W : B}
    (J : InjectiveResolution W) :
    Epi (coaugClass Q (RightDerivedCoEdge.augOf J) (RightDerivedCoEdge.augOf_comp_d J)) := by
  have := isIso_cyclesOfCoaug_augOf J
  rw [coaugClass_eq]
  infer_instance

end CoaugExact

section DeltaOne

variable (Q : B ⥤ D) [Q.Additive] {S : ShortComplex B} (hS : S.ShortExact)

/-- The extension of the augmentation of an injective resolution of `S.X₁` over the monomorphism
`S.f`, which exists because the degree-zero term of the resolution is injective. -/
def liftToResolution (J : InjectiveResolution S.X₁) : S.X₂ ⟶ J.cocomplex.X 0 :=
  haveI := hS.mono_f
  Injective.factorThru (RightDerivedCoEdge.augOf J) S.f

/-- The morphism `liftToResolution hS J` extends the augmentation `S.X₁ ⟶ J⁰` along `S.f`. -/
@[reassoc]
theorem f_comp_liftToResolution (J : InjectiveResolution S.X₁) :
    S.f ≫ liftToResolution hS J = RightDerivedCoEdge.augOf J :=
  have := hS.mono_f
  Injective.comp_factorThru _ _

/-- The composite `S.X₁ ⟶ S.X₂ ⟶ J⁰ ⟶ coker (S.X₁ ⟶ J⁰)` is zero. -/
theorem f_comp_liftToResolution_comp_π (J : InjectiveResolution S.X₁) :
    S.f ≫ liftToResolution hS J ≫ cokernel.π (RightDerivedCoEdge.augOf J) = 0 := by
  rw [f_comp_liftToResolution_assoc, cokernel.condition]

/-- The morphism `S.X₃ ⟶ coker (S.X₁ ⟶ J⁰)` obtained from `liftToResolution` by descending along
`S.g`, which is possible because the composite kills `S.X₁`. -/
def connecting (J : InjectiveResolution S.X₁) :
    S.X₃ ⟶ cokernel (RightDerivedCoEdge.augOf J) :=
  haveI := hS.epi_g
  hS.exact.desc (liftToResolution hS J ≫ cokernel.π (RightDerivedCoEdge.augOf J))
    (f_comp_liftToResolution_comp_π hS J)

/-- The morphism `S.g` followed by `connecting hS J` is `liftToResolution hS J` followed by the
projection onto `coker (S.X₁ ⟶ J⁰)`. -/
@[reassoc]
theorem g_comp_connecting (J : InjectiveResolution S.X₁) :
    S.g ≫ connecting hS J =
      liftToResolution hS J ≫ cokernel.π (RightDerivedCoEdge.augOf J) :=
  have := hS.epi_g
  hS.exact.g_desc _ _

variable [HasInjectiveResolutions B]

/-- **The degree-one connecting morphism `Q X₃ ⟶ R¹Q X₁`** of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, for an additive functor `Q`.  It is `Q` applied to the comparison
`X₃ ⟶ coker (X₁ ⟶ J⁰)` with the chosen injective resolution `J` of `X₁`, followed by the class
map into `H¹(Q J) = R¹Q X₁`. -/
def deltaOne : Q.obj S.X₃ ⟶ (Q.rightDerived 1).obj S.X₁ :=
  Q.map (connecting hS (injectiveResolution S.X₁)) ≫
    coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution S.X₁))
        (RightDerivedCoEdge.augOf_comp_d _) ≫
      ((injectiveResolution S.X₁).isoRightDerivedObj' Q 1).inv

/-- The defining formula for `deltaOne`. -/
theorem deltaOne_eq :
    deltaOne Q hS = Q.map (connecting hS (injectiveResolution S.X₁)) ≫
      coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution S.X₁))
          (RightDerivedCoEdge.augOf_comp_d _) ≫
        ((injectiveResolution S.X₁).isoRightDerivedObj' Q 1).inv :=
  rfl

end DeltaOne

section Epi

/-- The retraction `J⁰ ⟶ S.X₂` of the augmentation of an injective resolution `J` of `S.X₁`
through the monomorphism `S.f`, which exists because `S.X₂` is injective. -/
def resolutionToX₂ (S : ShortComplex B) [Injective S.X₂] (J : InjectiveResolution S.X₁) :
    J.cocomplex.X 0 ⟶ S.X₂ :=
  haveI := mono_augOf J
  Injective.factorThru S.f (RightDerivedCoEdge.augOf J)

/-- The augmentation `S.X₁ ⟶ J⁰` followed by `resolutionToX₂ S J` is `S.f`. -/
@[reassoc]
theorem augOf_comp_resolutionToX₂ (S : ShortComplex B) [Injective S.X₂]
    (J : InjectiveResolution S.X₁) :
    RightDerivedCoEdge.augOf J ≫ resolutionToX₂ S J = S.f :=
  have := mono_augOf J
  Injective.comp_factorThru _ _

/-- The morphism `coker (S.X₁ ⟶ J⁰) ⟶ S.X₃` descended from `resolutionToX₂`. -/
def coaugToX₃ (S : ShortComplex B) [Injective S.X₂] (J : InjectiveResolution S.X₁) :
    cokernel (RightDerivedCoEdge.augOf J) ⟶ S.X₃ :=
  cokernel.desc (RightDerivedCoEdge.augOf J) (resolutionToX₂ S J ≫ S.g) (by
    rw [augOf_comp_resolutionToX₂_assoc, S.zero])

/-- The projection onto `coker (S.X₁ ⟶ J⁰)` followed by `coaugToX₃ S J` is
`resolutionToX₂ S J ≫ S.g`. -/
@[reassoc]
theorem π_comp_coaugToX₃ (S : ShortComplex B) [Injective S.X₂] (J : InjectiveResolution S.X₁) :
    cokernel.π (RightDerivedCoEdge.augOf J) ≫ coaugToX₃ S J = resolutionToX₂ S J ≫ S.g :=
  cokernel.π_desc _ _ _

variable {S : ShortComplex B} (hS : S.ShortExact) [Injective S.X₂]

/-- The endomorphism `resolutionToX₂ S J ≫ liftToResolution hS J - 𝟙` of `J⁰` is killed by the
augmentation `S.X₁ ⟶ J⁰`. -/
theorem augOf_comp_resolutionToX₂_comp_liftToResolution_sub (J : InjectiveResolution S.X₁) :
    RightDerivedCoEdge.augOf J ≫
      (resolutionToX₂ S J ≫ liftToResolution hS J - 𝟙 (J.cocomplex.X 0)) = 0 := by
  rw [Preadditive.comp_sub, comp_id, augOf_comp_resolutionToX₂_assoc, f_comp_liftToResolution,
    sub_self]

/-- The failure of the retraction `J⁰ ⟶ S.X₂` to be a section of the extension `S.X₂ ⟶ J⁰` of
the augmentation, descended to the cokernel of the augmentation. -/
def retractionDefect (J : InjectiveResolution S.X₁) :
    cokernel (RightDerivedCoEdge.augOf J) ⟶ J.cocomplex.X 0 :=
  cokernel.desc (RightDerivedCoEdge.augOf J)
    (resolutionToX₂ S J ≫ liftToResolution hS J - 𝟙 _)
    (augOf_comp_resolutionToX₂_comp_liftToResolution_sub hS J)

/-- The projection onto `coker (S.X₁ ⟶ J⁰)` followed by `retractionDefect hS J` is
`resolutionToX₂ S J ≫ liftToResolution hS J - 𝟙`. -/
@[reassoc]
theorem π_comp_retractionDefect (J : InjectiveResolution S.X₁) :
    cokernel.π (RightDerivedCoEdge.augOf J) ≫ retractionDefect hS J =
      resolutionToX₂ S J ≫ liftToResolution hS J - 𝟙 _ :=
  cokernel.π_desc _ _ _

/-- **`coker (S.X₁ ⟶ J⁰) ⟶ S.X₃ ⟶ coker (S.X₁ ⟶ J⁰)` is the identity up to a morphism factoring
through `J⁰`.**  Composed with the class map, which kills the image of `Q J⁰`, this says that the
class map factors through the connecting morphism, hence that the latter is an epimorphism. -/
theorem coaugToX₃_comp_connecting (J : InjectiveResolution S.X₁) :
    coaugToX₃ S J ≫ connecting hS J =
      𝟙 _ + retractionDefect hS J ≫ cokernel.π (RightDerivedCoEdge.augOf J) := by
  rw [← cancel_epi (cokernel.π (RightDerivedCoEdge.augOf J)), Preadditive.comp_add, comp_id,
    π_comp_coaugToX₃_assoc, g_comp_connecting, π_comp_retractionDefect_assoc,
    Preadditive.sub_comp, id_comp]
  simp only [assoc]
  abel

/-- The endomorphism `liftToResolution hS J ≫ resolutionToX₂ S J - 𝟙` of `S.X₂` is killed by
`S.f`. -/
theorem f_comp_liftToResolution_comp_resolutionToX₂_sub (J : InjectiveResolution S.X₁) :
    S.f ≫ (liftToResolution hS J ≫ resolutionToX₂ S J - 𝟙 S.X₂) = 0 := by
  rw [Preadditive.comp_sub, comp_id, f_comp_liftToResolution_assoc,
    augOf_comp_resolutionToX₂, sub_self]

/-- The failure of the extension `S.X₂ ⟶ J⁰` of the augmentation to be a section of the
retraction `J⁰ ⟶ S.X₂`, descended along `S.g`. -/
def sectionDefect (J : InjectiveResolution S.X₁) : S.X₃ ⟶ S.X₂ :=
  haveI := hS.epi_g
  hS.exact.desc (liftToResolution hS J ≫ resolutionToX₂ S J - 𝟙 _)
    (f_comp_liftToResolution_comp_resolutionToX₂_sub hS J)

/-- The morphism `S.g` followed by `sectionDefect hS J` is
`liftToResolution hS J ≫ resolutionToX₂ S J - 𝟙`. -/
@[reassoc]
theorem g_comp_sectionDefect (J : InjectiveResolution S.X₁) :
    S.g ≫ sectionDefect hS J = liftToResolution hS J ≫ resolutionToX₂ S J - 𝟙 _ :=
  have := hS.epi_g
  hS.exact.g_desc _ _

/-- **`S.X₃ ⟶ coker (S.X₁ ⟶ J⁰) ⟶ S.X₃` is the identity up to a morphism factoring through
`S.X₃`**, the other half of the near-inverse pair behind the long exact sequence. -/
theorem connecting_comp_coaugToX₃ (J : InjectiveResolution S.X₁) :
    connecting hS J ≫ coaugToX₃ S J = 𝟙 S.X₃ + sectionDefect hS J ≫ S.g := by
  have := hS.epi_g
  rw [← cancel_epi S.g, Preadditive.comp_add, comp_id, g_comp_connecting_assoc,
    π_comp_coaugToX₃, g_comp_sectionDefect_assoc, Preadditive.sub_comp, id_comp]
  simp only [assoc]
  abel

variable [HasInjectiveResolutions B] (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

include hS in
/-- **The degree-one connecting morphism is an epimorphism when `S.X₂` is injective** and `Q` is
left exact.  This is the end `R¹Q X₂ = 0` of the long exact sequence, in the only form this file
needs it: the class map of `coker (X₁ ⟶ J⁰)` is an epimorphism, and it factors through the
connecting morphism. -/
theorem epi_deltaOne : Epi (deltaOne Q hS) := by
  have hχ : Epi (coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution S.X₁))
      (RightDerivedCoEdge.augOf_comp_d _)) := epi_coaugClass_augOf Q _
  have hfac : Q.map (coaugToX₃ S (injectiveResolution S.X₁)) ≫
      (Q.map (connecting hS (injectiveResolution S.X₁)) ≫
        coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution S.X₁))
          (RightDerivedCoEdge.augOf_comp_d _)) =
      coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution S.X₁))
        (RightDerivedCoEdge.augOf_comp_d _) := by
    rw [← assoc, ← Q.map_comp, coaugToX₃_comp_connecting, Q.map_add, Q.map_id, Q.map_comp,
      Preadditive.add_comp, id_comp, assoc, map_π_comp_coaugClass, comp_zero, add_zero]
  have : Epi (Q.map (connecting hS (injectiveResolution S.X₁)) ≫
      coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution S.X₁))
        (RightDerivedCoEdge.augOf_comp_d _)) := epi_of_epi_fac hfac
  rw [deltaOne_eq, ← assoc]
  infer_instance

omit [Injective S.X₂] [PreservesFiniteLimits Q] in
include hS in
/-- The composite `Q X₂ ⟶ Q X₃ ⟶ R¹Q X₁` vanishes: the comparison `X₃ ⟶ coker (X₁ ⟶ J⁰)`
precomposed with `S.g` factors through `J⁰`, whose image the class map kills. -/
theorem map_g_comp_deltaOne : Q.map S.g ≫ deltaOne Q hS = 0 := by
  rw [deltaOne_eq, ← assoc, ← Q.map_comp, g_comp_connecting, Q.map_comp, assoc,
    map_π_comp_coaugClass_assoc, zero_comp, comp_zero]

include hS in
/-- **`Q X₂ ⟶ Q X₃ ⟶ R¹Q X₁` is exact** when `S.X₂` is injective and `Q` is left exact.  A
morphism into `Q X₃` killed by the connecting morphism is, after a refinement, the image of a
morphism into `Q J⁰`, and the retraction `J⁰ ⟶ X₂` turns that into a preimage in `Q X₂` up to a
correction factoring through `S.g`. -/
theorem exact_map_g_deltaOne :
    (ShortComplex.mk (Q.map S.g) (deltaOne Q hS) (map_g_comp_deltaOne hS Q)).Exact := by
  set J := injectiveResolution S.X₁ with hJ
  have h1 : Q.map (cokernel.π (RightDerivedCoEdge.augOf J)) ≫ Q.map (coaugToX₃ S J) =
      Q.map (resolutionToX₂ S J) ≫ Q.map S.g := by
    rw [← Q.map_comp, π_comp_coaugToX₃, Q.map_comp]
  have h2 : Q.map (connecting hS J) ≫ Q.map (coaugToX₃ S J) =
      𝟙 _ + Q.map (sectionDefect hS J) ≫ Q.map S.g := by
    rw [← Q.map_comp, connecting_comp_coaugToX₃, Q.map_add, Q.map_id, Q.map_comp]
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  have hd : x ≫ Q.map (connecting hS J) ≫ coaugClass Q _ (RightDerivedCoEdge.augOf_comp_d J) ≫
      (J.isoRightDerivedObj' Q 1).inv = 0 := hx
  rw [coaugClass_eq] at hd
  have hz : (x ≫ Q.map (connecting hS J) ≫ Q.map (cyclesOfCoaug (RightDerivedCoEdge.augOf J)
        (RightDerivedCoEdge.augOf_comp_d _)) ≫ RightDerivedCoEdge.mapCycles Q J.cocomplex 1) ≫
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).homologyπ 1 = 0 := by
    rw [← cancel_mono (J.isoRightDerivedObj' Q 1).inv, zero_comp]
    simpa only [assoc] using hd
  obtain ⟨T', π₁, hπ₁, x₁, hx₁⟩ :=
    (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      J.cocomplex).comp_homologyπ_eq_zero_iff_up_to_refinements 0 1 (by simp) _).1 hz
  rw [← map_π_comp_cyclesOfCoaug_comp_mapCycles Q (RightDerivedCoEdge.augOf J)
    (RightDerivedCoEdge.augOf_comp_d _)] at hx₁
  have hcan : π₁ ≫ x ≫ Q.map (connecting hS J) =
      x₁ ≫ Q.map (cokernel.π (RightDerivedCoEdge.augOf J)) := by
    have := isIso_cyclesOfCoaug_augOf J
    rw [← cancel_mono (Q.map (cyclesOfCoaug (RightDerivedCoEdge.augOf J)
      (RightDerivedCoEdge.augOf_comp_d _)) ≫ RightDerivedCoEdge.mapCycles Q J.cocomplex 1)]
    simpa only [assoc] using hx₁
  have hcomb : π₁ ≫ x + (π₁ ≫ x ≫ Q.map (sectionDefect hS J)) ≫ Q.map S.g =
      (x₁ ≫ Q.map (resolutionToX₂ S J)) ≫ Q.map S.g := by
    have h3 := hcan =≫ Q.map (coaugToX₃ S J)
    simp only [assoc, h1, h2, Preadditive.comp_add, comp_id] at h3
    simpa only [assoc] using h3
  refine ⟨T', π₁, hπ₁, x₁ ≫ Q.map (resolutionToX₂ S J) -
    π₁ ≫ x ≫ Q.map (sectionDefect hS J), ?_⟩
  show π₁ ≫ x = (x₁ ≫ Q.map (resolutionToX₂ S J) - π₁ ≫ x ≫ Q.map (sectionDefect hS J)) ≫
    Q.map S.g
  rw [Preadditive.sub_comp, ← hcomb]
  abel

end Epi

section ClassMapTransport

variable (Q : B ⥤ D) [Q.Additive]
  {Z : B} {K : CochainComplex B ℕ} (a : Z ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
  {Z' : B} {K' : CochainComplex B ℕ} (a' : Z' ⟶ K'.X 0) (ha' : a' ≫ K'.d 0 1 = 0)
  (ψ : K' ⟶ K) (γ : cokernel a ⟶ cokernel a') (e : cokernel a ⟶ K.X 0)
  (hγ : γ ≫ coaugToOne a' ha' ≫ ψ.f 1 = coaugToOne a ha + e ≫ K.d 0 1)

include hγ in
/-- **The class map is transported by a twisted square.**  If `γ : coker a ⟶ coker a'` and a
chain map `ψ : K' ⟶ K` satisfy `γ ≫ (coker a' ⟶ K'¹) ≫ ψ¹ = (coker a ⟶ K¹)` up to a boundary of
`K`, then `γ` transports the class map of `a'` to the class map of `a`.  The boundary term is
invisible in homology, which is why the connecting morphism of this file does not need to be
compatible with the comparison of resolutions on the nose. -/
theorem map_comp_coaugClass_comp_homologyMap :
    Q.map γ ≫ coaugClass Q a' ha' ≫ HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) 1 =
      coaugClass Q a ha := by
  have hcyc : Q.map γ ≫ Q.map (cyclesOfCoaug a' ha') ≫
      RightDerivedCoEdge.mapCycles Q K' 1 ≫ HomologicalComplex.cyclesMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) 1 =
      Q.map (cyclesOfCoaug a ha) ≫ RightDerivedCoEdge.mapCycles Q K 1 +
        Q.map e ≫ ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).toCycles 0 1 := by
    rw [← cancel_mono (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles 1)]
    simp only [assoc, Preadditive.add_comp, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.toCycles_i, RightDerivedCoEdge.mapCycles_i_assoc,
      RightDerivedCoEdge.mapCycles_i, Functor.mapHomologicalComplex_map_f, ← Q.map_comp,
      cyclesOfCoaug_i_assoc, cyclesOfCoaug_i, hγ, Q.map_add,
      Functor.mapHomologicalComplex_obj_d]
  have h := hcyc =≫ ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ 1
  rw [coaugClass_eq, coaugClass_eq]
  simp only [assoc, HomologicalComplex.homologyπ_naturality] at h ⊢
  simp only [Preadditive.add_comp, assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero,
    add_zero] at h
  exact h

end ClassMapTransport

section MapAug

variable (P : A ⥤ B) [P.Additive] {X : A} (I : InjectiveResolution X)

/-- The short complex `0 ⟶ P X ⟶ (P I)⁰ ⟶ coker ⟶ 0` obtained by applying `P` to an injective
resolution `I` of `X` and taking the cokernel of the augmentation. -/
def shortComplexMapAug : ShortComplex B :=
  ShortComplex.mk (RightDerivedCoEdge.mapAug P I)
    (cokernel.π (RightDerivedCoEdge.mapAug P I)) (cokernel.condition _)

section

variable [PreservesFiniteLimits P]

/-- **`0 ⟶ P X ⟶ (P I)⁰ ⟶ coker ⟶ 0` is short exact** when `P` is left exact.  Its middle term is
injective when `P` preserves injective objects, which is what makes it the sequence computing the
first right derived functor of `P X`. -/
theorem shortExact_mapAug : (shortComplexMapAug P I).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := RightDerivedCoEdge.mono_mapAug P I
  epi_g := inferInstanceAs (Epi (cokernel.π (RightDerivedCoEdge.mapAug P I)))

end

end MapAug

section Main

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [P.PreservesInjectiveObjects]
  (Q : B ⥤ D) [Q.Additive]

/-- `Stacks.Cohomology.RightDerivedEdge.isoRightDerivedObjComp` with its target spelled as the
homology of a complex rather than as a value of the homology functor.  The two spellings are
definitionally equal, but only this one can be composed with the class map by the rewriting
tactics. -/
def isoRightDerivedObjComp' {X : A} (I : InjectiveResolution X) (n : ℕ) :
    ((P ⋙ Q).rightDerived n).obj X ≅
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).homology n :=
  RightDerivedEdge.isoRightDerivedObjComp P Q I n

omit [PreservesFiniteLimits P] in
/-- `Stacks.Cohomology.RightDerivedEdge.edge_app_eq` in the homology-of-a-complex spelling, with
the augmentation hypothesis written with `Stacks.Cohomology.RightDerivedCoEdge.augOf`. -/
theorem edge_app_eq' (n : ℕ) {X : A} (I : InjectiveResolution X)
    (J : InjectiveResolution (P.obj X))
    (φ : J.cocomplex ⟶ (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : RightDerivedCoEdge.augOf J ≫ φ.f 0 = RightDerivedCoEdge.mapAug P I) :
    (RightDerivedEdge.edge P Q n).app X = (J.isoRightDerivedObj' Q n).hom ≫
      HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
        (isoRightDerivedObjComp' P Q I n).inv :=
  RightDerivedEdge.edge_app_eq P Q n I J φ hφ

variable {X : A} (I : InjectiveResolution X)
  (φ : (injectiveResolution (P.obj X)).cocomplex ⟶
    (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  (hφ : RightDerivedCoEdge.augOf (injectiveResolution (P.obj X)) ≫ φ.f 0 =
    RightDerivedCoEdge.mapAug P I)

/-- `Stacks.Cohomology.RightDerivedDeltaOne.connecting` for the sequence
`0 ⟶ P X ⟶ (P I)⁰ ⟶ coker ⟶ 0`, with its source and target spelled as cokernels rather than as
projections of a short complex.  The retyping is what lets the rewriting tactics match it against
the class map. -/
def connectingMapAug : cokernel (RightDerivedCoEdge.mapAug P I) ⟶
    cokernel (RightDerivedCoEdge.augOf (injectiveResolution (P.obj X))) :=
  connecting (shortExact_mapAug P I) (injectiveResolution (P.obj X))

omit [HasInjectiveResolutions A] [P.PreservesInjectiveObjects] in
/-- The defining formula for the connecting morphism of
`Stacks.Cohomology.RightDerivedDeltaOne.shortExact_mapAug`. -/
theorem deltaOne_mapAug_eq :
    deltaOne Q (shortExact_mapAug P I) = Q.map (connectingMapAug P I) ≫
      coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution (P.obj X)))
          (RightDerivedCoEdge.augOf_comp_d _) ≫
        ((injectiveResolution (P.obj X)).isoRightDerivedObj' Q 1).inv :=
  rfl

omit [HasInjectiveResolutions A] [P.PreservesInjectiveObjects] in
/-- `Stacks.Cohomology.RightDerivedDeltaOne.g_comp_connecting` for
`Stacks.Cohomology.RightDerivedDeltaOne.shortExact_mapAug`, with the structure projections
evaluated and the partial retraction named as in
`Stacks.Cohomology.RightDerivedCoEdge.retractionZero`. -/
@[reassoc]
theorem π_comp_connecting_mapAug :
    cokernel.π (RightDerivedCoEdge.mapAug P I) ≫
        connectingMapAug P I =
      RightDerivedCoEdge.retractionZero P I (injectiveResolution (P.obj X)) ≫
        cokernel.π (RightDerivedCoEdge.augOf (injectiveResolution (P.obj X))) :=
  g_comp_connecting (shortExact_mapAug P I) _

omit [HasInjectiveResolutions A] [P.PreservesInjectiveObjects] in
include hφ in
/-- The partial retraction followed by the comparison differs from the identity of `(P I)⁰` by a
morphism killed by the augmentation. -/
theorem mapAug_comp_retraction_sub :
    RightDerivedCoEdge.mapAug P I ≫
        (RightDerivedCoEdge.retractionZero P I (injectiveResolution (P.obj X)) ≫ φ.f 0 -
          𝟙 _) = 0 := by
  rw [Preadditive.comp_sub, comp_id, ← assoc, RightDerivedCoEdge.mapAug_comp_retractionZero, hφ,
    sub_self]

/-- The failure of the partial retraction `(P I)⁰ ⟶ J⁰` of the comparison `φ : J ⟶ P I` to be a
section, descended to the cokernel of the augmentation.  It is the boundary term by which the
connecting morphism and the class map differ before passing to homology. -/
def comparisonDefect : cokernel (RightDerivedCoEdge.mapAug P I) ⟶
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X 0 :=
  cokernel.desc (RightDerivedCoEdge.mapAug P I)
    (RightDerivedCoEdge.retractionZero P I (injectiveResolution (P.obj X)) ≫ φ.f 0 - 𝟙 _)
    (mapAug_comp_retraction_sub P I φ hφ)

omit [HasInjectiveResolutions A] [P.PreservesInjectiveObjects] in
/-- The projection onto `coker (P X ⟶ (P I)⁰)` followed by `comparisonDefect P I φ hφ` is the
partial retraction `(P I)⁰ ⟶ J⁰` followed by `φ⁰`, minus the identity. -/
@[reassoc]
theorem π_comp_comparisonDefect :
    cokernel.π (RightDerivedCoEdge.mapAug P I) ≫ comparisonDefect P I φ hφ =
      RightDerivedCoEdge.retractionZero P I (injectiveResolution (P.obj X)) ≫ φ.f 0 - 𝟙 _ :=
  cokernel.π_desc _ _ _

omit [HasInjectiveResolutions A] [P.PreservesInjectiveObjects] in
/-- **The twisted square behind the connecting morphism.**  Following the comparison
`coker (P X ⟶ (P I)⁰) ⟶ coker (P X ⟶ J⁰)` by the inclusion of the latter into `J¹` and then by
`φ¹` gives the inclusion of the former into `(P I)¹`, up to a boundary of `P I`. -/
theorem connecting_comp_coaugToOne_comp_φ :
    connectingMapAug P I ≫
        coaugToOne (RightDerivedCoEdge.augOf (injectiveResolution (P.obj X)))
          (RightDerivedCoEdge.augOf_comp_d _) ≫ φ.f 1 =
      coaugToOne (RightDerivedCoEdge.mapAug P I) (RightDerivedCoEdge.mapAug_comp_d P I) +
        comparisonDefect P I φ hφ ≫
          ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).d 0 1 := by
  rw [← cancel_epi (cokernel.π (RightDerivedCoEdge.mapAug P I)), Preadditive.comp_add,
    π_comp_connecting_mapAug_assoc, π_comp_coaugToOne_assoc, ← φ.comm 0 1, π_comp_coaugToOne,
    π_comp_comparisonDefect_assoc, Preadditive.sub_comp, id_comp]
  simp only [assoc]
  abel

include hφ in
/-- **The connecting morphism of `0 ⟶ P X ⟶ (P I)⁰ ⟶ coker ⟶ 0`, followed by the degree-one edge
morphism of the composite `Q ∘ P`, is the class map of that cokernel.**  This is what pins the
abstract connecting morphism of this file to the already-constructed edge morphism, and it is the
whole reason the connecting morphism is of any use here. -/
theorem deltaOne_comp_edge_app_one :
    deltaOne Q (shortExact_mapAug P I) ≫ (RightDerivedEdge.edge P Q 1).app X =
      coaugClass Q (RightDerivedCoEdge.mapAug P I) (RightDerivedCoEdge.mapAug_comp_d P I) ≫
        (isoRightDerivedObjComp' P Q I 1).inv := by
  have key := map_comp_coaugClass_comp_homologyMap Q (RightDerivedCoEdge.mapAug P I)
    (RightDerivedCoEdge.mapAug_comp_d P I)
    (RightDerivedCoEdge.augOf (injectiveResolution (P.obj X)))
    (RightDerivedCoEdge.augOf_comp_d _) φ
    (connectingMapAug P I)
    (comparisonDefect P I φ hφ) (connecting_comp_coaugToOne_comp_φ P I φ hφ)
  show (Q.map (connectingMapAug P I) ≫
      coaugClass Q (RightDerivedCoEdge.augOf (injectiveResolution (P.obj X)))
          (RightDerivedCoEdge.augOf_comp_d _) ≫
        ((injectiveResolution (P.obj X)).isoRightDerivedObj' Q 1).inv) ≫
      (RightDerivedEdge.edge P Q 1).app X = _
  rw [edge_app_eq' P Q 1 I (injectiveResolution (P.obj X)) φ hφ]
  simp only [assoc, Iso.inv_hom_id_assoc]
  simpa only [assoc] using key =≫ (isoRightDerivedObjComp' P Q I 1).inv

end Main

section FiveTerm

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [P.PreservesInjectiveObjects]
  (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q] (X : A)

omit [HasInjectiveResolutions B] [PreservesFiniteLimits P] [P.PreservesInjectiveObjects] in
/-- `Stacks.Cohomology.RightDerivedCoEdge.isoRightDerivedObjComp_inv_comp_secondEdgeApp` solved
for the co-edge morphism, in the homology-of-a-complex spelling. -/
theorem secondEdge_app_eq_hom_comp {X : A} (I : InjectiveResolution X) :
    (RightDerivedCoEdge.secondEdge P Q 1).app X =
      (isoRightDerivedObjComp' P Q I 1).hom ≫
        RightDerivedCoEdge.homologyToMapHomology Q
            ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 1 ≫
          Q.map (I.isoRightDerivedObj P 1).inv := by
  have h := RightDerivedCoEdge.isoRightDerivedObjComp_inv_comp_secondEdgeApp P Q 1 I
  exact ((isoRightDerivedObjComp' P Q I 1).inv_comp_eq).1 h

/-- **The five-term low-degree sequence of a composite of right derived functors is exact in the
middle**: for additive `P` and `Q` with `P` left exact and preserving injective objects and `Q`
left exact, the sequence

  `R¹Q (P X) ⟶ R¹(Q ∘ P) X ⟶ Q (R¹P X)`

made of the edge morphism and the co-edge morphism is exact.  The proof reads both maps on the
chosen injective resolution `I` of `X`: the kernel of the co-edge morphism is the image of the
class map of `coker (P X ⟶ (P I)⁰)` (`exact_coaugClass`), and that class map factors through the
edge morphism via the degree-one connecting morphism
(`deltaOne_comp_edge_app_one`). -/
theorem exact_edge_secondEdge :
    (ShortComplex.mk ((RightDerivedEdge.edge P Q 1).app X)
      ((RightDerivedCoEdge.secondEdge P Q 1).app X)
      (RightDerivedCoEdge.edge_comp_secondEdge P Q 0 X)).Exact := by
  set I := injectiveResolution X with hI
  have hεg : (coaugClass Q (RightDerivedCoEdge.mapAug P I)
        (RightDerivedCoEdge.mapAug_comp_d P I) ≫ (isoRightDerivedObjComp' P Q I 1).inv) ≫
      (RightDerivedCoEdge.secondEdge P Q 1).app X = 0 := by
    rw [secondEdge_app_eq_hom_comp P Q I, assoc, Iso.inv_hom_id_assoc,
      coaugClass_comp_homologyToMapHomology_assoc, zero_comp]
  have hS' := exact_coaugClass Q (RightDerivedCoEdge.mapAug P I)
    (RightDerivedCoEdge.mapAug_comp_d P I) (RightDerivedCoEdge.exact_mapAug P I)
  have e : (ShortComplex.mk (coaugClass Q (RightDerivedCoEdge.mapAug P I)
          (RightDerivedCoEdge.mapAug_comp_d P I))
        (RightDerivedCoEdge.homologyToMapHomology Q
          ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 1)
        (coaugClass_comp_homologyToMapHomology Q _ _)) ≅
      ShortComplex.mk (coaugClass Q (RightDerivedCoEdge.mapAug P I)
            (RightDerivedCoEdge.mapAug_comp_d P I) ≫ (isoRightDerivedObjComp' P Q I 1).inv)
          ((RightDerivedCoEdge.secondEdge P Q 1).app X) hεg :=
    ShortComplex.isoMk (Iso.refl _) (isoRightDerivedObjComp' P Q I 1).symm
      (Q.mapIso (I.isoRightDerivedObj P 1)).symm (by simp)
      (RightDerivedCoEdge.isoRightDerivedObjComp_inv_comp_secondEdgeApp P Q 1 I)
  exact exact_of_factor_of_exact _ (deltaOne Q (shortExact_mapAug P I))
    (deltaOne_comp_edge_app_one P Q I (RightDerivedEdge.resolutionComparison P X)
      (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X)) hεg
    (ShortComplex.exact_of_iso e hS')

end FiveTerm

end Stacks.Cohomology.RightDerivedDeltaOne

end
