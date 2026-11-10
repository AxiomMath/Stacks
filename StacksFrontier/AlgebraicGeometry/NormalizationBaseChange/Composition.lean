module

public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian

/-!
# Normalized base change along a tower of bases

Let `X` be a scheme over a base `T₁` and let `ν : Y ⟶ X` be its normalization. For a further
base `T ⟶ T₁` the normalized base change of `X` relative to `T` is the normalization of
`X ×_{T₁} T`, and the normalized base change of `Y` relative to `T` is the normalization of
`Y ×_{T₁} T`. The base change of `ν` is an integral morphism `Y ×_{T₁} T ⟶ X ×_{T₁} T`, so as
soon as it is birational over every quasi-compact open the two normalizations agree: taking the
normalized base change commutes with composition of base changes.

## Main definitions

Unqualified names below live in the `AlgebraicGeometry.NormalizedBaseChange` namespace.

* `baseChangeMap`: the base change of a morphism of schemes over `T₁` along a morphism `T ⟶ T₁`, as
  a morphism between the two base changes.

## Main results

* `isPullback_baseChangeMap`: the base change of a morphism sits in a pullback square over it.
* `isIso_baseChangeMap_morphismRestrict`: the base change of a morphism which is an isomorphism
  over an open is an isomorphism over the base change of that open.
* `isBirational_baseChangeMap`: the base change of a morphism which is an isomorphism over a dense
  open with dense preimage is birational, provided both base-change projections are open.
* `isBirational_baseChangeMap_normalization`: the base change of the normalization of a reduced
  Noetherian scheme along a morphism with open projections is birational, provided the
  normalization is locally of finite type.
* `exists_normalizationScheme_iso_baseChangeMap_normalization`: the normalization of `X ×_{T₁} T`
  is the normalization of `Y ×_{T₁} T`, compatibly with both normalization morphisms, whenever the
  base change of `ν` is birational over every quasi-compact open.
* `exists_normalizationScheme_iso_baseChangeMap_normalization_of_isBirational`: the same conclusion
  for locally Noetherian base changes, from birationality of the base change of `ν` alone.
* `exists_normalizationScheme_iso_baseChangeMap_normalization_of_isOpenMap`: the same conclusion
  with no birationality hypothesis, for the normalization of a reduced Noetherian scheme
  base-changed along a morphism whose two projections are open.
* `AlgebraicGeometry.noetherianSpace_of_locallyOfFiniteType`: a quasi-compact scheme locally of
  finite type over a Noetherian ring is a Noetherian space.
* `exists_normalizationScheme_iso_baseChangeMap_normalization_of_isNoetherianRing`: the same
  conclusion for a reduced scheme quasi-compact and locally of finite type over a Noetherian ring
  with finite normalization, where every topological finiteness condition is produced rather than
  assumed.

## Implementation notes

The three base changes are taken as abstract pullback squares rather than as the chosen pullbacks,
so that a user may supply whichever presentation is at hand; `IsPullback.of_hasPullback` produces
the chosen one. Since `X ×_{T₁} T` is simultaneously a base change of `X` along `T ⟶ T₁` and a base
change of the scheme downstairs of `X ⟶ T₁` along the composite, by
`CategoryTheory.IsPullback.paste_horiz`, a single square covers both readings.

That the base change of an integral morphism is integral is inherited from stability of
`AlgebraicGeometry.IsIntegralHom` under base change, through the pullback square over `ν`.
Birationality of the base change is not formal: an integral birational morphism is an isomorphism
over a dense open of its target only when the target is reduced and the morphism is locally of
finite type, and the base change is birational only because that dense open and its preimage stay
dense, which needs both projections to be open.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 09IK](https://stacks.math.columbia.edu/tag/09IK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! The comparison morphism of this file is called `baseChangeMap` in the
`NormalizedBaseChange` namespace; the shorter `AlgebraicGeometry.baseChangeMap` names the
comparison between base changes of objects over a fixed base. -/
namespace NormalizedBaseChange

section BaseChangeMap

variable {X Y T T₁ V W : Scheme.{u}} {q : X ⟶ T₁} {j : T ⟶ T₁} {ν : Y ⟶ X}
  {a : V ⟶ Y} {b : V ⟶ T} {c : W ⟶ X} {d : W ⟶ T}

/-- The base change of a morphism `ν : Y ⟶ X` of schemes over `T₁` along a morphism `T ⟶ T₁`,
as a morphism from a base change `V` of `Y` to a base change `W` of `X`. -/
def baseChangeMap (hV : IsPullback a b (ν ≫ q) j) (hW : IsPullback c d q j) : V ⟶ W :=
  hW.lift (a ≫ ν) b ((Category.assoc a ν q).trans hV.w)

/-- The base change of `ν` followed by the first projection of `W` is the first projection of
`V` followed by `ν`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_comp_fst (hV : IsPullback a b (ν ≫ q) j) (hW : IsPullback c d q j) :
    baseChangeMap hV hW ≫ c = a ≫ ν :=
  hW.lift_fst _ _ _

/-- The base change of `ν` followed by the second projection of `W` is the second projection of
`V`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_comp_snd (hV : IsPullback a b (ν ≫ q) j) (hW : IsPullback c d q j) :
    baseChangeMap hV hW ≫ d = b :=
  hW.lift_snd _ _ _

/-- The base change of a morphism `ν` along `T ⟶ T₁` sits in a pullback square over `ν`. -/
theorem isPullback_baseChangeMap (hV : IsPullback a b (ν ≫ q) j) (hW : IsPullback c d q j) :
    IsPullback (baseChangeMap hV hW) a c ν := by
  have he : baseChangeMap hV hW =
      hW.flip.lift b (a ≫ ν) (by rw [hV.flip.w, Category.assoc]) :=
    hW.hom_ext (by rw [baseChangeMap_comp_fst, hW.flip.lift_snd])
      (by rw [baseChangeMap_comp_snd, hW.flip.lift_fst])
  rw [he]
  exact IsPullback.of_right' hV.flip hW.flip

/-- The preimage under the base change of `ν` of the preimage of an open `U` of `X` is the
preimage of `ν ⁻¹ᵁ U`. -/
private theorem baseChangeMap_preimage_preimage (hV : IsPullback a b (ν ≫ q) j)
    (hW : IsPullback c d q j) (U : X.Opens) :
    baseChangeMap hV hW ⁻¹ᵁ (c ⁻¹ᵁ U) = a ⁻¹ᵁ (ν ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, (isPullback_baseChangeMap hV hW).w, Scheme.Hom.comp_preimage]

/-- The base change of an integral morphism is integral. -/
instance isIntegralHom_baseChangeMap (hV : IsPullback a b (ν ≫ q) j)
    (hW : IsPullback c d q j) [IsIntegralHom ν] : IsIntegralHom (baseChangeMap hV hW) :=
  MorphismProperty.of_isPullback (P := @IsIntegralHom)
    (isPullback_baseChangeMap hV hW).flip ‹_›

/-- The base change of a morphism which is an isomorphism over an open of its target is an
isomorphism over the base change of that open. -/
theorem isIso_baseChangeMap_morphismRestrict (hV : IsPullback a b (ν ≫ q) j)
    (hW : IsPullback c d q j) (U : X.Opens) [IsIso (ν ∣_ U)] :
    IsIso (baseChangeMap hV hW ∣_ (c ⁻¹ᵁ U)) := by
  have HR := Scheme.Hom.isPullback_resLE (isPullback_baseChangeMap hV hW) (US := U)
    (UT := ν ⁻¹ᵁ U) (UX := c ⁻¹ᵁ U) le_rfl le_rfl
    (UY := baseChangeMap hV hW ⁻¹ᵁ (c ⁻¹ᵁ U)) (by rw [baseChangeMap_preimage_preimage, inf_idem])
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    MorphismProperty.of_isPullback (P := .isomorphisms Scheme) HR.flip
      (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
        (inferInstance : IsIso (ν ∣_ U)))

/-- A generic point of an irreducible component of a Noetherian space lies in every dense
open. -/
private theorem mem_of_mem_genericPoints_of_dense {Z : Type u} [TopologicalSpace Z]
    [NoetherianSpace Z] (U : Opens Z) (hU : Dense (U : Set Z)) {x : Z}
    (hx : x ∈ genericPoints Z) : x ∈ U := by
  obtain ⟨O, hO, hOne, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hx
  obtain ⟨y, hyO, hyU⟩ := (dense_iff_inter_open.mp hU) O hO hOne
  exact ((genericPoints.isGenericPoint ⟨x, hx⟩).specializes (hOC hyO)).mem_open U.isOpen hyU

/-- An isomorphism of schemes bijects the generic points of irreducible components. -/
private theorem bijOn_genericPoints_of_iso {A B : Scheme.{u}} (e : A ≅ B) :
    Set.BijOn e.hom (genericPoints A) (genericPoints B) :=
  ⟨fun _ hx ↦ e.hom.isOpenEmbedding.mem_genericPoints hx,
    fun _ _ _ _ hxy ↦ e.hom.homeomorph.injective hxy,
    fun y hy ↦ ⟨e.inv y, e.inv.isOpenEmbedding.mem_genericPoints hy, by simp⟩⟩

/-- A morphism of Noetherian schemes which is an isomorphism over a dense open of its target,
and whose preimage of that open is dense, is birational. -/
private theorem isBirational_of_dense_isIso_morphismRestrict {A B : Scheme.{u}}
    [NoetherianSpace A] [NoetherianSpace B] (f : A ⟶ B) (U : B.Opens)
    (hU : Dense (U : Set B)) (hpre : Dense (f ⁻¹' (U : Set B))) [IsIso (f ∣_ U)] :
    IsBirational f := by
  have hval (z : A) (hz : z ∈ f ⁻¹ᵁ U) : ((f ∣_ U) ⟨z, hz⟩).1 = f z :=
    congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ B ↦ g ⟨z, hz⟩) (morphismRestrict_ι f U)
  have hmem {x : A} (hx : x ∈ genericPoints A) : x ∈ f ⁻¹ᵁ U :=
    mem_of_mem_genericPoints_of_dense (f ⁻¹ᵁ U) hpre hx
  have hgen {x : A} (hx : x ∈ genericPoints A) : f x ∈ genericPoints B := by
    have H := U.ι.isOpenEmbedding.mem_genericPoints
      ((bijOn_genericPoints_of_iso (asIso (f ∣_ U))).mapsTo
        ((f ⁻¹ᵁ U).ι.isOpenEmbedding.mem_genericPoints_of_image (x := ⟨x, hmem hx⟩) hx))
    change ((f ∣_ U) ⟨x, hmem hx⟩).1 ∈ genericPoints B at H
    rwa [← hval x (hmem hx)]
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨fun _ ↦ hgen, fun x hx y hy hxy ↦ ?_,
    fun y hy ↦ ?_⟩ fun x hx ↦ ?_
  · have he : (f ∣_ U) ⟨x, hmem hx⟩ = (f ∣_ U) ⟨y, hmem hy⟩ :=
      Subtype.ext ((hval x _).trans (hxy.trans (hval y _).symm))
    exact congrArg Subtype.val ((f ∣_ U).homeomorph.injective he)
  · have hyU := mem_of_mem_genericPoints_of_dense U hU hy
    obtain ⟨x, hx, he⟩ := (bijOn_genericPoints_of_iso (asIso (f ∣_ U))).surjOn
      (U.ι.isOpenEmbedding.mem_genericPoints_of_image (x := (⟨y, hyU⟩ : U.toScheme)) hy)
    exact ⟨x.1, (f ⁻¹ᵁ U).ι.isOpenEmbedding.mem_genericPoints hx,
      (hval x.1 x.2).symm.trans (congrArg Subtype.val he)⟩
  · exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictStalkMap f U ⟨x, hmem hx⟩)).mp
        (((isIso_iff_isIso_stalkMap (f ∣_ U)).mp inferInstance).2 _)

/-- The base change of a morphism which is an isomorphism over a dense open of its target, with
dense preimage, is birational, provided both base-change projections are open. -/
theorem isBirational_baseChangeMap (hV : IsPullback a b (ν ≫ q) j)
    (hW : IsPullback c d q j) [NoetherianSpace V] [NoetherianSpace W]
    (hc : IsOpenMap c) (ha : IsOpenMap a) (U : X.Opens) (hU : Dense (U : Set X))
    (hpre : Dense (ν ⁻¹' (U : Set X))) [IsIso (ν ∣_ U)] :
    IsBirational (baseChangeMap hV hW) := by
  have hiso : IsIso (baseChangeMap hV hW ∣_ (c ⁻¹ᵁ U)) :=
    isIso_baseChangeMap_morphismRestrict hV hW U
  refine isBirational_of_dense_isIso_morphismRestrict _ (c ⁻¹ᵁ U) (hU.preimage hc) ?_
  change Dense ((baseChangeMap hV hW ⁻¹ᵁ (c ⁻¹ᵁ U) : V.Opens) : Set V)
  rw [baseChangeMap_preimage_preimage]
  exact hpre.preimage ha

end BaseChangeMap

section Composition

variable {X T T₁ V W : Scheme.{u}} {q : X ⟶ T₁} {j : T ⟶ T₁}

/-- The base change of the normalization of a reduced scheme along a morphism whose two
projections are open is birational, provided the normalization is locally of finite type. -/
theorem isBirational_baseChangeMap_normalization [IsReduced X] [NoetherianSpace X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    [NoetherianSpace (X.normalizationScheme hX)] [LocallyOfFiniteType (X.normalization hX)]
    {a : V ⟶ X.normalizationScheme hX} {b : V ⟶ T}
    (hV : IsPullback a b (X.normalization hX ≫ q) j)
    {c : W ⟶ X} {d : W ⟶ T} (hW : IsPullback c d q j)
    [NoetherianSpace V] [NoetherianSpace W] (hc : IsOpenMap c) (ha : IsOpenMap a) :
    IsBirational (baseChangeMap hV hW) := by
  have : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have : Finite (irreducibleComponents (X.normalizationScheme hX)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hnu : IsBirational (X.normalization hX) := X.isBirational_normalization hX
  obtain ⟨U, hU, hiso⟩ := exists_dense_open_isIso_morphismRestrict_of_isIntegralHom
    (X.normalization hX) hnu (Or.inl ⟨inferInstance, inferInstance⟩)
  refine isBirational_baseChangeMap hV hW hc ha U hU
    ((dense_iff_closure_eq.mpr
      (genericPoints.closure (α := X.normalizationScheme hX))).mono fun z hz ↦ ?_)
  exact mem_of_mem_genericPoints_of_dense U hU (hnu.bijOn.mapsTo hz)

/-- **Taking the normalized base change commutes with composition.** Let `X` be a scheme over
`T₁` whose quasi-compact opens have finitely many irreducible components, let `V` be a base
change of its normalization along `T ⟶ T₁` and let `W` be the corresponding base change of `X`.
If the induced morphism `V ⟶ W` is birational over every quasi-compact open of `W`, then the
normalization of `W` is a normalization of `V`. -/
theorem exists_normalizationScheme_iso_baseChangeMap_normalization
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {a : V ⟶ X.normalizationScheme hX} {b : V ⟶ T}
    (hV : IsPullback a b (X.normalization hX ≫ q) j)
    {c : W ⟶ X} {d : W ⟶ T} (hW : IsPullback c d q j)
    (hWfin : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (hcomponents : ∀ U : W.Opens, IsCompact (U : Set W) →
      (irreducibleComponents (baseChangeMap hV hW ⁻¹ᵁ U)).Finite)
    (hbirational : ∀ U : W.Opens, IsCompact (U : Set W) →
      IsBirational (baseChangeMap hV hW ∣_ U)) :
    ∃ (hVfin : ∀ U : V.Opens, IsCompact (U : Set V) → (irreducibleComponents U).Finite)
      (g : W.normalizationScheme hWfin ⟶ V)
      (e : W.normalizationScheme hWfin ≅ V.normalizationScheme hVfin),
      g ≫ baseChangeMap hV hW = W.normalization hWfin ∧
        e.hom ≫ V.normalization hVfin = g :=
  exists_normalizationFactorization_of_integral_of_birational hWfin _ hcomponents hbirational

/-- **Taking the normalized base change commutes with composition**, for locally Noetherian
base changes. The finiteness conditions on irreducible components are automatic, and
birationality over every quasi-compact open follows from birationality. -/
theorem exists_normalizationScheme_iso_baseChangeMap_normalization_of_isBirational
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {a : V ⟶ X.normalizationScheme hX} {b : V ⟶ T}
    (hV : IsPullback a b (X.normalization hX ≫ q) j)
    {c : W ⟶ X} {d : W ⟶ T} (hW : IsPullback c d q j)
    [IsLocallyNoetherian V] [IsLocallyNoetherian W]
    (hbirational : IsBirational (baseChangeMap hV hW)) :
    ∃ (g : W.normalizationScheme (finite_irreducibleComponents_of_isCompact W) ⟶ V)
      (e : W.normalizationScheme (finite_irreducibleComponents_of_isCompact W) ≅
        V.normalizationScheme (finite_irreducibleComponents_of_isCompact V)),
      g ≫ baseChangeMap hV hW =
          W.normalization (finite_irreducibleComponents_of_isCompact W) ∧
        e.hom ≫ V.normalization (finite_irreducibleComponents_of_isCompact V) = g := by
  obtain ⟨_, g, e, hg, he⟩ :=
    exists_normalizationScheme_iso_baseChangeMap_normalization hX hV hW
      (finite_irreducibleComponents_of_isCompact W)
      (fun U hU ↦ finite_irreducibleComponents_of_isCompact V _
        (QuasiCompact.isCompact_preimage _ U.2 hU))
      fun U _ ↦ hbirational.morphismRestrict U
  exact ⟨g, e, hg, he⟩

/-- **Taking the normalized base change commutes with composition**, for the normalization of a
reduced Noetherian scheme base-changed along a morphism whose two projections are open. -/
theorem exists_normalizationScheme_iso_baseChangeMap_normalization_of_isOpenMap
    [IsReduced X] [NoetherianSpace X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    [NoetherianSpace (X.normalizationScheme hX)] [LocallyOfFiniteType (X.normalization hX)]
    {a : V ⟶ X.normalizationScheme hX} {b : V ⟶ T}
    (hV : IsPullback a b (X.normalization hX ≫ q) j)
    {c : W ⟶ X} {d : W ⟶ T} (hW : IsPullback c d q j)
    [NoetherianSpace V] [NoetherianSpace W] [IsLocallyNoetherian V] [IsLocallyNoetherian W]
    (hc : IsOpenMap c) (ha : IsOpenMap a) :
    ∃ (g : W.normalizationScheme (finite_irreducibleComponents_of_isCompact W) ⟶ V)
      (e : W.normalizationScheme (finite_irreducibleComponents_of_isCompact W) ≅
        V.normalizationScheme (finite_irreducibleComponents_of_isCompact V)),
      g ≫ baseChangeMap hV hW =
          W.normalization (finite_irreducibleComponents_of_isCompact W) ∧
        e.hom ≫ V.normalization (finite_irreducibleComponents_of_isCompact V) = g :=
  exists_normalizationScheme_iso_baseChangeMap_normalization_of_isBirational hX hV hW
    (isBirational_baseChangeMap_normalization hX hV hW hc ha)

end Composition

end NormalizedBaseChange

/-! ### The Noetherian situation over a base ring -/

/-- **A quasi-compact scheme locally of finite type over a Noetherian ring is a Noetherian
space.** It is locally Noetherian and compact, hence Noetherian. -/
theorem noetherianSpace_of_locallyOfFiniteType {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [QuasiCompact f] :
    NoetherianSpace X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := IsNoetherian.mk
  inferInstance

namespace NormalizedBaseChange

/-- A base change of a quasi-compact scheme locally of finite type over a Noetherian ring, along a
morphism of Noetherian rings, is a Noetherian space and locally Noetherian. -/
private theorem noetherianSpace_isLocallyNoetherian_of_isPullback {A B : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing B] [IsNoetherianRing B] {P Q : Scheme.{u}}
    (p : P ⟶ Spec (.of A)) [LocallyOfFiniteType p] [QuasiCompact p] {x : Q ⟶ P}
    {y : Q ⟶ Spec (.of B)} {j : Spec (.of B) ⟶ Spec (.of A)} (h : IsPullback x y p j) :
    NoetherianSpace Q ∧ IsLocallyNoetherian Q :=
  have _ : LocallyOfFiniteType y := MorphismProperty.IsStableUnderBaseChange.of_isPullback h ‹_›
  have _ : QuasiCompact y := MorphismProperty.IsStableUnderBaseChange.of_isPullback h ‹_›
  ⟨noetherianSpace_of_locallyOfFiniteType y, LocallyOfFiniteType.isLocallyNoetherian y⟩

/-- **Taking the normalized base change commutes with composition**, for a reduced scheme
quasi-compact and locally of finite type over a Noetherian ring whose normalization is finite,
base-changed along a morphism of Noetherian rings with open projections.

Every topological finiteness condition of the open-map form
`exists_normalizationScheme_iso_baseChangeMap_normalization_of_isOpenMap`
is produced here from finite type over the Noetherian bases: both base changes are again
quasi-compact and locally of finite type over `Spec B`, and the normalization is so over
`Spec A` because it is finite. -/
theorem exists_normalizationScheme_iso_baseChangeMap_normalization_of_isNoetherianRing
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsNoetherianRing B]
    [Algebra A B] {X V W : Scheme.{u}} (q : X ⟶ Spec (.of A)) [IsReduced X]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hfin : IsFinite (X.normalization hX))
    {a : V ⟶ X.normalizationScheme hX} {b : V ⟶ Spec (.of B)}
    (hV : IsPullback a b (X.normalization hX ≫ q)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    {c : W ⟶ X} {d : W ⟶ Spec (.of B)}
    (hW : IsPullback c d q (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hc : IsOpenMap c.base) (ha : IsOpenMap a.base) :
    letI : LocallyOfFiniteType d :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hW inferInstance
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian d
    letI : LocallyOfFiniteType b :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hV inferInstance
    letI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian b
    ∃ (g : W.normalizationScheme (finite_irreducibleComponents_of_isCompact W) ⟶ V)
      (e : W.normalizationScheme (finite_irreducibleComponents_of_isCompact W) ≅
        V.normalizationScheme (finite_irreducibleComponents_of_isCompact V)),
      g ≫ baseChangeMap hV hW =
          W.normalization (finite_irreducibleComponents_of_isCompact W) ∧
        e.hom ≫ V.normalization (finite_irreducibleComponents_of_isCompact V) = g := by
  obtain ⟨_, _⟩ := noetherianSpace_isLocallyNoetherian_of_isPullback q hW
  obtain ⟨_, _⟩ := noetherianSpace_isLocallyNoetherian_of_isPullback (X.normalization hX ≫ q) hV
  have _ : NoetherianSpace X := noetherianSpace_of_locallyOfFiniteType q
  have _ : NoetherianSpace (X.normalizationScheme hX) :=
    noetherianSpace_of_locallyOfFiniteType (X.normalization hX ≫ q)
  exact exists_normalizationScheme_iso_baseChangeMap_normalization_of_isOpenMap hX hV hW hc ha

end NormalizedBaseChange

end AlgebraicGeometry
