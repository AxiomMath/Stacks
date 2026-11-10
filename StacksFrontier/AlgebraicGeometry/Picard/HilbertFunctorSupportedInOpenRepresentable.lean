module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenSubfunctor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpen

/-!
# The subfunctor of families supported in an open is the Hilbert functor of that open

Let `X` be a scheme over `S`, let `U ⊆ X` be an open and let `d` be a natural number. The
families in the degree-`d` Hilbert functor of `X` which are supported in `U` form a subfunctor
`Stacks.Hilbert.supportedIn X d U`, and:

* it is an open subfunctor, in the sense of `Stacks.Hilbert.IsOpenHilbertSubfunctor`;
* when every family in `U` is closed in `X ×_S T` (`Stacks.Hilbert.ClosedInAmbient`, which holds
  for `X ⟶ S` separated), it is isomorphic to the degree-`d` Hilbert functor of `U` regarded as a
  scheme over `S`, so it is representable as soon as that functor is.

## Main definitions

* `Stacks.Hilbert.restrictOver` — an open `U ⊆ X`, as a scheme over `S`.
* `Stacks.Hilbert.HilbertFamily.restrictOpen` — a family supported in `U` restricted to
  `U ×_S T`.
* `Stacks.Hilbert.HilbertFamily.extendOpen` — a family in `U ×_S T`, viewed in `X ×_S T`.
* `Stacks.Hilbert.ClosedInAmbient` — every family in `U ×_S T` is closed in `X ×_S T`.
* `Stacks.Hilbert.supportedInIso` — the natural isomorphism between `supportedIn X d U` and
  the Hilbert functor of `U`.

## Main results

* `Stacks.Hilbert.isOpenHilbertSubfunctor_supportedIn` — `supportedIn X d U` is open.
* `Stacks.Hilbert.supportedInRepresentableBy` — a representing scheme of the Hilbert functor
  of `U` represents `supportedIn X d U`.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01IQ](https://stacks.math.columbia.edu/tag/01IQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-! ### Openness -/

/-- The subfunctor of families supported in an open `U` is an open subfunctor. -/
theorem isOpenHilbertSubfunctor_supportedIn (X : Over S) (d : ℕ) (U : X.left.Opens) :
    IsOpenHilbertSubfunctor (supportedIn X d U) := by
  intro T Z
  refine ⟨⟨(Z.notSupportedLocus U)ᶜ, (Z.isClosed_notSupportedLocus U).isOpen_compl⟩,
    fun T' g => ?_⟩
  change (baseChange X g Z).SupportedIn U ↔ _
  rw [HilbertFamily.baseChange_supportedIn_iff]
  exact ⟨fun h _ ⟨t, ht⟩ => ht ▸ h t, fun h t => h ⟨t, rfl⟩⟩

/-! ### The open, as a scheme over the base -/

/-- An open `U` of a scheme `X` over `S`, as a scheme over `S`. -/
abbrev restrictOver (X : Over S) (U : X.left.Opens) : Over S :=
  Over.mk (U.ι ≫ X.hom)

/-- The inclusion of an open `U ⊆ X`, as a morphism over `S`. -/
abbrev restrictOverι (X : Over S) (U : X.left.Opens) : restrictOver X U ⟶ X :=
  Over.homMk U.ι

/-- The map `X ×_S T ⟶ Y ×_S T` induced by `X ⟶ Y` lies over `T`. -/
@[reassoc (attr := simp)]
theorem familyAmbientMap_hom {X Y : Over S} (i : X ⟶ Y) (T : Over S) :
    familyAmbientMap i T ≫ ((Over.pullback T.hom).obj Y).hom =
      ((Over.pullback T.hom).obj X).hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The map `X ×_S T ⟶ Y ×_S T` induced by `X ⟶ Y` is compatible with the projections. -/
@[reassoc (attr := simp)]
theorem familyAmbientMap_familyProjection {X Y : Over S} (i : X ⟶ Y) (T : Over S) :
    familyAmbientMap i T ≫ familyProjection Y T = familyProjection X T ≫ i.left :=
  pullback.lift_fst _ _ _

/-- The maps induced on the ambient schemes of families by `X ⟶ Y` and by `T' ⟶ T` commute. -/
@[reassoc]
theorem familyAmbientMap_familyBaseChangeMap {X Y : Over S} (i : X ⟶ Y) {T' T : Over S}
    (g : T' ⟶ T) :
    familyAmbientMap i T' ≫ familyBaseChangeMap Y g =
      familyBaseChangeMap X g ≫ familyAmbientMap i T := by
  refine pullback.hom_ext ?_ ?_
  · change _ ≫ _ ≫ familyProjection Y T = _ ≫ _ ≫ familyProjection Y T
    rw [familyBaseChangeMap_comp_familyProjection, familyAmbientMap_familyProjection,
      familyAmbientMap_familyProjection, ← Category.assoc,
      familyBaseChangeMap_comp_familyProjection]
  · change _ ≫ _ ≫ ((Over.pullback T.hom).obj Y).hom = _ ≫ _ ≫ ((Over.pullback T.hom).obj Y).hom
    rw [familyAmbientMap_hom, (isPullback_familyBaseChangeMap Y g).w,
      familyAmbientMap_hom_assoc, (isPullback_familyBaseChangeMap X g).w]

/-- `U ×_S T` is the preimage of `U` in `X ×_S T`: the square formed by the two projections to
`U` and `X` and the two inclusions is cartesian. -/
theorem isPullback_familyAmbientMap_restrictOverι (X : Over S) (U : X.left.Opens) (T : Over S) :
    IsPullback (familyProjection (restrictOver X U) T) (familyAmbientMap (restrictOverι X U) T)
      U.ι (familyProjection X T) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback X.hom T.hom)
  rw [show familyAmbientMap (restrictOverι X U) T ≫ pullback.snd X.hom T.hom =
      pullback.snd (U.ι ≫ X.hom) T.hom from familyAmbientMap_hom _ T]
  exact IsPullback.of_hasPullback (U.ι ≫ X.hom) T.hom

/-- The inclusion `U ×_S T ⟶ X ×_S T` is an open immersion. -/
instance isOpenImmersion_familyAmbientMap_restrictOverι (X : Over S) (U : X.left.Opens)
    (T : Over S) : IsOpenImmersion (familyAmbientMap (restrictOverι X U) T) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_familyAmbientMap_restrictOverι X U T)
    (inferInstanceAs (IsOpenImmersion U.ι))

/-- A point of `X ×_S T` lying over `U` comes from `U ×_S T`. -/
theorem exists_familyAmbientMap_restrictOverι_eq {X : Over S} {U : X.left.Opens} {T : Over S}
    (p : ((Over.pullback T.hom).obj X).left) (hp : familyProjection X T p ∈ U) :
    ∃ q, familyAmbientMap (restrictOverι X U) T q = p := by
  obtain ⟨x, hx⟩ : familyProjection X T p ∈ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  exact exists_preimage_of_isPullback (isPullback_familyAmbientMap_restrictOverι X U T).flip
    p x hx.symm

/-- A point of `U ×_S T` lies over `U` in `X`. -/
theorem familyProjection_familyAmbientMap_restrictOverι_mem {X : Over S} {U : X.left.Opens}
    {T : Over S} (q : ((Over.pullback T.hom).obj (restrictOver X U)).left) :
    familyProjection X T (familyAmbientMap (restrictOverι X U) T q) ∈ U := by
  rw [← Scheme.Hom.comp_apply, ← (isPullback_familyAmbientMap_restrictOverι X U T).w,
    Scheme.Hom.comp_apply]
  exact (Scheme.Opens.range_ι U).subset ⟨_, rfl⟩

/-! ### Transport of families between `X ×_S T` and `U ×_S T` -/

/-- Finite local freeness of rank `d` transported along an isomorphism of sources compatible with
the two morphisms. -/
private theorem isFiniteLocallyFreeOfRank_of_iso {A B T : Scheme.{u}} (e : A ≅ B) {a : A ⟶ T}
    {b : B ⟶ T} (h : e.hom ≫ b = a) {d : ℕ} (hb : Stacks.Morphisms.IsFiniteLocallyFreeOfRank b d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank a d :=
  h ▸ Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp e b hb

variable {X : Over S} {d : ℕ} {U : X.left.Opens}

/-- If the closed subscheme cut out by `I` lies over `U`, its pullback to `U ×_S T` maps
isomorphically onto it. -/
private theorem isIso_pullback_snd_of_supportedIn {T : Over S}
    (I : ((Over.pullback T.hom).obj X).left.IdealSheafData)
    (hI : ∀ z : I.subscheme, familyProjection X T (I.subschemeι z) ∈ U) :
    IsIso (pullback.snd (familyAmbientMap (restrictOverι X U) T) I.subschemeι) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun z => ?_⟩⟩
  obtain ⟨q, hq⟩ := exists_familyAmbientMap_restrictOverι_eq _ (hI z)
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback q z hq
  exact ⟨w, hw⟩

/-- The pullback of `I` to `U ×_S T` cuts out a closed subscheme isomorphic to the one cut out by
`I`, compatibly with the inclusions into `X ×_S T`. -/
private theorem comap_subschemeι_comp {T : Over S}
    (I : ((Over.pullback T.hom).obj X).left.IdealSheafData) :
    (I.comap (familyAmbientMap (restrictOverι X U) T)).subschemeι ≫
        familyAmbientMap (restrictOverι X U) T =
      ((I.comapIso (familyAmbientMap (restrictOverι X U) T)).hom ≫
        pullback.snd (familyAmbientMap (restrictOverι X U) T) I.subschemeι) ≫ I.subschemeι := by
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
    pullback.condition]

/-- A degree-`d` Hilbert family in `X` supported in an open `U` restricts to a degree-`d` Hilbert
family in `U`: its ideal sheaf is pulled back along the open immersion `U ×_S T ⟶ X ×_S T`. -/
def HilbertFamily.restrictOpen {T : Over S} (Z : HilbertFamily X T d) (hZ : Z.SupportedIn U) :
    HilbertFamily (restrictOver X U) T d where
  ideal := Z.ideal.comap (familyAmbientMap (restrictOverι X U) T)
  isFiniteLocallyFreeOfRank := by
    have := isIso_pullback_snd_of_supportedIn (U := U) Z.ideal hZ
    refine isFiniteLocallyFreeOfRank_of_iso
      (Z.ideal.comapIso _ ≪≫ asIso (pullback.snd _ Z.ideal.subschemeι)) ?_
      Z.isFiniteLocallyFreeOfRank
    simp only [Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, ← comap_subschemeι_comp, Category.assoc, familyAmbientMap_hom]

/-- The ideal sheaf of the restriction of a family to `U ×_S T` is the pullback of its ideal
sheaf along `U ×_S T ⟶ X ×_S T`. -/
theorem HilbertFamily.restrictOpen_ideal {T : Over S} (Z : HilbertFamily X T d)
    (hZ : Z.SupportedIn U) :
    (Z.restrictOpen hZ).ideal = Z.ideal.comap (familyAmbientMap (restrictOverι X U) T) :=
  rfl

variable (X d U) in
/-- Every degree-`d` Hilbert family in an open `U ⊆ X` is closed in `X ×_S T`: the composite of its
inclusion into `U ×_S T` with the open immersion `U ×_S T ⟶ X ×_S T` is a closed immersion. -/
class ClosedInAmbient : Prop where
  /-- The composite of the inclusion of a family in `U ×_S T` with `U ×_S T ⟶ X ×_S T` is a
  closed immersion. -/
  isClosedImmersion : ∀ {T : Over S} (Z : HilbertFamily (restrictOver X U) T d),
    IsClosedImmersion (Z.ideal.subschemeι ≫ familyAmbientMap (restrictOverι X U) T)

/-- The composite of the inclusion of a degree-`d` family in `U ×_S T` with the open immersion
`U ×_S T ⟶ X ×_S T` is a closed immersion. -/
instance HilbertFamily.isClosedImmersion_subschemeι_familyAmbientMap [ClosedInAmbient X d U]
    {T : Over S} (Z : HilbertFamily (restrictOver X U) T d) :
    IsClosedImmersion (Z.ideal.subschemeι ≫ familyAmbientMap (restrictOverι X U) T) :=
  ClosedInAmbient.isClosedImmersion Z

/-- The composite of the inclusion of a degree-`d` family in `U ×_S T` with the open immersion
`U ×_S T ⟶ X ×_S T` is a closed immersion, when `X ⟶ S` is separated. -/
instance closedInAmbient_of_isSeparated [IsSeparated X.hom] : ClosedInAmbient X d U where
  isClosedImmersion {T} Z := by
    have : UniversallyClosed ((Z.ideal.subschemeι ≫ familyAmbientMap (restrictOverι X U) T) ≫
        ((Over.pullback T.hom).obj X).hom) := by
      rw [Category.assoc, familyAmbientMap_hom]
      exact inferInstanceAs (UniversallyClosed Z.structural)
    have : IsSeparated ((Over.pullback T.hom).obj X).hom :=
      inferInstanceAs (IsSeparated (pullback.snd X.hom T.hom))
    have : UniversallyClosed (Z.ideal.subschemeι ≫ familyAmbientMap (restrictOverι X U) T) :=
      .of_comp_of_isSeparated _ ((Over.pullback T.hom).obj X).hom
    exact .of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range

/-- The ideal sheaf pushed forward from `U ×_S T` is the kernel of the composite closed
immersion. -/
private theorem map_eq_ker {T : Over S}
    (J : ((Over.pullback T.hom).obj (restrictOver X U)).left.IdealSheafData) :
    J.map (familyAmbientMap (restrictOverι X U) T) =
      (J.subschemeι ≫ familyAmbientMap (restrictOverι X U) T).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]

/-- The comparison between the closed subscheme cut out by a family in `U ×_S T` and the one cut
out by its pushforward to `X ×_S T`. -/
private def extendOpenLift [ClosedInAmbient X d U] {T : Over S}
    (Z : HilbertFamily (restrictOver X U) T d) :
    (Z.ideal.map (familyAmbientMap (restrictOverι X U) T)).subscheme ⟶ Z.ideal.subscheme :=
  IsClosedImmersion.lift (Z.ideal.subschemeι ≫ familyAmbientMap (restrictOverι X U) T)
    (Z.ideal.map (familyAmbientMap (restrictOverι X U) T)).subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, map_eq_ker])

private instance isIso_extendOpenLift [ClosedInAmbient X d U] {T : Over S}
    (Z : HilbertFamily (restrictOver X U) T d) : IsIso (extendOpenLift Z) :=
  IsClosedImmersion.isIso_lift _ _ (by rw [Scheme.IdealSheafData.ker_subschemeι, map_eq_ker])

@[reassoc]
private theorem extendOpenLift_fac [ClosedInAmbient X d U] {T : Over S}
    (Z : HilbertFamily (restrictOver X U) T d) :
    extendOpenLift Z ≫ Z.ideal.subschemeι ≫ familyAmbientMap (restrictOverι X U) T =
      (Z.ideal.map (familyAmbientMap (restrictOverι X U) T)).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-- A degree-`d` Hilbert family in an open `U ⊆ X` is a degree-`d` Hilbert family in `X`, when
families in `U` are closed in `X ×_S T` (for instance when `X ⟶ S` is separated): its ideal sheaf
is pushed forward along `U ×_S T ⟶ X ×_S T`. -/
def HilbertFamily.extendOpen [ClosedInAmbient X d U] {T : Over S}
    (Z : HilbertFamily (restrictOver X U) T d) : HilbertFamily X T d where
  ideal := Z.ideal.map (familyAmbientMap (restrictOverι X U) T)
  isFiniteLocallyFreeOfRank := by
    refine isFiniteLocallyFreeOfRank_of_iso (asIso (extendOpenLift Z)) ?_
      Z.isFiniteLocallyFreeOfRank
    rw [asIso_hom, ← extendOpenLift_fac_assoc, familyAmbientMap_hom]

/-- The pushforward of a family in `U` is supported in `U`. -/
theorem HilbertFamily.extendOpen_supportedIn [ClosedInAmbient X d U] {T : Over S}
    (Z : HilbertFamily (restrictOver X U) T d) : Z.extendOpen.SupportedIn U := by
  intro z
  change familyProjection X T ((Z.ideal.map _).subschemeι z) ∈ U
  rw [← extendOpenLift_fac]
  exact familyProjection_familyAmbientMap_restrictOverι_mem _

/-- Restricting the pushforward of a family in `U` gives back the family. -/
theorem HilbertFamily.restrictOpen_extendOpen [ClosedInAmbient X d U] {T : Over S}
    (Z : HilbertFamily (restrictOver X U) T d) :
    Z.extendOpen.restrictOpen Z.extendOpen_supportedIn = Z := by
  ext1
  set j := familyAmbientMap (restrictOverι X U) T
  have sq : IsPullback Z.ideal.subschemeι (𝟙 _) j (Z.ideal.subschemeι ≫ j) := by
    simpa using (IsPullback.of_vert_isIso (fst := Z.ideal.subschemeι) (snd := 𝟙 _)
      (f := 𝟙 _) (g := Z.ideal.subschemeι) ⟨by simp⟩).paste_horiz
      (IsKernelPair.id_of_mono j)
  change (Z.ideal.map j).comap j = Z.ideal
  rw [map_eq_ker, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← sq.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- Pushing forward the restriction of a family supported in `U` gives back the family. -/
theorem HilbertFamily.extendOpen_restrictOpen [ClosedInAmbient X d U] {T : Over S}
    (Z : HilbertFamily X T d) (hZ : Z.SupportedIn U) : (Z.restrictOpen hZ).extendOpen = Z := by
  ext1
  have := isIso_pullback_snd_of_supportedIn (U := U) Z.ideal hZ
  change (Z.ideal.comap _).map _ = Z.ideal
  rw [map_eq_ker, comap_subschemeι_comp, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

/-- Restriction to `U` commutes with base change. -/
theorem HilbertFamily.restrictOpen_baseChange {T' T : Over S} (g : T' ⟶ T)
    (Z : HilbertFamily X T d) (hZ : Z.SupportedIn U) :
    (baseChange X g Z).restrictOpen (hZ.baseChange g) =
      baseChange (restrictOver X U) g (Z.restrictOpen hZ) := by
  ext1
  simp only [HilbertFamily.restrictOpen_ideal, baseChange_ideal,
    ← Scheme.IdealSheafData.comap_comp, familyAmbientMap_familyBaseChangeMap]

/-- For every scheme `T` over `S`, the degree-`d` Hilbert families in `X` over `T` supported in an
open `U ⊆ X` correspond to the degree-`d` Hilbert families in `U` over `T`, when families in `U`
are closed in `X ×_S T` (for instance for `X ⟶ S` separated). -/
def supportedInEquiv [ClosedInAmbient X d U] (T : Over S) :
    {Z : HilbertFamily X T d // Z.SupportedIn U} ≃ HilbertFamily (restrictOver X U) T d where
  toFun Z := Z.1.restrictOpen Z.2
  invFun Z := ⟨Z.extendOpen, Z.extendOpen_supportedIn⟩
  left_inv Z := Subtype.ext (Z.1.extendOpen_restrictOpen Z.2)
  right_inv Z := Z.restrictOpen_extendOpen

/-- The natural isomorphism between the subfunctor of the degree-`d` Hilbert functor of `X`
consisting of the families supported in an open `U`, and the degree-`d` Hilbert functor of `U`,
when families in `U` are closed in `X ×_S T`, for instance for `X ⟶ S` separated. -/
def supportedInIso [ClosedInAmbient X d U] :
    (supportedIn X d U).toFunctor ≅ hilbertFunctorOfRank (restrictOver X U) d :=
  NatIso.ofComponents (fun T => (supportedInEquiv (U := U) T.unop).toIso) fun g => by
    ext Z
    exact HilbertFamily.restrictOpen_baseChange g.unop Z.1 Z.2

/-- A scheme representing the degree-`d` Hilbert functor of an open `U ⊆ X` represents the
subfunctor of families in `X` supported in `U`, when families in `U` are closed in `X ×_S T`,
for instance for `X ⟶ S` separated. -/
def supportedInRepresentableBy [ClosedInAmbient X d U] {H : Over S}
    (h : (hilbertFunctorOfRank (restrictOver X U) d).RepresentableBy H) :
    (supportedIn X d U).toFunctor.RepresentableBy H :=
  h.ofIso supportedInIso.symm

end Stacks.Hilbert

end
