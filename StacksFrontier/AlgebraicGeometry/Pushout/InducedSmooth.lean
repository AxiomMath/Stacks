module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.InducedMorphism
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Smoothness and étaleness of a morphism between pushouts

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be closed immersions, let `f : X' ⟶ X` and `g : Y' ⟶ Y` be
morphisms, and let the two inverse images of `Z` be identified over `Z`.  The glued source
`X' ⨿ Y'` then maps to `Y ⨿_Z X`, and this file shows that the induced morphism is smooth, resp.
étale, exactly when `f` and `g` are.

## Main results

* `AlgebraicGeometry.smooth_induced_iff`: the induced morphism of pushouts is smooth if and only
  if the morphisms on the two pieces are smooth.
* `AlgebraicGeometry.etale_induced_iff`: the induced morphism of pushouts is étale if and only if
  the morphisms on the two pieces are étale.

## Implementation notes

The two clauses differ only in which component of the Milnor patching theorem of
[Stacks Project, Tag 08KQ] they invoke, so the geometry is carried out once for an arbitrary
property of ring maps that is invariant under isomorphism and detected on the two base changes of
a Milnor patching square.

## References

* [Stacks Project, Tag 0CYY](https://stacks.math.columbia.edu/tag/0CYY)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-! ### A property of ring maps glued along a Milnor patching square -/

/-- The canonical map from a ring fibre product `B ×_A A'` to the fibre product of the two base
changes `D` and `C'` over `C`, in the situation of [Stacks Project, Tag 08KQ]. -/
private def fibreProductToPullback
    {A A' B D C' C : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing D] [CommRing C'] [CommRing C]
    {toBase : B →+* A} {surjection : A' →+* A}
    (base : RingFibreProduct.Situation toBase surjection (RingHom.ker surjection))
    {BtoD : B →+* D} {A'toC' : A' →+* C'} {AtoC : A →+* C}
    {DtoC : D →+* C} {C'toC : C' →+* C}
    (hD : MilnorPatching.ringPushout BtoD toBase DtoC AtoC)
    (hC' : MilnorPatching.ringPushout A'toC' surjection C'toC AtoC) :
    base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
  RingHom.codRestrict
    ((BtoD.comp base.pullbackCone.fst.hom).prod (A'toC'.comp base.pullbackCone.snd.hom))
    (RingHom.pullback DtoC C'toC) (fun x ↦ by
      change DtoC (BtoD (base.pullbackCone.fst.hom x)) =
        C'toC (A'toC' (base.pullbackCone.snd.hom x))
      calc
        _ = AtoC (toBase (base.pullbackCone.fst.hom x)) :=
          DFunLike.congr_fun (MilnorPatching.ringPushout_comm hD) (base.pullbackCone.fst.hom x)
        _ = AtoC (surjection (base.pullbackCone.snd.hom x)) := congrArg AtoC
          (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
        _ = _ := (DFunLike.congr_fun (MilnorPatching.ringPushout_comm hC')
          (base.pullbackCone.snd.hom x)).symm)

/-- A property of ring maps is *glued on Milnor patching squares* if, for a ring fibre product
`B ×_A A'` with `A' → A` surjective and two compatible Milnor patching squares on it, the
canonical map to the fibre product of the base changes has the property exactly when both base
changes do. -/
private def GluedOnMilnorPatching
    (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {A A' B D C' C : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing D] [CommRing C'] [CommRing C]
    {toBase : B →+* A} {surjection : A' →+* A}
    (base : RingFibreProduct.Situation toBase surjection (RingHom.ker surjection))
    {BtoD : B →+* D} {A'toC' : A' →+* C'} {AtoC : A →+* C}
    {DtoC : D →+* C} {C'toC : C' →+* C}
    (hD : MilnorPatching.ringPushout BtoD toBase DtoC AtoC)
    (hC' : MilnorPatching.ringPushout A'toC' surjection C'toC AtoC),
    Q (fibreProductToPullback base hD hC') ↔ Q BtoD ∧ Q A'toC'

/-- Smoothness of ring maps is glued on Milnor patching squares, by
[Stacks Project, Tag 08KQ]. -/
private theorem gluedOnMilnorPatching_smooth : GluedOnMilnorPatching RingHom.Smooth := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ base _ _ _ _ _ hD hC'
  obtain ⟨-, -, -, hsmooth, -⟩ :=
    MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction _ _ _ base _ _ _ _ _ hD hC'
  exact hsmooth

/-- Étaleness of ring maps is glued on Milnor patching squares, by
[Stacks Project, Tag 08KQ]. -/
private theorem gluedOnMilnorPatching_etale : GluedOnMilnorPatching RingHom.Etale := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ base _ _ _ _ _ hD hC'
  obtain ⟨-, -, -, -, hetale, -⟩ :=
    MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction _ _ _ base _ _ _ _ _ hD hC'
  exact hetale

/-- A cartesian square of commutative rings identifies its vertex with the subring fibre product
`RingHom.pullback`. -/
private def ringEquivPullbackOfIsPullback
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (pA : R →+* A) (pB : R →+* B) (f : A →+* C) (g : B →+* C)
    (H : IsPullback (CommRingCat.ofHom pA) (CommRingCat.ofHom pB)
      (CommRingCat.ofHom f) (CommRingCat.ofHom g)) :
    R ≃+* RingHom.pullback f g :=
  (H.isLimit.conePointUniqueUpToIso
    (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom f)
      (CommRingCat.ofHom g))).commRingCatIsoToRingEquiv

/-- Two cartesian squares of commutative rings over the same Milnor patching data present a map
between their vertices as the canonical map of [Stacks Project, Tag 08KQ], up to isomorphism of
arrows. -/
private def arrowIsoFibreProductToPullback
    {A A' B D C' C R P : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing D] [CommRing C'] [CommRing C] [CommRing R] [CommRing P]
    {toBase : B →+* A} {surjection : A' →+* A}
    (base : RingFibreProduct.Situation toBase surjection (RingHom.ker surjection))
    {BtoD : B →+* D} {A'toC' : A' →+* C'} {AtoC : A →+* C}
    {DtoC : D →+* C} {C'toC : C' →+* C}
    (hD : MilnorPatching.ringPushout BtoD toBase DtoC AtoC)
    (hC' : MilnorPatching.ringPushout A'toC' surjection C'toC AtoC)
    {pB : R →+* B} {pA' : R →+* A'}
    (hR : IsPullback (CommRingCat.ofHom pB) (CommRingCat.ofHom pA')
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection))
    {qD : P →+* D} {qC' : P →+* C'}
    (hP : IsPullback (CommRingCat.ofHom qD) (CommRingCat.ofHom qC')
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom C'toC))
    (m : R →+* P) (hmD : qD.comp m = BtoD.comp pB) (hmC' : qC'.comp m = A'toC'.comp pA') :
    Arrow.mk (CommRingCat.ofHom m) ≅
      Arrow.mk (CommRingCat.ofHom (fibreProductToPullback base hD hC')) :=
  Arrow.isoMk (ringEquivPullbackOfIsPullback pB pA' toBase surjection hR).toCommRingCatIso
    (ringEquivPullbackOfIsPullback qD qC' DtoC C'toC hP).toCommRingCatIso <| by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun x ↦ Subtype.ext (Prod.ext ?_ ?_)
      · exact (DFunLike.congr_fun hmD x).symm
      · exact (DFunLike.congr_fun hmC' x).symm

/-- A map between the vertices of two cartesian squares of commutative rings over the same Milnor
patching data has a glued property exactly when both base changes do.  This is
[Stacks Project, Tag 08KQ] transported along the two identifications of a fibre product. -/
private theorem ringHom_iff_of_isPullback
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQiso : RingHom.RespectsIso Q) (hQglue : GluedOnMilnorPatching Q)
    {A A' B D C' C R P : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing D] [CommRing C'] [CommRing C] [CommRing R] [CommRing P]
    {toBase : B →+* A} {surjection : A' →+* A} (hsurj : Function.Surjective surjection)
    {BtoD : B →+* D} {A'toC' : A' →+* C'} {AtoC : A →+* C}
    {DtoC : D →+* C} {C'toC : C' →+* C}
    (hD : MilnorPatching.ringPushout BtoD toBase DtoC AtoC)
    (hC' : MilnorPatching.ringPushout A'toC' surjection C'toC AtoC)
    {pB : R →+* B} {pA' : R →+* A'}
    (hR : IsPullback (CommRingCat.ofHom pB) (CommRingCat.ofHom pA')
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection))
    {qD : P →+* D} {qC' : P →+* C'}
    (hP : IsPullback (CommRingCat.ofHom qD) (CommRingCat.ofHom qC')
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom C'toC))
    (m : R →+* P) (hmD : qD.comp m = BtoD.comp pB) (hmC' : qC'.comp m = A'toC'.comp pA') :
    Q m ↔ Q BtoD ∧ Q A'toC' :=
  let base : RingFibreProduct.Situation toBase surjection (RingHom.ker surjection) := ⟨hsurj, rfl⟩
  (hQiso.arrow_mk_iso_iff
      (arrowIsoFibreProductToPullback base hD hC' hR hP m hmD hmC')).trans
    (hQglue base hD hC')

/-! ### Sections of the two pushouts -/

/-- A cartesian square of schemes whose three given opens are affine induces a Milnor patching
square on sections. -/
private theorem ringPushout_appLE_of_isPullback
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f) {US : S.Opens} {UT : T.Opens} {UX : X.Opens}
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
    {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX) :
    MilnorPatching.ringPushout (iX.appLE US UX hUSX).hom (f.appLE US UT hUST).hom
      (g.appLE UX UY (by simp [*])).hom (iY.appLE UT UY (by simp [*])).hom :=
  MilnorPatching.ringPushout_of_isPushout _ _ _ _ <| (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX)

/-- The sections of the pushout of two closed immersions over an open form the fibre product of
the sections on the two pieces over the sections on the common closed subscheme.  This is the
last assertion of [Stacks Project, Tag 0E25] for the pushout of [Stacks Project, Tag 0B7M]. -/
private theorem pushout_sections_isPullback {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (U : (pushout i j).Opens)
    (e : i ⁻¹ᵁ (pushout.inl i j ⁻¹ᵁ U) = j ⁻¹ᵁ (pushout.inr i j ⁻¹ᵁ U)) :
    IsPullback ((pushout.inr i j).appLE U (pushout.inr i j ⁻¹ᵁ U) le_rfl)
      ((pushout.inl i j).appLE U (pushout.inl i j ⁻¹ᵁ U) le_rfl)
      (j.appLE (pushout.inr i j ⁻¹ᵁ U) (j ⁻¹ᵁ (pushout.inr i j ⁻¹ᵁ U)) le_rfl)
      (i.appLE (pushout.inl i j ⁻¹ᵁ U) (j ⁻¹ᵁ (pushout.inr i j ⁻¹ᵁ U)) e.ge) := by
  have h := structureSheaf_isPullback_of_isPushout_of_isAffineHom
    (IsPushout.of_hasPushout i j) U
  rw [← app_comp_eqToHom_eq_appLE i e e.ge]
  simpa only [Scheme.Hom.app_eq_appLE] using h

/-! ### The induced morphism on an affine chart -/

namespace CompatiblePushoutMorphismSituation

variable (S : CompatiblePushoutMorphismSituation.{u})

/-- An open of the glued source lying over an open of the target cuts out, on each piece, an open
lying over the corresponding piece of the target. -/
private theorem piece_le_preimage {U : (pushout S.i S.j).Opens} {V : S.sourcePushout.Opens}
    (e : V ≤ S.induced ⁻¹ᵁ U) :
    (pushout.inl S.toX' S.toY' ⁻¹ᵁ V ≤ S.f ⁻¹ᵁ (pushout.inl S.i S.j ⁻¹ᵁ U)) ∧
      (pushout.inr S.toX' S.toY' ⁻¹ᵁ V ≤ S.g ⁻¹ᵁ (pushout.inr S.i S.j ⁻¹ᵁ U)) := by
  constructor
  · intro x hx
    change (S.f ≫ pushout.inl S.i S.j) x ∈ U
    rw [← S.inl_comp_induced]
    exact e hx
  · intro y hy
    change (S.g ≫ pushout.inr S.i S.j) y ∈ U
    rw [← S.inr_comp_induced]
    exact e hy

/-- The second piece of the glued source is the fibre product of the second piece of the target
and the common closed subscheme. -/
private theorem isPullback_toY' :
    IsPullback S.toY' (pullback.snd S.f S.i) S.g S.j :=
  (IsPullback.of_hasPullback S.g S.j).of_iso' S.φ (Iso.refl _) (Iso.refl _) (Iso.refl _) rfl
    S.φ_over rfl rfl

/-- A property of ring maps that is glued on Milnor patching squares is detected, on the sections
over an affine chart of the induced morphism, by the sections of `f` and `g` over the two induced
charts. -/
private theorem appLE_induced_iff
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQiso : RingHom.RespectsIso Q) (hQglue : GluedOnMilnorPatching Q)
    {U : (pushout S.i S.j).Opens} {V : S.sourcePushout.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ S.induced ⁻¹ᵁ U)
    (eX : pushout.inl S.toX' S.toY' ⁻¹ᵁ V ≤ S.f ⁻¹ᵁ (pushout.inl S.i S.j ⁻¹ᵁ U))
    (eY : pushout.inr S.toX' S.toY' ⁻¹ᵁ V ≤ S.g ⁻¹ᵁ (pushout.inr S.i S.j ⁻¹ᵁ U)) :
    Q (S.induced.appLE U V e).hom ↔
      Q (S.f.appLE (pushout.inl S.i S.j ⁻¹ᵁ U)
          (pushout.inl S.toX' S.toY' ⁻¹ᵁ V) eX).hom ∧
        Q (S.g.appLE (pushout.inr S.i S.j ⁻¹ᵁ U)
          (pushout.inr S.toX' S.toY' ⁻¹ᵁ V) eY).hom := by
  set a := pushout.inl S.i S.j
  set b := pushout.inr S.i S.j
  set a' := pushout.inl S.toX' S.toY'
  set b' := pushout.inr S.toX' S.toY'
  set Ux := a ⁻¹ᵁ U
  set Uy := b ⁻¹ᵁ U
  set Vx := a' ⁻¹ᵁ V
  set Vy := b' ⁻¹ᵁ V
  set Uz := S.j ⁻¹ᵁ Uy
  set Vz := S.toY' ⁻¹ᵁ Vy
  have hUz : S.i ⁻¹ᵁ Ux = Uz :=
    congrArg (fun k : S.Z ⟶ pushout S.i S.j ↦ k ⁻¹ᵁ U) (IsPushout.of_hasPushout S.i S.j).w
  have hVz : S.toX' ⁻¹ᵁ Vx = Vz :=
    congrArg (fun k : S.intersection ⟶ S.sourcePushout ↦ k ⁻¹ᵁ V)
      (IsPushout.of_hasPushout S.toX' S.toY').w
  have hUx : IsAffineOpen Ux := hU.preimage a
  have hUy : IsAffineOpen Uy := hU.preimage b
  have hVx : IsAffineOpen Vx := hV.preimage a'
  have hVy : IsAffineOpen Vy := hV.preimage b'
  have hUzAff : IsAffineOpen Uz := hUy.preimage S.j
  set q := pullback.snd S.f S.i
  have eZ : Vz ≤ q ⁻¹ᵁ Uz := by
    intro z hz
    change S.j (q z) ∈ Uy
    rw [← Scheme.Hom.comp_apply, ← S.isPullback_toY'.w, Scheme.Hom.comp_apply]
    exact eY hz
  have hVzinf : Vz = S.toY' ⁻¹ᵁ Vy ⊓ q ⁻¹ᵁ Uz := (inf_eq_left.mpr eZ).symm
  have hVzinf' : Vz = S.toX' ⁻¹ᵁ Vx ⊓ q ⁻¹ᵁ Uz := by rw [hVz, ← hVzinf]
  have hD := ringPushout_appLE_of_isPullback S.isPullback_toY' (US := Uy) (UT := Uz)
    (UX := Vy) le_rfl eY hVzinf hUy hUzAff hVy
  have hC' := ringPushout_appLE_of_isPullback (IsPullback.of_hasPullback S.f S.i) (US := Ux)
    (UT := Uz) (UX := Vx) hUz.ge eX hVzinf' hUx hUzAff hVx
  have hR := pushout_sections_isPullback S.i S.j U hUz
  have hP := pushout_sections_isPullback S.toX' S.toY' V hVz
  have hsurj := appLE_surjective_of_isClosedImmersion S.i hUx hUz hUz.ge
  have hmD : (b'.appLE V Vy le_rfl).hom.comp (S.induced.appLE U V e).hom =
      (S.g.appLE Uy Vy eY).hom.comp (b.appLE U Uy le_rfl).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE, appLE_eq_appLE_of_eq S.inr_comp_induced]
  have hmC' : (a'.appLE V Vx le_rfl).hom.comp (S.induced.appLE U V e).hom =
      (S.f.appLE Ux Vx eX).hom.comp (a.appLE U Ux le_rfl).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE, appLE_eq_appLE_of_eq S.inl_comp_induced]
  exact (ringHom_iff_of_isPullback hQiso hQglue hsurj hD hC' hR hP _ hmD hmC').trans and_comm

/-- A property of morphisms of schemes coming from a property of ring maps that is glued on
Milnor patching squares holds for the induced morphism exactly when it holds for the morphisms on
the two pieces. -/
private theorem induced_iff_of_hasRingHomProperty
    (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] (hQsrc : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    (hQiso : RingHom.RespectsIso Q) (hQglue : GluedOnMilnorPatching Q) :
    P S.induced ↔ P S.f ∧ P S.g := by
  constructor
  · intro h
    rw [HasRingHomProperty.iff_exists_appLE (P := P) hQsrc] at h
    refine ⟨?_, ?_⟩
    · rw [HasRingHomProperty.iff_exists_appLE (P := P) hQsrc]
      intro x
      obtain ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, e, hring⟩ := h (pushout.inl S.toX' S.toY' x)
      obtain ⟨eX, eY⟩ := S.piece_le_preimage e
      exact ⟨⟨_, hU.preimage _⟩, ⟨_, hV.preimage _⟩, hxV, eX,
        ((S.appLE_induced_iff hQiso hQglue hU hV e eX eY).1 hring).1⟩
    · rw [HasRingHomProperty.iff_exists_appLE (P := P) hQsrc]
      intro y
      obtain ⟨⟨U, hU⟩, ⟨V, hV⟩, hyV, e, hring⟩ := h (pushout.inr S.toX' S.toY' y)
      obtain ⟨eX, eY⟩ := S.piece_le_preimage e
      exact ⟨⟨_, hU.preimage _⟩, ⟨_, hV.preimage _⟩, hyV, eY,
        ((S.appLE_induced_iff hQiso hQglue hU hV e eX eY).1 hring).2⟩
  · rintro ⟨hf, hg⟩
    rw [HasRingHomProperty.iff_appLE (P := P)] at hf hg ⊢
    rintro ⟨U, hU⟩ ⟨V, hV⟩ e
    obtain ⟨eX, eY⟩ := S.piece_le_preimage e
    exact (S.appLE_induced_iff hQiso hQglue hU hV e eX eY).2
      ⟨hf ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ eX, hg ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ eY⟩

end CompatiblePushoutMorphismSituation

/-! ### The two clauses -/

/-- In a compatible morphism of pushouts along closed immersions, the induced morphism is étale if
and only if the morphisms on both pieces are étale. -/
@[stacks 0CYY "etale"]
theorem etale_induced_iff (S : CompatiblePushoutMorphismSituation.{u}) :
    Etale S.induced ↔ (Etale S.f ∧ Etale S.g) :=
  S.induced_iff_of_hasRingHomProperty @Etale
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
        RingHom.Etale.containsIdentities)).1
    RingHom.Etale.respectsIso gluedOnMilnorPatching_etale

/-- In a compatible morphism of pushouts along closed immersions, the induced morphism is smooth
if and only if the morphisms on both pieces are smooth. -/
@[stacks 0CYY "smooth"]
theorem smooth_induced_iff (S : CompatiblePushoutMorphismSituation.{u}) :
    Smooth S.induced ↔ (Smooth S.f ∧ Smooth S.g) :=
  S.induced_iff_of_hasRingHomProperty @Smooth
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1
    RingHom.Smooth.propertyIsLocal.respectsIso gluedOnMilnorPatching_smooth

end AlgebraicGeometry

end
