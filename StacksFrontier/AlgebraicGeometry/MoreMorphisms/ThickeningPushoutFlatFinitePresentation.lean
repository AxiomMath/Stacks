module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Flatness and local finite presentation across a pushout along a thickening

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT].  A compatible triple
`T = (V, U', φ)` glues to a scheme `V ⨿_U U'` over `Y'` by the left adjoint of
[Stacks Project, Tag 07RV].  This file proves clauses (2) and (3) of
[Stacks Project, Tag 07RX] for that glued scheme: it is flat over `Y'` exactly when both
pieces are flat over `Y` and `X'`, and it is flat and locally of finite presentation exactly
when both pieces are.

## Main results

* `Stacks.Pushout.gluingFunctor_obj_flat_iff`: Tag 07RX, clause (2).
* `Stacks.Pushout.gluingFunctor_obj_flat_locallyOfFinitePresentation_iff`: Tag 07RX, clause (3).

## Implementation notes

Both properties are local on the target over affine opens and detected on the maps of sections,
by the very definition of `AlgebraicGeometry.Flat` and
`AlgebraicGeometry.LocallyOfFinitePresentation`.  So the whole content is the single affine
computation `Stacks.Pushout.appLE_properties_of_cube`: over an affine open `U` of `Y'` and an
affine open `V` of the glued scheme above it, the two squares of rings of sections are
cocartesian — this is the fourth assertion of Tag 07RT for the two pushout squares, fed through
`AlgebraicGeometry.isPushout_appLE_of_isPullback` — and the map of sections of the glued morphism
is, up to an isomorphism of arrows, the canonical map of [Stacks Project, Tag 08KQ], available
as `MilnorPatching.ringHom_properties_pullback_iff_and_flatAlgebra_equivalence`.

That lemma is stated for an abstract cube of schemes, exactly as
`Stacks.Pushout.isPullback_of_section_cube` is, so that it can be applied to the gluing
situation by the same list of arguments; and it concludes *both* ring-level properties at once,
each from its own hypotheses.  This is the one deviation from the draft proof, which obtained
flatness of the glued morphism from an equivalence of categories of flat algebras that is itself
proved from the flatness assertion.  Here the flatness clause uses the flatness half of Tag 08KQ
and therefore needs flatness of the two pieces only, with no finite-presentation hypothesis,
which is what the source asserts.

The easy direction of both equivalences is base change: the unit of the gluing adjunction is an
isomorphism, which is `Stacks.Pushout.gluingAdjunction_unit_app_isIso`, so each piece is a base
change of the glued scheme, and both properties are stable under base change.

*Nothing is assumed beyond the hypotheses of the source.*  [Stacks Project, Tag 06AD] — a
thickening of an affine scheme is affine — is taken from the library, where it is proved
unconditionally as `Stacks.Thickenings.forall_isAffine_of_isThickening`; the lemmas of Tag 07RT
reached from here take it as an explicit hypothesis, and every call below discharges it with that
theorem.  The existence of `Y' = Y ⨿_X X'` is not assumed either: it is the first assertion of
Tag 07RT, obtained from `hi` and the affineness of `f` by
`Stacks.Pushout.hasPushout_of_isThickening`, and the two main results bind that instance inside
their own types with `letI`, so that `pushout i f` is writable while only `hi` and the affineness
of `f` are hypotheses.  The private lemma `Stacks.Pushout.appLE_properties_of_gluing`, which is
not itself part of the statement of the tag, still takes `[HasPushout i f]` as an instance
argument because its own binders range over the opens of `pushout i f`; both call sites supply
that instance from `hi`.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-- A property of ring maps that respects isomorphisms is transported along an isomorphism of
arrows of `CommRingCat`. -/
private theorem transfer_arrow_iso
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.RespectsIso @P) {R₁ S₁ R₂ S₂ : CommRingCat.{u}}
    {m₁ : R₁ ⟶ S₁} {m₂ : R₂ ⟶ S₂} (e : Arrow.mk m₁ ≅ Arrow.mk m₂)
    (h : P m₁.hom) : P m₂.hom := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp hP
  exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty @P) e).mp h

/-- **The ring-level half of [Stacks Project, Tag 07RX].**  A map between the vertices of two
cartesian squares of rings which is compatible with the two projections, where the two horizontal
comparisons are cocartesian and the bottom map of the first square is surjective, is flat as soon
as the two comparisons are, and flat of finite presentation as soon as they are. -/
private theorem flat_and_finitePresentation_of_pullback_square
    {A A' B D C' C : CommRingCat.{u}}
    {toBase : B ⟶ A} {surjection : A' ⟶ A}
    {BtoD : B ⟶ D} {A'toC' : A' ⟶ C'} {AtoC : A ⟶ C} {DtoC : D ⟶ C} {C'toC : C' ⟶ C}
    (hD : IsPushout BtoD toBase DtoC AtoC)
    (hC' : IsPushout A'toC' surjection C'toC AtoC)
    (hsurj : Function.Surjective surjection.hom)
    {R₀ S₀ : CommRingCat.{u}} {pB : R₀ ⟶ B} {pA' : R₀ ⟶ A'} {pD : S₀ ⟶ D} {pC' : S₀ ⟶ C'}
    (hR : IsPullback pB pA' toBase surjection)
    (hS : IsPullback pD pC' DtoC C'toC)
    (m : R₀ ⟶ S₀) (hm₁ : m ≫ pD = pB ≫ BtoD) (hm₂ : m ≫ pC' = pA' ≫ A'toC') :
    (BtoD.hom.Flat → A'toC'.hom.Flat → m.hom.Flat) ∧
      ((BtoD.hom.Flat ∧ BtoD.hom.FinitePresentation) →
        (A'toC'.hom.Flat ∧ A'toC'.hom.FinitePresentation) →
          (m.hom.Flat ∧ m.hom.FinitePresentation)) := by
  let base : RingFibreProduct.Situation toBase.hom surjection.hom
      (RingHom.ker surjection.hom) := ⟨hsurj, rfl⟩
  have hDr : MilnorPatching.ringPushout BtoD.hom toBase.hom DtoC.hom AtoC.hom :=
    MilnorPatching.ringPushout_of_isPushout _ _ _ _ hD
  have hC'r : MilnorPatching.ringPushout A'toC'.hom surjection.hom C'toC.hom AtoC.hom :=
    MilnorPatching.ringPushout_of_isPushout _ _ _ _ hC'
  obtain ⟨-, hflat, hfp, -, -, -, -⟩ :=
    MilnorPatching.ringHom_properties_pullback_iff_and_flatAlgebra_equivalence
      toBase.hom surjection.hom (RingHom.ker surjection.hom) base
      BtoD.hom A'toC'.hom AtoC.hom DtoC.hom C'toC.hom hDr hC'r
  let toD' : base.fibreProduct →+* RingHom.pullback DtoC.hom C'toC.hom :=
    RingHom.codRestrict ((BtoD.hom.comp base.pullbackCone.fst.hom).prod
        (A'toC'.hom.comp base.pullbackCone.snd.hom))
      (RingHom.pullback DtoC.hom C'toC.hom) (fun x ↦ by
        show DtoC.hom (BtoD.hom (base.pullbackCone.fst.hom x)) =
          C'toC.hom (A'toC'.hom (base.pullbackCone.snd.hom x))
        have hd : DtoC.hom.comp BtoD.hom = AtoC.hom.comp toBase.hom :=
          MilnorPatching.ringPushout_comm hDr
        have hc : C'toC.hom.comp A'toC'.hom = AtoC.hom.comp surjection.hom :=
          MilnorPatching.ringPushout_comm hC'r
        calc
          _ = AtoC.hom (toBase.hom (base.pullbackCone.fst.hom x)) :=
            DFunLike.congr_fun hd (base.pullbackCone.fst.hom x)
          _ = AtoC.hom (surjection.hom (base.pullbackCone.snd.hom x)) :=
            congrArg AtoC.hom (DFunLike.congr_fun
              (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
          _ = _ := (DFunLike.congr_fun hc (base.pullbackCone.snd.hom x)).symm)
  have hR₀ := IsPullback.of_isLimit base.pullbackConeIsLimit
  have hS₀ := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit DtoC C'toC)
  let eR := hR.isoIsPullback B A' hR₀
  let eS := hS.isoIsPullback D C' hS₀
  have heRfst : eR.hom ≫ base.pullbackCone.fst = pB := hR.isoIsPullback_hom_fst B A' hR₀
  have heRsnd : eR.hom ≫ base.pullbackCone.snd = pA' := hR.isoIsPullback_hom_snd B A' hR₀
  have heSfst : eS.hom ≫ (CommRingCat.pullbackCone DtoC C'toC).fst = pD :=
    hS.isoIsPullback_hom_fst D C' hS₀
  have heSsnd : eS.hom ≫ (CommRingCat.pullbackCone DtoC C'toC).snd = pC' :=
    hS.isoIsPullback_hom_snd D C' hS₀
  let mD : base.pullbackCone.pt ⟶ (CommRingCat.pullbackCone DtoC C'toC).pt :=
    CommRingCat.ofHom toD'
  have htoDfst : mD ≫ (CommRingCat.pullbackCone DtoC C'toC).fst =
      base.pullbackCone.fst ≫ BtoD :=
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)
  have htoDsnd : mD ≫ (CommRingCat.pullbackCone DtoC C'toC).snd =
      base.pullbackCone.snd ≫ A'toC' :=
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)
  have hcomm : eR.hom ≫ mD = m ≫ eS.hom := by
    apply hS₀.hom_ext
    · rw [Category.assoc, Category.assoc, htoDfst, heSfst, ← Category.assoc, heRfst, hm₁]
    · rw [Category.assoc, Category.assoc, htoDsnd, heSsnd, ← Category.assoc, heRsnd, hm₂]
  have hArrow : Arrow.mk mD ≅ Arrow.mk m := by
    refine Arrow.isoMk eR.symm eS.symm ?_
    show eR.inv ≫ m = mD ≫ eS.inv
    apply (cancel_epi eR.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hF := transfer_arrow_iso (fun f ↦ f.Flat) RingHom.Flat.respectsIso hArrow
  refine ⟨fun hfD hfC' ↦ hF (hflat.mpr ⟨hfD, hfC'⟩), fun hfD hfC' ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hfp.mpr ⟨hfD, hfC'⟩
  exact ⟨hF h₁, transfer_arrow_iso (fun f ↦ f.FinitePresentation)
    RingHom.finitePresentation_respectsIso hArrow h₂⟩

/-- **The affine computation behind [Stacks Project, Tag 07RX].**  For a cube of schemes whose
two horizontal faces have cartesian squares of sections over every open, whose two vertical faces
are cartesian and whose back face is a closed immersion, the map of sections of the front
morphism over an affine open and an affine open above it is flat, respectively flat of finite
presentation, as soon as the two vertical morphisms of the front face are. -/
private theorem appLE_properties_of_cube
    {X X' Y P Q Q' R Z : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ P) (b : Y ⟶ P)
    (j : Q ⟶ Q') (g : Q ⟶ R) (c : Q' ⟶ Z) (d : R ⟶ Z)
    (z : Q ⟶ X) (w : Q' ⟶ X') (v : R ⟶ Y) (m : Z ⟶ P)
    [IsClosedImmersion i] [IsAffineHom f] [IsAffineHom g]
    [IsAffineHom a] [IsAffineHom b] [IsAffineHom c] [IsAffineHom d]
    (hRcomm : i ≫ a = f ≫ b) (hPcomm : j ≫ c = g ≫ d)
    (hRsec : ∀ S : P.Opens, IsPullback (b.app S) (a.app S) (f.app (b ⁻¹ᵁ S))
      (i.app (a ⁻¹ᵁ S) ≫ eqToHom (congrArg (fun V : X.Opens ↦ Γ(X, V))
        (congrArg (fun k : X ⟶ P ↦ k ⁻¹ᵁ S) hRcomm))))
    (hPsec : ∀ S : Z.Opens, IsPullback (d.app S) (c.app S) (g.app (d ⁻¹ᵁ S))
      (j.app (c ⁻¹ᵁ S) ≫ eqToHom (congrArg (fun V : Q.Opens ↦ Γ(Q, V))
        (congrArg (fun k : Q ⟶ Z ↦ k ⁻¹ᵁ S) hPcomm))))
    (hv : IsPullback g z v f) (hw : IsPullback j z w i)
    (hmd : d ≫ m = v ≫ b) (hmc : c ≫ m = w ≫ a)
    {U : P.Opens} (hU : IsAffineOpen U) {V : Z.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ m ⁻¹ᵁ U) :
    (Flat v → Flat w → (m.appLE U V hVU).hom.Flat) ∧
      ((Flat v ∧ LocallyOfFinitePresentation v) →
        (Flat w ∧ LocallyOfFinitePresentation w) →
          ((m.appLE U V hVU).hom.Flat ∧ (m.appLE U V hVU).hom.FinitePresentation)) := by
  have hiS : i ⁻¹ᵁ (a ⁻¹ᵁ U) = f ⁻¹ᵁ (b ⁻¹ᵁ U) :=
    congrArg (fun k : X ⟶ P ↦ k ⁻¹ᵁ U) hRcomm
  have hjT : j ⁻¹ᵁ (c ⁻¹ᵁ V) = g ⁻¹ᵁ (d ⁻¹ᵁ V) :=
    congrArg (fun k : Q ⟶ Z ↦ k ⁻¹ᵁ V) hPcomm
  -- The map on sections over an open whose inverse image is a given open is the map on sections
  -- over the whole inverse image, transported along that equality of opens.  The base states
  -- this privately in `ThickeningPushoutGluing` and in `Pushout.QuasiFiniteFunctoriality`; it is
  -- Mathlib's `Scheme.Hom.appLE_eq_app` once the two opens are identified.
  have happ : ∀ {A B : Scheme.{u}} (k : A ⟶ B) (W : B.Opens) (W' : A.Opens)
      (hW : k ⁻¹ᵁ W = W'),
      k.appLE W W' hW.ge = k.app W ≫ eqToHom (congrArg (fun T : A.Opens ↦ Γ(A, T)) hW) := by
    rintro A B k W W' rfl
    simp [Scheme.Hom.appLE_eq_app]
  have hle : ∀ {S T : Scheme.{u}} (k : S ⟶ Z) (k' : S ⟶ T) (p : T ⟶ P), k ≫ m = k' ≫ p →
      k ⁻¹ᵁ V ≤ k' ⁻¹ᵁ (p ⁻¹ᵁ U) := fun k k' p h ↦ by
    calc
      k ⁻¹ᵁ V ≤ k ⁻¹ᵁ (m ⁻¹ᵁ U) := k.preimage_mono hVU
      _ = _ := by simp only [← Scheme.Hom.comp_preimage, h]
  have hVR : d ⁻¹ᵁ V ≤ v ⁻¹ᵁ (b ⁻¹ᵁ U) := hle d v b hmd
  have hVQ' : c ⁻¹ᵁ V ≤ w ⁻¹ᵁ (a ⁻¹ᵁ U) := hle c w a hmc
  have hVQ : g ⁻¹ᵁ (d ⁻¹ᵁ V) ≤ z ⁻¹ᵁ (f ⁻¹ᵁ (b ⁻¹ᵁ U)) := by
    calc
      g ⁻¹ᵁ (d ⁻¹ᵁ V) ≤ g ⁻¹ᵁ (v ⁻¹ᵁ (b ⁻¹ᵁ U)) := g.preimage_mono hVR
      _ = _ := congrArg (fun k : Q ⟶ Y ↦ k ⁻¹ᵁ (b ⁻¹ᵁ U)) hv.w
  have hUY : IsAffineOpen (b ⁻¹ᵁ U) := hU.preimage b
  have hUX' : IsAffineOpen (a ⁻¹ᵁ U) := hU.preimage a
  have hUX : IsAffineOpen (f ⁻¹ᵁ (b ⁻¹ᵁ U)) := hUY.preimage f
  have hVRa : IsAffineOpen (d ⁻¹ᵁ V) := hV.preimage d
  have hVQ'a : IsAffineOpen (c ⁻¹ᵁ V) := hV.preimage c
  -- the two cocartesian squares of rings of sections
  have hPushL := isPushout_appLE_of_isPullback hv (V := b ⁻¹ᵁ U)
    (U := d ⁻¹ᵁ V) (V' := f ⁻¹ᵁ (b ⁻¹ᵁ U)) (U' := g ⁻¹ᵁ (d ⁻¹ᵁ V))
    hUY hVRa hVR hUX le_rfl (le_antisymm (le_inf le_rfl hVQ) inf_le_left)
  have hPushR := isPushout_appLE_of_isPullback hw (V := a ⁻¹ᵁ U)
    (U := c ⁻¹ᵁ V) (V' := f ⁻¹ᵁ (b ⁻¹ᵁ U)) (U' := g ⁻¹ᵁ (d ⁻¹ᵁ V))
    hUX' hVQ'a hVQ' hUX hiS.ge
    (by
      have h : j ⁻¹ᵁ (c ⁻¹ᵁ V) ≤ z ⁻¹ᵁ (f ⁻¹ᵁ (b ⁻¹ᵁ U)) := hjT ▸ hVQ
      rw [← hjT]
      exact le_antisymm (le_inf le_rfl h) inf_le_left)
  -- the two cartesian squares of rings of sections
  have hRsq : IsPullback (b.app U) (a.app U)
      (f.appLE (b ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) le_rfl)
      (i.appLE (a ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) hiS.ge) := by
    rw [happ i _ _ hiS, Scheme.Hom.appLE_eq_app]
    exact hRsec U
  have hPsq : IsPullback (d.app V) (c.app V)
      (g.appLE (d ⁻¹ᵁ V) (g ⁻¹ᵁ (d ⁻¹ᵁ V)) le_rfl)
      (j.appLE (c ⁻¹ᵁ V) (g ⁻¹ᵁ (d ⁻¹ᵁ V)) hjT.ge) := by
    rw [happ j _ _ hjT, Scheme.Hom.appLE_eq_app]
    exact hPsec V
  -- surjectivity of the bottom map of the first square
  have hsurj : Function.Surjective
      (i.appLE (a ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) hiS.ge).hom := by
    have : IsAffine (a ⁻¹ᵁ U).toScheme := hUX'
    have : IsAffine (f ⁻¹ᵁ (b ⁻¹ᵁ U)).toScheme := hUX
    have hir : IsPullback (i.resLE (a ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) hiS.ge)
        (f ⁻¹ᵁ (b ⁻¹ᵁ U)).ι (a ⁻¹ᵁ U).ι i := by
      apply IsOpenImmersion.isPullback
      · exact (Scheme.Hom.resLE_comp_ι _ _).symm
      · simpa using hiS
    have : IsClosedImmersion (i.resLE (a ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) hiS.ge) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hir.flip inferInstance
    exact transfer_arrow_iso (fun k ↦ Function.Surjective k) RingHom.surjective_respectsIso
      (arrowResLEAppIso i (a ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) hiS.ge)
      (IsClosedImmersion.isAffine_surjective_of_isAffine
        (i.resLE (a ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) hiS.ge)).2
  -- the comparison of the two vertices
  have hm₁ : m.appLE U V hVU ≫ d.app V =
      b.app U ≫ v.appLE (b ⁻¹ᵁ U) (d ⁻¹ᵁ V) hVR := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hmd]
  have hm₂ : m.appLE U V hVU ≫ c.app V =
      a.app U ≫ w.appLE (a ⁻¹ᵁ U) (c ⁻¹ᵁ V) hVQ' := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hmc]
  obtain ⟨key₁, key₂⟩ := flat_and_finitePresentation_of_pullback_square hPushL hPushR hsurj
    hRsq hPsq (m.appLE U V hVU) hm₁ hm₂
  refine ⟨fun hfv hfw ↦ key₁ (hfv.flat_appLE hUY hVRa hVR) (hfw.flat_appLE hUX' hVQ'a hVQ'),
    fun hpv hpw ↦ key₂ ⟨hpv.1.flat_appLE hUY hVRa hVR,
      hpv.2.finitePresentation_appLE hUY hVRa hVR⟩
      ⟨hpw.1.flat_appLE hUX' hVQ'a hVQ', hpw.2.finitePresentation_appLE hUX' hVQ'a hVQ'⟩⟩

/-- Both pieces of a compatible triple inherit from the glued scheme any property of morphisms
of schemes that is stable under base change: each piece is a base change of the glued scheme
along `Y ⟶ Y'`, respectively `X' ⟶ Y'`, because the unit of the gluing adjunction is an
isomorphism. -/
private theorem pieces_of_glued {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f]
    (T : gluingData i f) {Pr : MorphismProperty Scheme.{u}}
    (hPr : Pr.IsStableUnderBaseChange)
    (h : Pr ((gluingFunctor i f hi).obj T).hom) :
    Pr T.obj.left.hom ∧ Pr T.obj.right.hom := by
  let := hasPushout_of_isThickening i f hi
  have := hPr
  have := hPr.respectsIso
  have : IsIso ((gluingAdjunction i f hi).unit.app T) :=
    gluingAdjunction_unit_app_isIso i f hi T
  let e := asIso ((gluingAdjunction i f hi).unit.app T)
  let Fl : gluingData i f ⥤ Over Y :=
    (show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from
      fun Z ↦ IsIso Z.hom).ι ⋙ Comma.fst _ _
  let Fr : gluingData i f ⥤ Over X' :=
    (show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from
      fun Z ↦ IsIso Z.hom).ι ⋙ Comma.snd _ _
  exact ⟨(MorphismProperty.over_iso_iff Pr (Fl.mapIso e)).mpr
      (MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback ((gluingFunctor i f hi).obj T).hom (pushout.inr i f)) h),
    (MorphismProperty.over_iso_iff Pr (Fr.mapIso e)).mpr
      (MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback ((gluingFunctor i f hi).obj T).hom (pushout.inl i f)) h)⟩

/-- The first inclusion of the pushout of a thickening along an affine morphism is affine. -/
private theorem isAffineHom_pushout_inl {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    [IsClosedImmersion (pushout.inr i f)] : IsAffineHom (pushout.inl i f) := by
  have : IsAffineHom (i ≫ pushout.inl i f) := by
    rw [pushout.condition]
    infer_instance
  exact isAffineHom_of_isThickening_comp forall_isAffine_of_isThickening i _ hi

/-- The cube of schemes to which `Stacks.Pushout.appLE_properties_of_cube` is applied: the two
pushout squares of Tag 07RT, the one defining `Y'` and the one defining the glued scheme. -/
private theorem appLE_properties_of_gluing {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    {U : (pushout i f).Opens} (hU : IsAffineOpen U)
    {V : (pushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)).Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ (gluingPushoutData i f T).hom ⁻¹ᵁ U) :
    (Flat T.obj.left.hom → Flat T.obj.right.hom →
        ((gluingPushoutData i f T).hom.appLE U V hVU).hom.Flat) ∧
      ((Flat T.obj.left.hom ∧ LocallyOfFinitePresentation T.obj.left.hom) →
        (Flat T.obj.right.hom ∧ LocallyOfFinitePresentation T.obj.right.hom) →
          (((gluingPushoutData i f T).hom.appLE U V hVU).hom.Flat ∧
            ((gluingPushoutData i f T).hom.appLE U V hVU).hom.FinitePresentation)) := by
  have : IsClosedImmersion i := hi.1
  have hj : IsThickening (pullback.fst T.obj.right.hom i) :=
    isThickening_of_isPullback (IsPullback.of_hasPullback T.obj.right.hom i) hi
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  have : IsClosedImmersion
      (pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)) :=
    (gluing_inr_isThickening i f hi T).1
  let : IsAffineHom (gluingSourceMap i f T) :=
    MorphismProperty.of_isPullback (gluingSourceMap_isPullback i f T).flip inferInstance
  have := isAffineHom_pushout_inl i f hi
  have := isAffineHom_pushout_inl _ (gluingSourceMap i f T) hj
  exact appLE_properties_of_cube i f (pushout.inl i f) (pushout.inr i f)
    (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)
    (pushout.inl _ _) (pushout.inr _ _)
    (pullback.snd T.obj.right.hom i) T.obj.right.hom T.obj.left.hom
    (gluingPushoutData i f T).hom
    pushout.condition pushout.condition
    (pushout_structureSheaf_isPullback forall_isAffine_of_isThickening i f hi)
    (pushout_structureSheaf_isPullback forall_isAffine_of_isThickening _ _ hj)
    (gluingSourceMap_isPullback i f T) (IsPullback.of_hasPullback T.obj.right.hom i)
    (gluingPushoutData_inr i f T) (gluingPushoutData_inl i f T) hU hV hVU

/-- **[Stacks Project, Tag 07RX], clause (2).**  The scheme glued from a compatible triple is
flat over the pushout `Y' = Y ⨿_X X'` exactly when both of its pieces are flat over `Y` and
over `X'`. -/
theorem gluingFunctor_obj_flat_iff {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f]
    (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    Flat ((gluingFunctor i f hi).obj T).hom ↔
      (Flat T.obj.left.hom ∧ Flat T.obj.right.hom) := by
  let := hasPushout_of_isThickening i f hi
  let : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) :=
    gluingHasPushout i f hi T
  refine ⟨pieces_of_glued i f hi T Flat.isStableUnderBaseChange, fun ⟨hl, hr⟩ ↦ ?_⟩
  show Flat (gluingPushoutData i f T).hom
  constructor
  intro U hU V hV hVU
  exact (appLE_properties_of_gluing i f hi T hU hV hVU).1 hl hr

/-- **[Stacks Project, Tag 07RX], clause (3).**  The scheme glued from a compatible triple is
flat and locally of finite presentation over the pushout `Y' = Y ⨿_X X'` exactly when both of its
pieces are flat and locally of finite presentation over `Y` and over `X'`. -/
theorem gluingFunctor_obj_flat_locallyOfFinitePresentation_iff {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f]
    (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    (Flat ((gluingFunctor i f hi).obj T).hom ∧
        LocallyOfFinitePresentation ((gluingFunctor i f hi).obj T).hom) ↔
      ((Flat T.obj.left.hom ∧ LocallyOfFinitePresentation T.obj.left.hom) ∧
        (Flat T.obj.right.hom ∧ LocallyOfFinitePresentation T.obj.right.hom)) := by
  let := hasPushout_of_isThickening i f hi
  let : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) :=
    gluingHasPushout i f hi T
  constructor
  · rintro ⟨hflat, hlfp⟩
    obtain ⟨hlf, hrf⟩ := pieces_of_glued i f hi T Flat.isStableUnderBaseChange hflat
    obtain ⟨hlp, hrp⟩ := pieces_of_glued i f hi T
      locallyOfFinitePresentation_isStableUnderBaseChange hlfp
    exact ⟨⟨hlf, hlp⟩, ⟨hrf, hrp⟩⟩
  · rintro ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · show Flat (gluingPushoutData i f T).hom
      constructor
      intro U hU V hV hVU
      exact ((appLE_properties_of_gluing i f hi T hU hV hVU).2 hl hr).1
    · show LocallyOfFinitePresentation (gluingPushoutData i f T).hom
      constructor
      intro U hU V hV hVU
      exact ((appLE_properties_of_gluing i f hi T hU hV hVU).2 hl hr).2

end Stacks.Pushout

end
