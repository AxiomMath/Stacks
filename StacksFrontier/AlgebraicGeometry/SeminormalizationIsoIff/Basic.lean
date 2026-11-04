module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
public import StacksFrontier.AlgebraicGeometry.SeminormalizationIsoIff.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCube
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Initial

/-!
# Subintegral maps into a seminormal scheme are isomorphisms

A *subintegral* map is a universal homeomorphism inducing isomorphisms on all residue
fields; these are exactly the structure morphisms of the objects of
`AlgebraicGeometry.SeminormalizationCategory`.  The main result of this file is that a
subintegral map out of a reduced scheme into a seminormal scheme is an isomorphism.  Applied
to the canonical map out of the seminormalization it gives one of the two implications of
Stacks 0EUS: the canonical map from the seminormalization of `X` to a candidate `Y` is an
isomorphism as soon as `Y` is seminormal.

## Main results

* `AlgebraicGeometry.isIso_of_isSeminormal_target_of_universalHomeomorphism`: a subintegral
  map from a reduced scheme to a seminormal scheme is an isomorphism.
* `AlgebraicGeometry.bijective_of_universalHomeomorphism_of_residueFieldMap_isIso`: the
  affine, ring-level form of the same statement.
* `AlgebraicGeometry.isReduced_initial_seminormalizationCategory`: the chosen initial object
  of the seminormalization category is reduced.
* `AlgebraicGeometry.isIso_initialTo_of_isSeminormal`: the implication of 0EUS that is proved
  here.
* `AlgebraicGeometry.isIso_initialTo_iff_isSeminormal_of_isSeminormal_initial`: the full
  equivalence of 0EUS, conditional on the seminormalization being seminormal.

## Implementation notes

The existence of an initial object of the seminormalization category is carried here as an
instance argument `[HasInitial (SeminormalizationCategory X)]`.  This is purely a matter of
import order, not of availability: the instance
`AlgebraicGeometry.hasInitial_seminormalizationCategory` lives in
`StacksFrontier.AlgebraicGeometry.SeminormalizationGluing.Basic`, and that file imports this one,
because the gluing construction of the initial object uses the results proved here.  A
downstream file that imports it should therefore state its results with no such hypothesis.

The converse implication of 0EUS — that the seminormalization is itself seminormal — is not
proved here either, for the same reason, and it is the only thing missing from the equivalence
*in this file*.  It is isolated as the hypothesis of
`isIso_initialTo_iff_isSeminormal_of_isSeminormal_initial`, so that the equivalence follows
from it with no further geometry.  It is discharged downstream by
`AlgebraicGeometry.isSeminormal_initial_seminormalizationCategory`, from the same gluing
construction, which gives the unconditional equivalence
`AlgebraicGeometry.isIso_initialTo_iff_isSeminormal`.  The affine-local step of that
implication is `AlgebraicGeometry.isSeminormalRing_of_squareCube_sections`, here.

Reducedness of the initial object is obtained from initiality rather than from any
construction: its reduction is again an object of the category, and the two maps between the
two objects compose to identities because the Hom-sets out of an initial object are
singletons.

The affine step is pushed all the way down to commutative algebra: the image subring of the
corresponding ring map is proper unless the map is surjective, and `Stacks 0CNB` then
produces an element outside the image whose square and cube lie in it — which seminormality
of the source forbids.

Consequently no Stacks attribute for tag 0EUS is attached anywhere in this directory.  The
single assertion carrying the label `seminormalization_iso_iff` is an equivalence, only one
implication of which is proved here, and the statement that does assert the equivalence does
so under a hypothesis the tag does not have.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The chosen initial object of the seminormalization category is reduced: its reduction is
again an object of the category, so initiality makes the canonical closed immersion from the
reduction an isomorphism. -/
instance isReduced_initial_seminormalizationCategory (X : Scheme.{u})
    [HasInitial (SeminormalizationCategory X)] :
    IsReduced (initial (SeminormalizationCategory X)).obj.left := by
  let I : SeminormalizationCategory X := initial (SeminormalizationCategory X)
  let P := I.obj.left
  let r : P.nilradical.subscheme ⟶ P := P.nilradical.subschemeι
  let redObj : SeminormalizationCategory X :=
    ⟨Over.mk (r ≫ I.obj.hom), ⟨by
      exact (universalHomeomorphism_hasTwoOutOfThreeProperty).comp_mem
        r I.obj.hom (inferInstance) I.property.1, by
        intro z
        change IsIso ((r ≫ I.obj.hom).residueFieldMap z)
        rw [Scheme.residueFieldMap_comp]
        exact IsIso.comp_isIso' (I.property.2 (r z))
          (residueFieldMap_isIso_of_isClosedImmersion r z)⟩⟩
  let m := initial.to redObj
  let g := m.hom.left
  let rHom : redObj ⟶ I := ObjectProperty.homMk (Over.homMk r (by rfl))
  have hgr : g ≫ r = 𝟙 P :=
    congrArg (fun f : I ⟶ I => f.hom.left) (Subsingleton.elim (m ≫ rHom) (𝟙 I))
  have hrg : r ≫ g = 𝟙 P.nilradical.subscheme := by
    exact (cancel_mono r).mp (by simp [Category.assoc, hgr])
  let : IsIso r := ⟨g, hrg, hgr⟩
  let : IsReduced P.nilradical.subscheme := by
    simpa only [← Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := P) ⊤
  let : IsOpenImmersion (inv r) := inferInstance
  exact AlgebraicGeometry.isReduced_of_isOpenImmersion (inv r)

/-- A ring map whose spectrum map is a universal homeomorphism is injective when the source
is reduced: dominance forces its kernel into the nilradical, which is zero. -/
theorem injective_of_universalHomeomorphism_of_isReduced
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) [_root_.IsReduced R]
    (hU : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom f).op)) :
    Function.Injective f := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) := by
    have h := MorphismProperty.universally_le _ _ hU.universally_isHomeomorph
    change IsHomeomorph (PrimeSpectrum.comap f) at h
    exact h.surjective
  have hker : RingHom.ker f ≤ nilradical R :=
    PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f |>.mp hsurj.denseRange
  refine (RingHom.injective_iff_ker_eq_bot f).2 (le_antisymm ?_ bot_le)
  simpa [nilradical_eq_zero] using hker

/-- If a composite induces an isomorphism on a residue field and the second map does too at the
image point, then so does the first map. -/
private theorem isIso_residueFieldMap_of_isIso_comp_right {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (x : X) [IsIso (g.residueFieldMap (f x))]
    (h : IsIso ((f ≫ g).residueFieldMap x)) : IsIso (f.residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp] at h
  let : IsIso (g.residueFieldMap (f x) ≫ f.residueFieldMap x) := h
  exact IsIso.of_isIso_comp_left (g.residueFieldMap (f x)) (f.residueFieldMap x)

/-- **The affine case of Stacks 0EUS.** A ring map out of a seminormal ring into a reduced
ring whose spectrum map is a universal homeomorphism inducing isomorphisms on residue fields
is bijective. -/
theorem bijective_of_universalHomeomorphism_of_residueFieldMap_isIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hR : IsSeminormalRing R) [_root_.IsReduced S]
    (hU : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom f).op))
    (hres : ∀ x : Spec (CommRingCat.of S),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom f).op).residueFieldMap x)) :
    Function.Bijective f := by
  let : _root_.IsReduced R := seminormalRing_isReduced hR
  have hf : Function.Injective f :=
    injective_of_universalHomeomorphism_of_isReduced f hU
  refine ⟨hf, ?_⟩
  let A := f.range
  let g := f.rangeRestrict
  let i := A.subtype
  have hgi : CommRingCat.ofHom g ≫ CommRingCat.ofHom i = CommRingCat.ofHom f := by
    rw [← CommRingCat.ofHom_comp]
    apply CommRingCat.hom_ext
    ext x
    rfl
  let e : R ≃+* A := RingEquiv.ofBijective g
    ⟨(fun x y h => hf (congrArg Subtype.val h)), RingHom.rangeRestrict_surjective f⟩
  have : IsIso (CommRingCat.ofHom g) := e.toCommRingCatIso.isIso_hom
  let ug := Scheme.Spec.map (CommRingCat.ofHom g).op
  let ui := Scheme.Spec.map (CommRingCat.ofHom i).op
  have : IsIso ug := Functor.map_isIso Scheme.Spec _
  have hUg : UniversalHomeomorphism ug := universalHomeomorphism_of_isIso ug
  have hcomp : ui ≫ ug = Scheme.Spec.map (CommRingCat.ofHom f).op := by
    have hgi' := congrArg (fun q => q.op) hgi
    simpa only [CategoryTheory.op_comp, Scheme.Spec.map_comp] using
      congrArg (fun q => Scheme.Spec.map q) hgi'
  let : MorphismProperty.HasOfPostcompProperty
      (@UniversalHomeomorphism.{u}) (@UniversalHomeomorphism.{u}) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty
  have hUi : UniversalHomeomorphism ui := by
    apply MorphismProperty.of_postcomp _ ui ug hUg
    simpa [hcomp] using hU
  have hresI : ∀ x : Spec (CommRingCat.of S), IsIso (ui.residueFieldMap x) := fun x =>
    isIso_residueFieldMap_of_isIso_comp_right ui ug x (by rw [hcomp]; exact hres x)
  let : UniversalHomeomorphism ui := hUi
  intro b
  by_contra hb
  have hneq : A ≠ ⊤ := fun htop => hb (RingHom.range_eq_top.mp htop b)
  obtain ⟨b, hbA, hb2, hb3⟩ :=
    exists_not_mem_and_sq_mem_and_cube_mem_of_universalHomeomorphism_of_residueFieldMap_isIso
      A hresI hneq
  obtain ⟨x, hx⟩ := (RingHom.mem_range).mp hb2
  obtain ⟨y, hy⟩ := (RingHom.mem_range).mp hb3
  have hxy : x ^ 3 = y ^ 2 := hf <| by
    rw [map_pow, map_pow, hx, hy]
    ring
  obtain ⟨a, ha, _⟩ := hR x y hxy
  have ha₂ : f a ^ 2 = b ^ 2 := by rw [← map_pow, ← ha.1, hx]
  have ha₃ : f a ^ 3 = b ^ 3 := by rw [← map_pow, ← ha.2, hy]
  exact hbA ((RingHom.mem_range).2
    ⟨a, Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq ha₂ ha₃⟩)

/-- The restriction of a subintegral map to an affine open of a seminormal target is an
isomorphism, by the affine case. -/
theorem isIso_morphismRestrict_of_isSeminormal_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : IsReduced X) (hY : IsSeminormal Y)
    (hU : UniversalHomeomorphism f) (hres : ∀ x : X, IsIso (f.residueFieldMap x))
    (V : Y.affineOpens) : IsIso (f ∣_ V) := by
  have : IsIntegralHom f :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hU |>.1
  have : IsAffineHom f := inferInstance
  let W : X.affineOpens := ⟨f ⁻¹ᵁ V.1, IsAffineOpen.preimage V.2 f⟩
  let g : W.1.toScheme ⟶ V.1.toScheme := f ∣_ V.1
  have hgU : UniversalHomeomorphism g := by
    rw [universalHomeomorphism_iff] at hU ⊢
    exact MorphismProperty.of_isPullback
      (AlgebraicGeometry.isPullback_morphismRestrict f V.1).flip hU
  have hgres : ∀ z : W.1.toScheme, IsIso (g.residueFieldMap z) := fun z =>
    isIso_residueFieldMap_of_isIso_comp_right g V.1.ι z (by
      rw [AlgebraicGeometry.morphismRestrict_ι, Scheme.residueFieldMap_comp]
      have : IsIso (W.1.ι.residueFieldMap z) := inferInstance
      exact IsIso.comp_isIso' (hres (W.1.ι z)) inferInstance)
  have hR' : IsSeminormalRing Γ(Y, V.1) := (isSeminormal_iff_forall_affineOpens Y).mp hY V
  have hR : IsSeminormalRing Γ(V.1.toScheme, ⊤) := by
    convert hR' using 1
    rw [Scheme.Opens.toScheme_presheaf_obj, V.1.ι_image_top]
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine W.1.toScheme := W.2
  have : IsReduced W.1.toScheme := isReduced_of_isOpenImmersion W.1.ι
  have : _root_.IsReduced Γ(W.1.toScheme, ⊤) := inferInstance
  let q := W.1.toScheme.isoSpec.inv
  let p := V.1.toScheme.isoSpec.hom
  let c := q ≫ g ≫ p
  let φ := (Spec.fullyFaithful.preimage c).unop
  have hSpecEq : Scheme.Spec.map φ.op = c := Spec.fullyFaithful.map_preimage c
  have hSpec : UniversalHomeomorphism (Scheme.Spec.map φ.op) := by
    rw [hSpecEq]
    let : UniversalHomeomorphism q := universalHomeomorphism_of_isIso _
    let : UniversalHomeomorphism p := universalHomeomorphism_of_isIso _
    exact (universalHomeomorphism_hasTwoOutOfThreeProperty).comp_mem (q ≫ g) p
      ((universalHomeomorphism_hasTwoOutOfThreeProperty).comp_mem q g inferInstance hgU)
      inferInstance
  have hSpecRes : ∀ z : Spec (CommRingCat.of Γ(W.1.toScheme, ⊤)),
      IsIso ((Scheme.Spec.map φ.op).residueFieldMap z) := by
    intro z
    rw [hSpecEq]
    dsimp [c]
    rw [Scheme.residueFieldMap_comp]
    let : IsIso (q.residueFieldMap z) := inferInstance
    let : IsIso ((g ≫ p).residueFieldMap (q z)) := by
      rw [Scheme.residueFieldMap_comp]
      let : IsIso (g.residueFieldMap (q z)) := hgres (q z)
      let : IsIso (p.residueFieldMap (g (q z))) := inferInstance
      exact IsIso.comp_isIso' (inferInstance : IsIso (p.residueFieldMap (g (q z))))
        (hgres (q z))
    exact IsIso.comp_isIso' (inferInstance : IsIso ((g ≫ p).residueFieldMap (q z)))
      (inferInstance : IsIso (q.residueFieldMap z))
  have hb : Function.Bijective φ.hom :=
    bijective_of_universalHomeomorphism_of_residueFieldMap_isIso φ.hom hR hSpec hSpecRes
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).2 hb
  have : IsIso φ.op := (isIso_op_iff φ).2 inferInstance
  have : IsIso (Scheme.Spec.map φ.op) := Functor.map_isIso Scheme.Spec φ.op
  have : IsIso c := by rw [← hSpecEq]; infer_instance
  have : IsIso (g ≫ p) := IsIso.of_isIso_comp_left q _
  exact IsIso.of_isIso_comp_right g p

/-- **One implication of Stacks 0EUS.** A universal homeomorphism out of a reduced scheme
which induces isomorphisms on all residue fields and whose target is seminormal is an
isomorphism. -/
theorem isIso_of_isSeminormal_target_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : IsReduced X) (hY : IsSeminormal Y)
    (hU : UniversalHomeomorphism f) (hres : ∀ x : X, IsIso (f.residueFieldMap x)) :
    IsIso f := by
  classical
  have hbase : IsHomeomorph f.base :=
    MorphismProperty.universally_le _ _ hU.universally_isHomeomorph
  have : IsIso f.base := (TopCat.isIso_iff_isHomeomorph _).mpr hbase
  let V : Y.affineCover.I₀ → Y.affineOpens := fun i =>
    ⟨(Y.affineCover.f i).opensRange, isAffineOpen_opensRange (Y.affineCover.f i)⟩
  have hcover : ⨆ i, (V i : Y.Opens) = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext y
    rw [TopologicalSpace.Opens.coe_iSup]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨z, hz⟩ := Y.affineCover.covers y
      exact Set.mem_iUnion.mpr ⟨Y.affineCover.idx y, ⟨z, hz⟩⟩
  let : HasAffineProperty @IsOpenImmersion
      (AffineTargetMorphismProperty.of @IsOpenImmersion) :=
    HasAffineProperty.of_isZariskiLocalAtTarget @IsOpenImmersion
  have hOpen : IsOpenImmersion f := by
    apply HasAffineProperty.of_iSup_eq_top (P := @IsOpenImmersion) V hcover
    intro i
    show IsOpenImmersion (f ∣_ V i)
    let : IsIso (f ∣_ V i) :=
      isIso_morphismRestrict_of_isSeminormal_of_universalHomeomorphism f hX hY hU hres (V i)
    infer_instance
  let : IsOpenImmersion f := hOpen
  exact IsOpenImmersion.isIso f

/-- **One implication of Stacks 0EUS.** If a candidate `Y` for the seminormalization of `X`
is seminormal, then the canonical map to it from the chosen initial object of the
seminormalization category is an isomorphism. -/
theorem isIso_initialTo_of_isSeminormal (X : Scheme.{u})
    [HasInitial (SeminormalizationCategory X)] (Y : SeminormalizationCategory X)
    (hY : IsSeminormal Y.obj.left) : IsIso (initial.to Y).hom.left := by
  let f := (initial.to Y).hom.left
  have hComp : f ≫ Y.obj.hom = (initial (SeminormalizationCategory X)).obj.hom :=
    (initial.to Y).hom.w
  let : MorphismProperty.HasOfPostcompProperty
      (@UniversalHomeomorphism.{u}) (@UniversalHomeomorphism.{u}) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty
  have hU : UniversalHomeomorphism f := by
    apply MorphismProperty.of_postcomp _ f Y.obj.hom Y.property.1
    simpa [hComp] using (initial (SeminormalizationCategory X)).property.1
  have hres : ∀ x : (initial (SeminormalizationCategory X)).obj.left,
      IsIso (f.residueFieldMap x) := fun x =>
    haveI := Y.property.2 (f x)
    isIso_residueFieldMap_of_isIso_comp_right f Y.obj.hom x (by
      rw [hComp]; exact (initial (SeminormalizationCategory X)).property.2 x)
  exact isIso_of_isSeminormal_target_of_universalHomeomorphism f
    (isReduced_initial_seminormalizationCategory X) hY hU hres

/-- **Stacks 0EUS**, conditional on the seminormalization being seminormal. The canonical map
from the chosen initial object of the seminormalization category of `X` to a candidate `Y` is
an isomorphism exactly when `Y` is seminormal.

The hypothesis `hP` is the remaining content of the tag and is *not* proved in this
repository; see the implementation notes. -/
theorem isIso_initialTo_iff_isSeminormal_of_isSeminormal_initial (X : Scheme.{u})
    [HasInitial (SeminormalizationCategory X)]
    (hP : IsSeminormal (initial (SeminormalizationCategory X)).obj.left)
    (Y : SeminormalizationCategory X) :
    IsIso (initial.to Y).hom.left ↔ IsSeminormal Y.obj.left := by
  refine ⟨fun hIso => ?_, isIso_initialTo_of_isSeminormal X Y⟩
  let : IsIso (initial.to Y).hom.left := hIso
  exact isSeminormal_of_isIso (initial.to Y).hom.left hP

end AlgebraicGeometry

end
