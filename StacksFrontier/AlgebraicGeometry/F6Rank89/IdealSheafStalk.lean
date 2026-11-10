module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Properties.RegularLocus
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# The stalk of an ideal sheaf, and the ideal sheaf of a reduced closed point

`AlgebraicGeometry.IdealSheafData.stalk I x` is the ideal of the local ring `𝒪_{X,x}` generated
by the sections of the quasi-coherent ideal sheaf `I`. At an affine open neighbourhood it is the
image of `I.ideal U` under the germ map, which is
`AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ`; this file computes it further: it is the
unit ideal exactly off the support of `I`, and for a closed immersion it is the kernel of the map
on stalks.

The reduced closed point `x` of a scheme `X` gives such an ideal sheaf,
`Scheme.IdealSheafData.vanishingIdeal {x}`, and the second half of the file identifies it: on an
affine open it is the prime of `x`, its stalk at `x` is the maximal ideal, and its inverse image
along `X.fromSpecStalk x` is the ideal of the closed point of `Spec 𝒪_{X,x}`. The last of these
is what lets a statement about a closed point of a scheme be transported to the local ring at
that point, and the transport needs that `X.fromSpecStalk x` is flat and a monomorphism, both of
which are proved here.

## Main results

* `AlgebraicGeometry.IdealSheafData.stalk_mono`: the stalk is monotone in the ideal sheaf.
* `AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support`: the stalk is the unit
  ideal exactly off the support.
* `AlgebraicGeometry.IdealSheafData.stalk_ker_of_isClosedImmersion`: for a closed immersion the
  stalk of its kernel ideal sheaf is the kernel of the induced map of local rings.
* `AlgebraicGeometry.vanishingIdeal_singleton_ideal`: the ideal of a reduced closed point on an
  affine open containing it is the corresponding prime.
* `AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton`: its stalk at that point is
  the maximal ideal of the local ring.
* `AlgebraicGeometry.vanishingIdeal_singleton_comap_fromSpecStalk`: its inverse image along
  `X.fromSpecStalk x` is the kernel of the residue map.
* `AlgebraicGeometry.isIso_stalkMap_of_flat_preimmersion`: a flat preimmersion is an
  isomorphism on local rings.
* `AlgebraicGeometry.isRegular_of_stalks` and `AlgebraicGeometry.isRegular_of_iso`: regularity
  of a locally Noetherian scheme is a condition on its local rings, hence invariant under
  isomorphism.

## Implementation notes

The stalk is defined as a supremum over all affine opens containing the point, so computing it on
one affine open needs a cofinality argument: two affine opens containing `x` share a basic open
containing `x` (`AlgebraicGeometry.exists_basicOpen_le_affine_inter`), and the ideals of an ideal
sheaf are compatible with restriction, so every term of the supremum is dominated by the one
chosen.

`AlgebraicGeometry.isIso_pullback_snd_of_factorization` is the categorical fact behind both
`AlgebraicGeometry.ker_comap_of_factorization` and
`AlgebraicGeometry.exists_comapIso_of_isPullback_of_factorization`: a base change along a
monomorphism which the other leg factors through is an isomorphism. It is stated for an arbitrary
category with pullbacks rather than for schemes, since nothing about schemes enters.

`AlgebraicGeometry.vanishingIdeal_singleton_ideal` identifies `PrimeSpectrum.vanishingIdeal` of
the preimage of `{x}` in the affine chart with the prime of `x`. The preimage is computed as a
singleton by injectivity of `IsAffineOpen.fromSpec`, and the resulting equality of ideals is then
transported by `congrArg` rather than by `rw`: the two sides are definitionally the ideal of a
`PrimeSpectrum` point but not syntactically so, and a `change` to the `vanishingIdeal` spelling
followed by a rewrite needs reducible unfolding of `IsAffineOpen.primeIdealOf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If a monomorphism `f` is factored by `g`, then the base change of `f` along `g`'s target
map is an isomorphism. -/
theorem isIso_pullback_snd_of_factorization {C : Type*} [Category C] [HasPullbacks C]
    {A B T : C} (f : A ⟶ T) [Mono f] (g : B ⟶ T) (h : B ⟶ A) (hh : h ≫ f = g) :
    IsIso (pullback.snd f g) := by
  let i : B ⟶ pullback f g := pullback.lift h (𝟙 B) (by simpa using hh)
  refine ⟨⟨i, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply (cancel_mono f).1
      simp only [i, Category.assoc, pullback.lift_fst_assoc, hh,
        ← pullback.condition, Category.id_comp]
    · simp only [i, Category.assoc, pullback.lift_snd, Category.comp_id,
        Category.id_comp]
  · exact pullback.lift_snd _ _ _

/-- The kernel ideal sheaf of a morphism of affine schemes, as the image of the kernel of the
corresponding ring map. -/
theorem Scheme.ker_SpecMap {R T : CommRingCat.{u}} (φ : R ⟶ T) :
    (Spec.map φ).ker = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso R).inv.hom (RingHom.ker φ.hom)) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv]
  change RingHom.ker (((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso T).hom).hom) = _
  rw [Scheme.ΓSpecIso_naturality]
  rw [CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact (Ideal.map_comap_of_equiv
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).symm

/-- The inverse image of the kernel ideal sheaf of a closed immersion along a monomorphism it
factors through is the kernel of the factoring morphism. -/
theorem ker_comap_of_factorization {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : Y ⟶ X) [Mono f] (g : Z ⟶ Y) (hg : g ≫ f = i) : i.ker.comap f = g.ker := by
  let : IsIso (pullback.snd f i) := isIso_pullback_snd_of_factorization f i g hg
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso (inv (pullback.snd f i))]
  congr 1
  apply (cancel_mono f).1
  simp only [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, hg]

/-- A monomorphic base change that fixes a closed subscheme also fixes its inverse image under
any morphism. -/
theorem exists_comapIso_of_isPullback_of_factorization {X Y B B' : Scheme.{u}} (f : Y ⟶ X)
    [Mono f] (b : B ⟶ X) (b' : B' ⟶ Y) (h : B' ⟶ B) (hp : IsPullback b' h f b)
    (I : X.IdealSheafData) (g : I.subscheme ⟶ Y) (hg : g ≫ f = I.subschemeι) :
    ∃ e : ((I.comap b).comap h).subscheme ≅ (I.comap b).subscheme,
      e.hom ≫ (I.comap b).subschemeι = ((I.comap b).comap h).subschemeι ≫ h := by
  let D := I.comap b
  let c : D.subscheme ⟶ I.subscheme := (I.comapIso b).hom ≫ pullback.snd b I.subschemeι
  have hc : c ≫ I.subschemeι = D.subschemeι ≫ b := by
    simp only [c, Category.assoc, ← pullback.condition,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc, D]
  have hw : (c ≫ g) ≫ f = D.subschemeι ≫ b := by rw [Category.assoc, hg, hc]
  have : Mono h := by
    rw [← hp.isoPullback_hom_snd]
    infer_instance
  have : IsIso (pullback.snd h D.subschemeι) :=
    isIso_pullback_snd_of_factorization h D.subschemeι
      (hp.lift (c ≫ g) D.subschemeι hw) (hp.lift_snd _ _ _)
  refine ⟨D.comapIso h ≪≫ asIso (pullback.snd h D.subschemeι), ?_⟩
  change ((D.comapIso h).hom ≫ pullback.snd h D.subschemeι) ≫ D.subschemeι = _
  rw [Category.assoc, ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

namespace IdealSheafData

/-- **The stalk of an ideal sheaf is monotone in the ideal sheaf.** The stalk is the supremum,
over the affine opens containing the point, of the images of the ideals of sections under the
germ maps, and both the supremum and `Ideal.map` are monotone. -/
theorem stalk_mono {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    stalk I x ≤ stalk J x :=
  iSup₂_mono fun U _ ↦ Ideal.map_mono (h U)

/-- The stalk of an ideal sheaf is the unit ideal exactly at the points outside its support. -/
theorem stalk_eq_top_iff_not_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    stalk I x = ⊤ ↔ x ∉ I.support := by
  have hle : stalk I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔ x ∈ I.support := by
    have key : ∀ (U : X.affineOpens) (hxU : x ∈ U.1) (s : Γ(X, U.1)),
        (X.presheaf.germ U.1 x hxU).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
          x ∉ X.basicOpen s := fun U hxU s ↦ by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Scheme.mem_basicOpen X s x hxU]
    simp only [stalk, iSup_le_iff, Scheme.IdealSheafData.mem_support_iff, Scheme.mem_zeroLocus_iff]
    constructor
    · intro h U s hs
      by_cases hxU : x ∈ U.1
      · exact (key U hxU s).mp (h U hxU (Ideal.mem_map_of_mem _ hs))
      · exact fun hbasic ↦ hxU (X.basicOpen_le s hbasic)
    · intro h U hx
      rw [Ideal.map_le_iff_le_comap]
      exact fun s hs ↦ (key U hx s).mpr (h U s hs)
  rw [← hle]
  refine ⟨fun h hle' ↦ ?_, fun h ↦ not_not.mp fun hne ↦ h (IsLocalRing.le_maximalIdeal hne)⟩
  rw [h, top_le_iff] at hle'
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle'

/-- For a closed immersion, the stalk of its kernel ideal sheaf at the image of a point is the
kernel of the induced map of local rings. -/
theorem stalk_ker_of_isClosedImmersion {X C : Scheme.{u}} (f : C ⟶ X) [IsClosedImmersion f]
    (x : C) : stalk f.ker (f x) = RingHom.ker (f.stalkMap x).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let R := Γ(X, U)
  let B := Γ(C, V)
  let Rp := X.presheaf.stalk (f x)
  let Bp := C.presheaf.stalk x
  let p := hU.primeIdealOf ⟨f x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxU⟩
  let α : R →+* B := (f.app U).hom
  let : Algebra R Rp := X.presheaf.algebra_section_stalk ⟨f x, hxU⟩
  let : Algebra B Bp := C.presheaf.algebra_section_stalk (⟨x, hxU⟩ : V)
  have : IsLocalization.AtPrime Rp p.asIdeal := hU.isLocalization_stalk ⟨f x, hxU⟩
  have : IsLocalization.AtPrime Bp q.asIdeal := hV.isLocalization_stalk ⟨x, hxU⟩
  have hpq : q.asIdeal.comap α = p.asIdeal := by
    have h := hU.comap_primeIdealOf_appLE U V hV (le_refl _) hxU
    simpa only [R, B, α, p, q, V, Scheme.Hom.appLE_eq_app,
      PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal h
  have hT : p.asIdeal.primeCompl.map α = q.asIdeal.primeCompl := by
    simpa only [hpq] using
      Ideal.map_primeCompl_comap_of_surjective α (f.app_surjective U hU) q.asIdeal
  have hle : p.asIdeal.primeCompl ≤ q.asIdeal.primeCompl.comap α :=
    Submonoid.map_le_iff_le_comap.mp hT.le
  have hmap : (f.stalkMap x).hom = IsLocalization.map Bp α hle := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    rw [IsLocalization.map_comp]
    exact congrArg CommRingCat.Hom.hom (f.germ_stalkMap U x hxU)
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ _ ⟨U, hU⟩ hxU, Scheme.Hom.ker_apply,
    hmap]
  exact (IsLocalization.ker_map Bp α hT).symm

end IdealSheafData

/-- The ideal sheaf of a reduced closed point is the kernel of the canonical morphism from the
spectrum of its residue field. -/
theorem vanishingIdeal_singleton_eq_ker {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) :
    Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) =
      (X.fromSpecResidueField x).ker := by
  have hT : (⟨{x}, hx⟩ : Closeds X) =
      .closure ((X.fromSpecResidueField x) '' (⊤ : Closeds (Spec (X.residueField x)))) := by
    apply SetLike.coe_injective
    simp
  rw [hT, ← Scheme.IdealSheafData.map_vanishingIdeal]
  simp [Scheme.nilradical_eq_bot]

/-- The reduced closed point factors through its local scheme. -/
theorem exists_factor_fromSpecStalk_of_vanishingIdeal_singleton {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) :
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
    ∃ g : I.subscheme ⟶ Spec (X.presheaf.stalk x), g ≫ X.fromSpecStalk x = I.subschemeι := by
  let i := X.fromSpecResidueField x
  let : IsClosedImmersion i := (isClosed_singleton_iff_isClosedImmersion (x := x)).mp hx
  rw [vanishingIdeal_singleton_eq_ker x hx]
  refine ⟨inv i.toImage ≫ Spec.map (X.residue x), ?_⟩
  change inv i.toImage ≫ i = i.imageι
  calc
    inv i.toImage ≫ i = inv i.toImage ≫ (i.toImage ≫ i.imageι) :=
      congrArg (inv i.toImage ≫ ·) i.toImage_imageι.symm
    _ = i.imageι := IsIso.inv_hom_id_assoc _ _

/-- The inverse image of the ideal sheaf of a reduced closed point along the canonical morphism
from the spectrum of its local ring is the kernel of the residue map. -/
theorem vanishingIdeal_singleton_comap_fromSpecStalk {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).comap
        (X.fromSpecStalk x) = (Spec.map (X.residue x)).ker := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  rw [vanishingIdeal_singleton_eq_ker x hx]
  exact ker_comap_of_factorization (X.fromSpecResidueField x) (X.fromSpecStalk x)
    (Spec.map (X.residue x)) rfl

/-- On an affine open containing it, the ideal of a reduced closed point is the prime ideal
corresponding to that point. -/
theorem vanishingIdeal_singleton_ideal {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (U : X.affineOpens) (hxU : x ∈ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).ideal U =
      (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hpre : U.2.fromSpec.base ⁻¹' ({x} : Set X) = {U.2.primeIdealOf ⟨x, hxU⟩} := by
    ext p
    change U.2.fromSpec.base p = x ↔ p = U.2.primeIdealOf ⟨x, hxU⟩
    constructor
    · intro hp
      apply U.2.fromSpec.isOpenEmbedding.injective
      exact hp.trans (U.2.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
    · rintro rfl
      exact U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact (congrArg PrimeSpectrum.vanishingIdeal hpre).trans
    (PrimeSpectrum.vanishingIdeal_singleton _)

/-- The stalk at a reduced closed point of its own ideal sheaf is the maximal ideal of the local
ring there. -/
theorem IdealSheafData.stalk_vanishingIdeal_singleton {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have hxU : x ∈ (⟨(X.affineCover.f (X.affineCover.idx x)).opensRange,
      isAffineOpen_opensRange _⟩ : X.affineOpens).1 := X.affineCover.covers x
  rw [IdealSheafData.stalk_eq_map_germ _ _ _ hxU, vanishingIdeal_singleton_ideal x hx _ hxU]
  let : Algebra Γ(X, (X.affineCover.f (X.affineCover.idx x)).opensRange)
      (X.presheaf.stalk x) :=
    (X.presheaf.germ (X.affineCover.f (X.affineCover.idx x)).opensRange x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).primeIdealOf
        ⟨x, hxU⟩).asIdeal :=
    (isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).isLocalization_stalk
      ⟨x, hxU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _

/-- A flat preimmersion induces isomorphisms on local rings: the induced map is surjective
because the morphism is a preimmersion, and injective because a flat local homomorphism is
faithfully flat. -/
theorem isIso_stalkMap_of_flat_preimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsPreimmersion f] (x : X) : IsIso (f.stalkMap x) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (Flat.iff_flat_stalkMap f).mp ‹Flat f› x
  have : IsLocalHom
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    change IsLocalHom (f.stalkMap x).hom
    infer_instance
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (f.stalkMap x).hom :=
    FaithfulSMul.algebraMap_injective _ _
  have hsurj : Function.Surjective (f.stalkMap x).hom := Scheme.Hom.stalkMap_surjective f x
  exact (ConcreteCategory.isIso_iff_bijective (f.stalkMap x)).mpr ⟨hinj, hsurj⟩

/-- A locally Noetherian scheme all of whose local rings are regular is regular. -/
theorem isRegular_of_stalks {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) : IsRegular X := by
  have he : IsRegular X ↔ IsLocallyNoetherian X ∧
      ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := (isRegular_tfae X).out 1 2
  exact he.mpr ⟨inferInstance, h⟩

/-- Regularity of a locally Noetherian scheme transports along an isomorphism. -/
theorem isRegular_of_iso {X Y : Scheme.{u}} [IsLocallyNoetherian X] (e : X ≅ Y)
    (hY : IsRegular Y) : IsRegular X := by
  apply isRegular_of_stalks
  intro x
  have := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hY (e.hom x)
  exact IsRegularLocalRing.of_ringEquiv (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

end AlgebraicGeometry

end
