module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSpaceFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvr
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumMapFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionQuotient
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientAdic

/-!
# The flat part of a Noetherian affine formal algebraic space over a discrete valuation ring

Let `A` be a discrete valuation ring with an adic topology and let `U = Spf R` be a Noetherian
affine formal algebraic space over `Spf A`. The affine half of the proof of **Stacks 0GD8**
takes the closed formal subspace `Spf (R ⧸ T) ⟶ Spf R`, where `T` is the `A`-torsion ideal of
`R`: it is flat over `A`, and every morphism into `Spf R` out of a Noetherian affine formal
algebraic space flat over `A` factors through it, because the corresponding continuous ring map
out of `R` kills the torsion.

## Main definitions

* `AlgebraicGeometry.FormalSpace.QuotientSystem.quotient`: the quotient system over `S` that a
  quotient system of `R` induces on a quotient ring `R ⧸ K` with the quotient topology.
* `AlgebraicGeometry.FormalSpace.ContinuousHom.quotientMk`: the projection `R ⟶ R ⧸ K` as a
  continuous homomorphism over `S`.

## Main results

* `TopologicalRing.isAdic_quotient`: a quotient of a Noetherian adic topological ring, with the
  quotient topology, is adic.
* `RingHom.isTaut_quotient_mk`: the projection onto a quotient with the quotient topology is
  taut.
* `AlgebraicGeometry.FormalSpace.hasAffineFlatParts`: the affine half of Stacks 0GD8.

## References

* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### The quotient topology on a quotient of a Noetherian adic ring -/

namespace TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R]

/-- **A quotient of a Noetherian adic topological ring is adic.** For an ideal `K` of a
Noetherian adic topological ring `R`, the quotient `R ⧸ K` with the quotient topology is adic:
the image of an ideal of definition defines its topology, `K` is closed because every ideal of
a complete Noetherian adic ring is, so the quotient is separated, and it is complete as a
quotient of a complete group with a countable basis of neighbourhoods of zero. -/
theorem isAdic_quotient [IsNoetherianRing R] (hR : IsAdic R) (K : Ideal R) :
    IsAdic (R ⧸ K) := by
  obtain ⟨⟨I, -, hIadic⟩, hT2, hcomplete⟩ := hR
  have hJ := isAdic_map_quotient_mk I K hIadic
  refine ⟨⟨I.map (Ideal.Quotient.mk K), isIdealOfDefinition_of_isAdic hJ, hJ⟩, ?_,
    completeSpace_quotient_of_isCountablyGenerated K hcomplete
      (isCountablyGenerated_nhds_zero_of_isAdic hIadic)⟩
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace R := hcomplete
  exact t2Space_quotient_of_isClosed K (isClosed_ideal_of_isAdic_of_isNoetherianRing hIadic K)

end TopologicalRing

namespace RingHom

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R]

/-- **The projection onto a quotient with the quotient topology is taut.** The image of an open
ideal is open, the projection being an open map, hence closed; and the images of the open ideals
form a basis of neighbourhoods of zero of the quotient, since the open ideals form one of `R`. -/
theorem isTaut_quotient_mk (K : Ideal R) : IsTaut (Ideal.Quotient.mk K) := by
  have himage : ∀ I : Ideal R, IsOpen (I : Set R) →
      IsOpen ((I.map (Ideal.Quotient.mk K) : Ideal (R ⧸ K)) : Set (R ⧸ K)) := fun I hI ↦ by
    rw [Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    exact QuotientRing.isOpenMap_coe K _ hI
  have hclosure : ∀ I : Ideal R, IsOpen (I : Set R) →
      (I.map (Ideal.Quotient.mk K)).closure = I.map (Ideal.Quotient.mk K) := fun I hI ↦
    Ideal.closure_eq_of_isClosed _
      (AddSubgroup.isClosed_of_isOpen (I.map (Ideal.Quotient.mk K)).toAddSubgroup (himage I hI))
  refine ⟨fun I hI ↦ by rw [hclosure I hI]; exact himage I hI, ⟨fun t ↦ ⟨fun ht ↦ ?_, ?_⟩⟩⟩
  · have hpre : Ideal.Quotient.mk K ⁻¹' t ∈ nhds (0 : R) :=
      (QuotientRing.isOpenQuotientMap_mk K).continuous.continuousAt.preimage_mem_nhds
        (by simpa using ht)
    obtain ⟨I, hI, hIt⟩ := (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp hpre
    refine ⟨I, hI, ?_⟩
    rw [hclosure I hI, Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    rintro _ ⟨x, hx, rfl⟩
    exact hIt hx
  · rintro ⟨I, hI, hIt⟩
    rw [hclosure I hI] at hIt
    exact Filter.mem_of_superset ((himage I hI).mem_nhds (Ideal.zero_mem _)) hIt

end RingHom

namespace AlgebraicGeometry.FormalSpace

/-! ### Quotient systems on quotient rings -/

section Quotient

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
  (hR : TopologicalRing.IsWeaklyAdmissible R) (E : QuotientSystem B S hS R) (K : Ideal R)

/-- **The quotient system of a quotient ring.** A quotient system over `S` of a weakly
admissible topological ring `R` induces one on `R ⧸ K` with the quotient topology: a weak ideal
of definition `K'` of `R ⧸ K` contains the image of a weak ideal of definition `J` of `R`, so
`Spec ((R ⧸ K) ⧸ K')` is a closed subscheme of `Spec (R ⧸ J)`, which lies in the site, and it
maps to `S` through `Spec (R ⧸ J)`; the choice of `J` does not matter. -/
noncomputable def QuotientSystem.quotient : QuotientSystem B S hS (R ⧸ K) where
  inSite K' := by
    obtain ⟨J, hJ⟩ := exists_weakIdeal_le_comap hR (Ideal.Quotient.mk K)
      (QuotientRing.isOpenQuotientMap_mk K).continuous K'
    let f := Spec.map (CommRingCat.ofHom (Ideal.quotientMap K'.1 (Ideal.Quotient.mk K) hJ))
    have : AlgebraicGeometry.IsClosedImmersion f :=
      IsClosedImmersion.spec_of_surjective _ (Ideal.quotientMap_surjective
        (H := hJ) Ideal.Quotient.mk_surjective)
    exact Scheme.size_lt_of_isClosedImmersion f (E.inSite J)
  overS K' := Spec.map (CommRingCat.ofHom (Ideal.quotientMap K'.1 (Ideal.Quotient.mk K)
      (exists_weakIdeal_le_comap hR (Ideal.Quotient.mk K)
        (QuotientRing.isOpenQuotientMap_mk K).continuous K').choose_spec)) ≫
    E.overS (exists_weakIdeal_le_comap hR (Ideal.Quotient.mk K)
      (QuotientRing.isOpenQuotientMap_mk K).continuous K').choose
  compatible K' L h := by
    rw [quotientMap_comp_overS_eq E (Ideal.Quotient.mk K) L _
      (exists_weakIdeal_le_comap hR (Ideal.Quotient.mk K)
        (QuotientRing.isOpenQuotientMap_mk K).continuous K').choose _
      ((exists_weakIdeal_le_comap hR (Ideal.Quotient.mk K)
        (QuotientRing.isOpenQuotientMap_mk K).continuous K').choose_spec.trans
          (Ideal.comap_mono h)),
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

/-- The structure morphism of a quotient stage of `R ⧸ K` may be computed through any weak ideal
of definition of `R` whose image it contains. -/
theorem QuotientSystem.quotient_overS
    (K' : { I : Ideal (R ⧸ K) // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJ : J.1 ≤ Ideal.comap (Ideal.Quotient.mk K) K'.1) :
    (QuotientSystem.quotient hR E K).overS K' =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K'.1 (Ideal.Quotient.mk K) hJ)) ≫
        E.overS J :=
  quotientMap_comp_overS_eq E (Ideal.Quotient.mk K) K' _ J _ hJ

/-- The projection `R ⟶ R ⧸ K` as a continuous homomorphism over `S`. -/
noncomputable def ContinuousHom.quotientMk : ContinuousHom E (QuotientSystem.quotient hR E K) where
  toRingHom := Ideal.Quotient.mk K
  continuous := (QuotientRing.isOpenQuotientMap_mk K).continuous
  overS J K' h := (QuotientSystem.quotient_overS hR E K K' J h).symm

/-- The ring homomorphism underlying `ContinuousHom.quotientMk` is `Ideal.Quotient.mk K`. -/
@[simp]
theorem ContinuousHom.quotientMk_toRingHom :
    (ContinuousHom.quotientMk hR E K).toRingHom = Ideal.Quotient.mk K := rfl

/-- **A continuous homomorphism over `S` killing `K` factors through `R ⧸ K` over `S`.** -/
noncomputable def ContinuousHom.quotientLift {C : Type u} [CommRing C] [TopologicalSpace C]
    {F : QuotientSystem B S hS C} (h : ContinuousHom E F)
    (hK : ∀ r ∈ K, h.toRingHom r = 0) : ContinuousHom (QuotientSystem.quotient hR E K) F where
  toRingHom := Ideal.Quotient.lift K h.toRingHom hK
  continuous := (QuotientRing.isOpenQuotientMap_mk K).isQuotientMap.continuous_iff.mpr
    h.continuous
  overS J' K'' hJ' := by
    obtain ⟨J, hJ⟩ := exists_weakIdeal_le_comap hR (Ideal.Quotient.mk K)
      (QuotientRing.isOpenQuotientMap_mk K).continuous J'
    have hJK : J.1 ≤ Ideal.comap h.toRingHom K''.1 := fun r hr ↦ by
      have := hJ' (hJ hr)
      simpa using this
    rw [QuotientSystem.quotient_overS hR E K J' J hJ, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← h.overS J K'' hJK]
    congr 3
    apply Ideal.Quotient.ringHom_ext
    ext r
    rfl

/-- The ring homomorphism underlying `ContinuousHom.quotientLift` is the lift of `h.toRingHom`
through `Ideal.Quotient.mk K`. -/
@[simp]
theorem ContinuousHom.quotientLift_toRingHom {C : Type u} [CommRing C] [TopologicalSpace C]
    {F : QuotientSystem B S hS C} (h : ContinuousHom E F)
    (hK : ∀ r ∈ K, h.toRingHom r = 0) :
    (ContinuousHom.quotientLift hR E K h hK).toRingHom = Ideal.Quotient.lift K h.toRingHom hK :=
  rfl

end Quotient

/-! ### The affine flat part -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

/-- **The affine half of Stacks 0GD8.** Let `A` be a discrete valuation ring with an adic
topology and `p : X ⟶ Spf A`. Every Noetherian affine formal algebraic space `U` representable
étale over `X` carries a closed immersion `Z ⟶ U` with `Z` Noetherian affine and flat over `A`,
through which every Noetherian affine formal algebraic space flat over `A` and mapping to `U`
factors.

With `U = Spf R` and `A ⟶ R` the continuous homomorphism of Stacks 0AN0 presenting
`U ⟶ X ⟶ Spf A`, `Z` is `Spf (R ⧸ T)` for the `A`-torsion ideal `T` of `R` with the quotient
topology. `R ⧸ T` is torsion free, hence flat over the discrete valuation ring `A`, and adic
Noetherian; the projection is taut with dense image, so `Spf (R ⧸ T) ⟶ Spf R` is a closed
immersion. A morphism `W ⟶ U` out of `W = Spf F` flat over `A` is `Spf` of a continuous
homomorphism `R ⟶ F` over `S` whose composite with `A ⟶ R` is flat, by Definition 0GCC read on
the identity charts; a flat module over a domain is torsion free, so `R ⟶ F` kills `T` and
factors through `R ⧸ T`. -/
theorem hasAffineFlatParts [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A) {X : FppfSheaf B S hS} (p : X ⟶ formalSpectrum D) :
    HasAffineFlatParts B S hS D p := by
  let : IsLinearTopology A A := Rig.isLinearTopology_of_isAdicRing hA
  have hAw : TopologicalRing.IsWeaklyAdmissible A := hA.isWeaklyAdmissible
  intro U v hU hUn hv
  obtain ⟨-, R, _, _, _, _, ⟨hRw, ⟨P⟩⟩, hRnoeth, hRadic⟩ := hUn
  set E := P.quotientSystem
  set eU : U ≅ formalSpectrum E := P.formalSpectrumIso
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hRw (eU.inv ≫ v ≫ p)
  let : Algebra A R := g.toRingHom.toAlgebra
  set K := Algebra.baseTorsionIdeal A R
  have hR'adic : TopologicalRing.IsAdic (R ⧸ K) := TopologicalRing.isAdic_quotient hRadic K
  let : IsLinearTopology (R ⧸ K) (R ⧸ K) := Rig.isLinearTopology_of_isAdicRing hR'adic
  have hR'w : TopologicalRing.IsWeaklyAdmissible (R ⧸ K) := hR'adic.isWeaklyAdmissible
  set E' := QuotientSystem.quotient hRw E K
  set π := ContinuousHom.quotientMk hRw E K
  have hπ : IsClosedImmersion B S hS (formalSpectrumMap hRw π) :=
    isClosedImmersion_formalSpectrumMap_of_isTaut_of_denseRange B S hS hRw hR'w E E' π
      (RingHom.isTaut_quotient_mk K) Ideal.Quotient.mk_surjective.denseRange
  refine ⟨formalSpectrum E', formalSpectrumMap hRw π ≫ eU.inv,
    isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hR'adic E' (Iso.refl _),
    isNoetherian_formalSpectrum B S hS hR'adic E',
    isClosedImmersion_comp B S hS _ _ hπ (isClosedImmersion_of_isIso B S hS eU.inv), ?_, ?_⟩
  · have hrw : (formalSpectrumMap hRw π ≫ eU.inv) ≫ v ≫ p =
        formalSpectrumMap hAw (ContinuousHom.comp hRw hAw π g) := by
      rw [← formalSpectrumMap_comp_eq, hg, Category.assoc]
    rw [hrw]
    refine isFlat_formalSpectrumMap_of_flat B S hS hA hR'adic hAw D E' _ ?_
    rw [ContinuousHom.comp_toRingHom, ContinuousHom.quotientMk_toRingHom]
    exact RingHom.flat_algebraMap_iff.mpr (Algebra.flat_quotient_baseTorsionIdeal A R)
  · intro W w hW hWn hWflat
    obtain ⟨-, F, _, _, _, _, ⟨hFw, ⟨PW⟩⟩, hFnoeth, hFadic⟩ := hWn
    set EW := PW.quotientSystem
    set eW : W ≅ formalSpectrum EW := PW.formalSpectrumIso
    obtain ⟨h, hh, -⟩ :=
      existsUnique_continuousHom_formalSpectrumMap_eq hRw hFw (eW.inv ≫ w ≫ eU.hom)
    have hflat : (h.toRingHom.comp g.toRingHom).Flat := by
      have hid := isRepresentableEtale_id B S hS W
      have hid' := isRepresentableEtale_id B S hS (formalSpectrum D)
      refine hWflat W (formalSpectrum D) hW
        (isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hA D (Iso.refl _))
        (𝟙 W) (𝟙 _) (w ≫ v ≫ p) hid.1 hid'.1 hid.2 hid'.2
        (by simp) A F hA hFadic hAw D EW eW (Iso.refl _) (ContinuousHom.comp hRw hAw h g) ?_
      rw [← formalSpectrumMap_comp_eq, hh, hg]
      simp
    let : Algebra A F := (h.toRingHom.comp g.toRingHom).toAlgebra
    have : Module.Flat A F := hflat
    have : Module.IsTorsionFree A F := Module.Flat.isTorsionFree
    let φ : R →ₐ[A] F := { h.toRingHom with commutes' := fun _ ↦ rfl }
    have hK : ∀ r ∈ K, h.toRingHom r = 0 := fun r hr ↦
      Algebra.baseTorsionIdeal_le_ker A R φ hr
    set h' := ContinuousHom.quotientLift hRw E K h hK
    refine ⟨eW.hom ≫ formalSpectrumMap hR'w h', ?_⟩
    have hcomp : ContinuousHom.comp hR'w hRw h' π = h :=
      ContinuousHom.ext_toRingHom (RingHom.ext fun _ ↦ rfl)
    rw [Category.assoc, ← Category.assoc (formalSpectrumMap hR'w h'), formalSpectrumMap_comp_eq,
      hcomp, hh]
    simp

end AlgebraicGeometry.FormalSpace

end
