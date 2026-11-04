module

public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalPointed
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSmooth
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Algebra
public import StacksFrontier.RingTheory.Syntomic.SectionedDeformation

/-!
# Smoothness over the integers of the universal sectioned finite syntomic locus

Let `pi_d : Y_d ⟶ X_d` be the universal finite free family of rank `d` (Tag 0FKZ) and let
`U_d ⊆ X_d` be the maximal open over which it is finite syntomic (Tag 0FL0). Then
`V_d = pi_d^{-1}(U_d)` is smooth over `Spec(ZZ)`.

## Main results

* `AlgebraicGeometry.universalSyntomicPreimage_smooth_uLift`: `V_d` is smooth over the terminal
  scheme `Spec(ULift ZZ)` of an arbitrary universe.
* `AlgebraicGeometry.universalSyntomicPreimage_smooth`: the same statement over `Spec(ZZ)`
  itself.

## Implementation notes

Smoothness is checked with the infinitesimal lifting criterion of Tag 02HX
(`InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness`), which over a locally
Noetherian base tests smoothness at a point against *small extensions*, that is surjections of
artinian local rings with kernel of length one. This is the criterion the source uses, and not
the one of Tag 02H6 against first-order thickenings of arbitrary affine schemes: the deformation
problem is solved by writing the algebra as a relative global complete intersection with as many
relations as variables, which needs the conormal module of a presentation to be free and so holds
over a semilocal base, as an artinian local ring is.

The lifting problem for `V_d` is translated into that deformation problem by the functor of
points of `V_d`: a point of `V_d` over a scheme `T` is a multiplication table over `R = Γ(T, 𝒪)`
whose classifying morphism factors through `U_d` together with the coordinates of a section of
the algebra `Carrier m` of the table (`AlgebraicGeometry.pointedSyntomicEquiv`). Factoring
through `U_d` makes the base change of the universal family along the classifying morphism
syntomic (Tag 0FL0), and that base change is free on a basis whose table is `m`
(`AlgebraicGeometry.affinePullbackGammaBasis_structure_of_map`), hence isomorphic to
`Carrier m`; so `Carrier m` is a finite syntomic `R`-algebra with a section. Tag 0FL3's
deformation lemma (`Algebra.exists_finite_syntomic_section_lift`) lifts it along `R' → R` to a
finite syntomic `R'`-algebra `B'` with a section and with `B'/IB' = Carrier m`. Flatness of `B'`
lifts the standard basis of `Carrier m` through that reduction to a basis of `B'` beginning with
`1` (`Algebra.exists_basis_lift_of_nilpotent_ker`, from Tag 051F); its table and the images of
its vectors under the section form the point of `Y_d` over `T'` that is wanted. That point
restricts to the given one, and since a surjection with nilpotent kernel is surjective on points
its image again lies in `V_d`.

## References

* [Stacks Project, Tag 0FL3](https://stacks.math.columbia.edu/tag/0FL3)
* [Stacks Project, Tag 0FL1](https://stacks.math.columbia.edu/tag/0FL1)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
* [Stacks Project, Tag 051F](https://stacks.math.columbia.edu/tag/051F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry.FiniteFreeAlgebra

universe u

/-- Over a nilpotent ideal `I`, a basis of `M ⧸ I M` whose vector `i₀` is the image of `m` lifts
to a basis of the flat module `M` whose vector `i₀` is `m`. -/
private theorem Module.Basis.exists_lift_mkQ_of_isNilpotent {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] {I : Ideal R} (hI : IsNilpotent I) {ι : Type*}
    (b : Module.Basis ι (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) (i₀ : ι) (m : M)
    (hm : (I • (⊤ : Submodule R M)).mkQ m = b i₀) :
    ∃ b' : Module.Basis ι R M, b' i₀ = m ∧ ∀ i, (I • (⊤ : Submodule R M)).mkQ (b' i) = b i := by
  classical
  let lift : ι → M := fun i => if i = i₀ then m else (Submodule.mkQ_surjective _ (b i)).choose
  have hlift : (I • (⊤ : Submodule R M)).mkQ ∘ lift = b := by
    funext i
    by_cases hi : i = i₀
    · subst hi
      simpa [lift] using hm
    · simpa [lift, hi] using (Submodule.mkQ_surjective _ (b i)).choose_spec
  have h := (Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent I hI
    lift).mp (hlift ▸ ⟨b.linearIndependent, b.span_eq⟩)
  refine ⟨.mk h.1 h.2.ge, by simp [lift], fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  exact congrFun hlift i

/-- Over a nilpotent ideal `I` of `R`, a basis of `A ⧸ I A` over `R ⧸ I` whose vector `i₀` is `1`
lifts to a basis of the flat `R`-algebra `A` whose vector `i₀` is `1`. -/
private theorem Module.Basis.exists_lift_quotient_map_of_isNilpotent {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] {I : Ideal R} (hI : IsNilpotent I)
    [Algebra (R ⧸ I) (A ⧸ I.map (algebraMap R A))]
    [IsScalarTower R (R ⧸ I) (A ⧸ I.map (algebraMap R A))] {ι : Type*}
    (b : Module.Basis ι (R ⧸ I) (A ⧸ I.map (algebraMap R A))) (i₀ : ι) (hb : b i₀ = 1) :
    ∃ b' : Module.Basis ι R A, b' i₀ = 1 ∧ ∀ i, Ideal.Quotient.mk _ (b' i) = b i := by
  let e : (A ⧸ I.map (algebraMap R A)) ≃ₗ[R ⧸ I] (A ⧸ I • (⊤ : Submodule R A)) :=
    ((Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I)).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)).symm.extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective
  obtain ⟨b', hb'0, hb'⟩ := Module.Basis.exists_lift_mkQ_of_isNilpotent hI (b.map e) i₀ 1
    (by rw [Module.Basis.map_apply, hb]; rfl)
  refine ⟨b', hb'0, fun i => ?_⟩
  show e.symm ((I • (⊤ : Submodule R A)).mkQ (b' i)) = b i
  rw [hb' i, Module.Basis.map_apply, LinearEquiv.symm_apply_apply]

/-- **Lifting a basis through a reduction by a nilpotent ideal.** Let `R' → R` be surjective with
nilpotent kernel `I`, let `A'` be a flat `R'`-algebra and let `A' → A` be a surjection onto an
`R`-algebra with kernel `IA'`, compatible with the base rings. Then a basis of `A` over `R` whose
first vector is `1` lifts to a basis of `A'` over `R'` whose first vector is `1`. -/
theorem Algebra.exists_basis_lift_of_nilpotent_ker
    {R' R A' A : Type u} [CommRing R'] [CommRing R] [CommRing A'] [CommRing A]
    [Algebra R' R] [Algebra R' A'] [Algebra R A] [Module.Flat R' A']
    (hsurj : Function.Surjective (algebraMap R' R))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (φ : A' →+* A) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.map (algebraMap R' A') (RingHom.ker (algebraMap R' R)))
    (hcompat : ∀ c : R', φ (algebraMap R' A' c) = algebraMap R A (algebraMap R' R c))
    {d : ℕ} [NeZero d] (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) :
    ∃ b' : Module.Basis (Fin d) R' A', b' 0 = 1 ∧ ∀ i, φ (b' i) = b i := by
  classical
  set I := RingHom.ker (algebraMap R' R)
  let eR : (R' ⧸ I) ≃+* R := RingHom.quotientKerEquivOfSurjective (f := algebraMap R' R) hsurj
  let : Algebra (R' ⧸ I) R := eR.toRingHom.toAlgebra
  let : Algebra (R' ⧸ I) A := Algebra.compHom _ eR.toRingHom
  -- the given basis, read over `R' ⧸ I`
  let b₀ : Module.Basis (Fin d) (R' ⧸ I) A := b.mapCoeffs eR.symm fun c x => by
    show eR (eR.symm c) • x = c • x
    rw [eR.apply_symm_apply]
  have hb₀_apply : ∀ i : Fin d, b₀ i = b i := b.mapCoeffs_apply _ _
  -- the kernel of the reduction, as an ideal of `A'`
  set J : Ideal A' := Ideal.map (algebraMap R' A') I
  let : Algebra (R' ⧸ I) (A' ⧸ J) :=
    (Ideal.quotientMap J (algebraMap R' A') Ideal.le_comap_map).toAlgebra
  have : IsScalarTower R' (R' ⧸ I) (A' ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the reduction identifies `A' ⧸ J` with `A`
  let eJ : (A' ⧸ J) ≃+* A :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have heJmk : ∀ a : A', eJ (Ideal.Quotient.mk J a) = φ a := fun _ => rfl
  let eRed : A ≃ₐ[R' ⧸ I] (A' ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := eJ.symm) fun r => by
      obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
      refine eJ.injective ?_
      show eJ (eJ.symm (algebraMap R A (eR (Ideal.Quotient.mk I r')))) =
        eJ (Ideal.Quotient.mk J (algebraMap R' A' r'))
      rw [eJ.apply_symm_apply, heJmk, hcompat]
      exact congrArg (algebraMap R A)
        (RingHom.quotientKerEquivOfSurjective_apply_mk (f := algebraMap R' R) hsurj r')
  let bRed : Module.Basis (Fin d) (R' ⧸ I) (A' ⧸ J) := b₀.map eRed.toLinearEquiv
  have hbRedone : bRed 0 = 1 := by
    rw [Module.Basis.map_apply, hb₀_apply, hb]
    exact map_one eRed
  -- lift the basis through the reduction
  obtain ⟨b', hb'0, hb'⟩ :=
    Module.Basis.exists_lift_quotient_map_of_isNilpotent hnil bRed 0 hbRedone
  refine ⟨b', hb'0, fun i => ?_⟩
  calc φ (b' i) = eJ (Ideal.Quotient.mk J (b' i)) := (heJmk (b' i)).symm
    _ = eJ (bRed i) := congrArg eJ (hb' i)
    _ = b i := by
      rw [Module.Basis.map_apply, hb₀_apply]
      exact eJ.apply_symm_apply (b i)

namespace AlgebraicGeometry

/-- The pointed table of a composite `i ≫ a` is the pointed table of `a` extended along the map
of `i` on global sections. -/
private theorem pointedFamilyTable_comp (d : ℕ) [NeZero d] {T T' : Scheme.{u}} (i : T ⟶ T')
    (a : T' ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) :
    pointedFamilyTable.{u} d (i ≫ a) = (pointedFamilyTable.{u} d a).map i.appTop.hom := by
  refine PointedFiniteFreeAlgebra.ext ?_ (funext fun k => ?_)
  · rw [PointedFiniteFreeAlgebra.map_table, pointedFamilyTable_table.{u} d (i ≫ a),
      pointedFamilyTable_table.{u} d a, Category.assoc]
    exact ((representation.{u} d).naturality i _).symm
  · rw [PointedFiniteFreeAlgebra.map_coord, pointedFamilyTable_coord.{u} d (i ≫ a) k,
      pointedFamilyTable_coord.{u} d a k]
    rfl

/-- The algebra of the table of a point of `V_d = pi_d^{-1}(U_d)` over an affine scheme is
syntomic over its global sections (Tag 0FL0). -/
private theorem algebraSyntomic_carrier_pointedFamilyTable (d : ℕ) [NeZero d] {T : Scheme.{u}}
    [IsAffine T] (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d))
    (ha : Set.range a.base ⊆ Set.range (universalSyntomicPreimage.{u} d).ι.base) :
    Algebra.Syntomic Γ(T, ⊤) (Carrier (pointedFamilyTable.{u} d a).table) := by
  classical
  let := (universalAlgebraStructure d).ring
  let := (universalAlgebraStructure d).algebra
  set F := universalFamily.{u} d (universalAlgebraStructure d)
  set fT : T ⟶ scheme.{u} d := a ≫ F
  have : IsAffine (universalTotalScheme.{u} d (universalAlgebraStructure d)) := by
    dsimp [universalTotalScheme]
    infer_instance
  let : Algebra Γ(T, ⊤) Γ(pullback F fT, ⊤) := (pullback.snd F fT).appTop.hom.toAlgebra
  let : Algebra Γ(scheme.{u} d, ⊤)
      Γ(universalTotalScheme.{u} d (universalAlgebraStructure d), ⊤) := F.appTop.hom.toAlgebra
  have hPsyn : Algebra.Syntomic Γ(T, ⊤) Γ(pullback F fT, ⊤) :=
    algebraSyntomic_of_affineSyntomic (pullback.snd F fT)
      ((factorsThrough_universalSyntomicOpen_iff d T fT).mp
        ((range_subset_universalSyntomicPreimage_iff.{u} d T a).mp ha))
  set m : FiniteFreeAlgebra Γ(T, ⊤) d := (pointedFamilyTable.{u} d a).table
  have hbP0 : affinePullbackGammaBasis F fT (Fin d) (universalTotalGammaBasis.{u} d) 0 = 1 :=
    affinePullbackGammaBasis_zero F fT d (universalTotalGammaBasis.{u} d)
      (universalTotalGammaBasis_zero.{u} d)
  have hbPtable : ofBasis (affinePullbackGammaBasis F fT (Fin d)
        (universalTotalGammaBasis.{u} d)) hbP0 = (representation.{u} d).equiv T fT :=
    affinePullbackGammaBasis_structure_of_map F fT (universalTotalGammaBasis.{u} d)
      (universalTotalGammaBasis_zero.{u} d) (universalTotalGammaBasis_structure.{u} d)
  exact Stacks.SyntomicLocus.Algebra.Syntomic.of_algEquiv
    (FiniteFreeAlgebra.algEquivOfBasisEq
      (affinePullbackGammaBasis F fT (Fin d) (universalTotalGammaBasis.{u} d))
      (Carrier.basis m) hbP0 (Carrier.basis_zero m)
      (by rw [hbPtable, ← pointedFamilyTable_table.{u} d a, ofBasis_carrierBasis]))

/-- **The lifting problem of Stacks 0FL3 for `V_d`.** Along a morphism of affine schemes that is
surjective on global sections with nilpotent kernel and surjective on points, with artinian
nonzero global sections on the source, every point of `V_d = pi_d^{-1}(U_d)` extends to the
target. -/
theorem exists_lift_universalSyntomicPreimage (d : ℕ) [NeZero d]
    {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
    (hsurj : Function.Surjective i.appTop.hom)
    (hnil : IsNilpotent (RingHom.ker i.appTop.hom))
    (hbase : Function.Surjective i.base)
    [IsArtinianRing Γ(T, ⊤)] [Nontrivial Γ(T, ⊤)]
    (α : T ⟶ (universalSyntomicPreimage.{u} d).toScheme) :
    ∃ γ : T' ⟶ (universalSyntomicPreimage.{u} d).toScheme, i ≫ γ = α := by
  classical
  set a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d) :=
    α ≫ (universalSyntomicPreimage.{u} d).ι with ha
  -- `V_d` membership, and the syntomicity it gives by Tag 0FL0
  have harange : Set.range a.base ⊆ Set.range (universalSyntomicPreimage.{u} d).ι.base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨α.base t, by simp [ha]⟩
  -- the algebra of the table of the given point, with its section
  set p := pointedFamilyTable.{u} d a
  set m : FiniteFreeAlgebra Γ(T, ⊤) d := p.table
  have : Algebra.Syntomic Γ(T, ⊤) (Carrier m) :=
    algebraSyntomic_carrier_pointedFamilyTable d a harange
  have : Nontrivial (Carrier m) := Carrier.nontrivial m
  -- the deformation problem of Tag 0FL3
  let : Algebra Γ(T', ⊤) Γ(T, ⊤) := i.appTop.hom.toAlgebra
  have hsurj' : Function.Surjective (algebraMap Γ(T', ⊤) Γ(T, ⊤)) := hsurj
  have hnil' : IsNilpotent (RingHom.ker (algebraMap Γ(T', ⊤) Γ(T, ⊤))) := hnil
  obtain ⟨B', hB'ring, hB'alg, hB'syn, hB'fin, sec, red, hredsurj, hredker, hredc, hreds⟩ :=
    Algebra.exists_finite_syntomic_section_lift (C' := Γ(T', ⊤)) (C := Γ(T, ⊤))
      (B := Carrier m) hsurj' hnil' p.sec
  have : Module.Flat Γ(T', ⊤) B' := hB'syn.flat
  obtain ⟨b', hb'0, hb'red⟩ :=
    Algebra.exists_basis_lift_of_nilpotent_ker hsurj' hnil' red hredsurj hredker hredc
      (Carrier.basis m) (Carrier.basis_zero m)
  -- the lifted point of `Y_d`
  set a' : T' ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d) :=
    pointedFamilyHom.{u} d (PointedFiniteFreeAlgebra.ofBasisSection b' hb'0 sec) with ha'
  have hcomp : i ≫ a' = a := by
    refine universalTotal_hom_ext.{u} d ?_
    rw [pointedFamilyTable_comp, ha', pointedFamilyTable_pointedFamilyHom]
    refine PointedFiniteFreeAlgebra.ext ?_ (funext fun k => ?_)
    · have hmap : FiniteFreeAlgebra.map i.appTop.hom (FiniteFreeAlgebra.ofBasis b' hb'0) = m := by
        rw [FiniteFreeAlgebra.ofBasis_map i.appTop.hom red hredc b' hb'0
          (Carrier.basis m) (Carrier.basis_zero m) hb'red, ofBasis_carrierBasis]
      exact hmap
    · have h : p.sec (red (b' k)) = p.coord k := by
        rw [hb'red k, Carrier.basis_apply, PointedFiniteFreeAlgebra.sec_basisVector]
      exact (hreds (b' k)).symm.trans h
  -- its image again lies in `V_d`
  have hrange : Set.range a'.base ⊆ Set.range (universalSyntomicPreimage.{u} d).ι.base := by
    rintro _ ⟨t', rfl⟩
    obtain ⟨t, rfl⟩ := hbase t'
    exact harange ⟨t, (congrArg (fun k : T ⟶ _ => k.base t) hcomp).symm⟩
  exact ⟨IsOpenImmersion.lift _ a' hrange, (cancel_mono (universalSyntomicPreimage.{u} d).ι).1
    (by rwa [Category.assoc, IsOpenImmersion.lift_fac])⟩

/-- The open `V_d` is locally of finite presentation over the terminal scheme: it is open in the
total space of the universal family, which is of finite presentation over `X_d`, which is of
finite presentation over the integers. -/
theorem universalSyntomicPreimage_locallyOfFinitePresentation (d : ℕ) [NeZero d] :
    LocallyOfFinitePresentation
      (specULiftZIsTerminal.from (universalSyntomicPreimage.{u} d).toScheme) := by
  have : LocallyOfFinitePresentation
      (universalFamily.{u} d (universalAlgebraStructure d)) :=
    (universalFamily_isFinite_flat_locallyOfFinitePresentation.{u} d).2.2
  have : LocallyOfFinitePresentation (specULiftZIsTerminal.from (scheme.{u} d)) :=
    scheme_locallyOfFinitePresentation d
  rw [show specULiftZIsTerminal.from (universalSyntomicPreimage.{u} d).toScheme =
      (universalSyntomicPreimage.{u} d).ι ≫
        universalFamily.{u} d (universalAlgebraStructure d) ≫
          specULiftZIsTerminal.from (scheme.{u} d) from
    specULiftZIsTerminal.hom_ext _ _]
  infer_instance

/-- On global sections, `Spec φ` is `φ` up to the identifications `Γ(Spec B, ⊤) ≅ B`. -/
private theorem Spec.map_appTop_hom_apply {B' B : CommRingCat.{u}} (φ : B' ⟶ B)
    (x : Γ(Spec B', ⊤)) :
    (Spec.map φ).appTop.hom x = (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.symm
      (φ.hom ((Scheme.ΓSpecIso B').commRingCatIsoToRingEquiv x)) := by
  rw [show (Spec.map φ).appTop = (Scheme.ΓSpecIso B').hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv by
    rw [Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]]
  rfl

/-- `Spec φ` is surjective on global sections when `φ` is surjective. -/
private theorem Spec.map_appTop_surjective {B' B : CommRingCat.{u}} {φ : B' ⟶ B}
    (hφ : Function.Surjective φ.hom) : Function.Surjective (Spec.map φ).appTop.hom := by
  intro z
  obtain ⟨y, hy⟩ := hφ ((Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv z)
  refine ⟨(Scheme.ΓSpecIso B').commRingCatIsoToRingEquiv.symm y, ?_⟩
  rw [Spec.map_appTop_hom_apply, RingEquiv.apply_symm_apply, hy, RingEquiv.symm_apply_apply]

/-- The kernel of `Spec φ` on global sections is nilpotent when the kernel of `φ` squares to
zero. -/
private theorem Spec.isNilpotent_ker_map_appTop {B' B : CommRingCat.{u}} {φ : B' ⟶ B}
    (hφ : RingHom.ker φ.hom ^ 2 = ⊥) : IsNilpotent (RingHom.ker (Spec.map φ).appTop.hom) := by
  have hker : RingHom.ker (Spec.map φ).appTop.hom =
      Ideal.map (Scheme.ΓSpecIso B').commRingCatIsoToRingEquiv.symm (RingHom.ker φ.hom) := by
    rw [Ideal.map_symm]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, Spec.map_appTop_hom_apply,
      map_eq_zero_iff _ (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.symm.injective]
  refine ⟨2, ?_⟩
  rw [hker, ← Ideal.map_pow, hφ, Ideal.map_bot]
  rfl

/-- `Spec φ` is surjective when its source is local artinian and its target is local. -/
private theorem Spec.map_base_surjective_of_isArtinianRing {B' B : CommRingCat.{u}} (φ : B' ⟶ B)
    [IsLocalRing B'] [IsArtinianRing B'] [IsLocalRing B] :
    Function.Surjective (Spec.map φ).base := by
  have hsub : ∀ y z : PrimeSpectrum B', y = z := fun y z => PrimeSpectrum.ext
    ((IsLocalRing.eq_maximalIdeal (inferInstance : y.asIdeal.IsMaximal)).trans
      (IsLocalRing.eq_maximalIdeal (inferInstance : z.asIdeal.IsMaximal)).symm)
  exact fun y => ⟨IsLocalRing.closedPoint B, hsub _ y⟩

/-- **Stacks Project, Tag 0FL3,** the geometric assertion. The preimage
`V_d = pi_d^{-1}(U_d)` of the open of Tag 0FL0 under the universal finite free family of rank `d`
is smooth over the terminal scheme `Spec(ULift ZZ)`, which is `Spec(ZZ)` in the universe of the
test schemes. -/
@[stacks 0FL3 "the geometric assertion: V_d = pi_d^{-1}(U_d) is smooth over Z, for the open U_d \
of Tag 0FL0 and the universal finite free family pi_d of Tag 0FKZ. Stated over the terminal \
scheme Spec(ULift Z) of the universe of the test schemes."]
public instance universalSyntomicPreimage_smooth_uLift (d : ℕ) [NeZero d] :
    Smooth (specULiftZIsTerminal.from (universalSyntomicPreimage.{u} d).toScheme) := by
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have := universalSyntomicPreimage_locallyOfFinitePresentation.{u} d
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine eq_top_iff.2 fun x _ => ?_
  rw [Scheme.Hom.mem_smoothLocus]
  set f := specULiftZIsTerminal.from (universalSyntomicPreimage.{u} d).toScheme
  have hsmoothAt : InfinitesimalLifting.SmoothAt f x := by
    refine ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness f x).out 3 1).mp
      fun B' B φ hφ _ αm β hcomm hclosed => ?_
    have hsq := (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ).2.2.2
    obtain ⟨hlocB', hlocB, hartB', hartB, hsurjφ, hlen⟩ := hφ
    -- the global-sections data of `Spec φ`
    have : IsArtinianRing Γ(Spec B, ⊤) :=
      (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.symm.isArtinianRing
    have : Nontrivial Γ(Spec B, ⊤) :=
      (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.symm.injective.nontrivial
    obtain ⟨γ, hγ⟩ :=
      exists_lift_universalSyntomicPreimage.{u} d (Spec.map φ) (Spec.map_appTop_surjective hsurjφ)
        (Spec.isNilpotent_ker_map_appTop hsq) (Spec.map_base_surjective_of_isArtinianRing φ) αm
    exact ⟨γ, hγ, specULiftZIsTerminal.hom_ext _ _⟩
  exact hsmoothAt.formallySmooth_stalkMap f x

/-- **Stacks Project, Tag 0FL3,** the geometric assertion, in the literal form of the source:
`V_d = pi_d^{-1}(U_d)` is smooth over the spectrum of the integers themselves. -/
@[stacks 0FL3 "the geometric assertion: V_d = pi_d^{-1}(U_d) is smooth over Z, for the open U_d \
of Tag 0FL0 and the universal finite free family pi_d of Tag 0FKZ. Stated over Spec(Z) itself."]
public instance universalSyntomicPreimage_smooth (d : ℕ) [NeZero d] :
    Smooth (specZIsTerminal.from (universalSyntomicPreimage d).toScheme) := by
  let e : Spec (.of (ULift.{0} ℤ)) ⟶ Spec (.of ℤ) := specZIsTerminal.from _
  have : IsIso e := isIso_of_isTerminal specULiftZIsTerminal specZIsTerminal e
  have : Smooth e := inferInstance
  have : Smooth (specULiftZIsTerminal.from (universalSyntomicPreimage d).toScheme) :=
    universalSyntomicPreimage_smooth_uLift.{0} d
  rw [show specZIsTerminal.from (universalSyntomicPreimage d).toScheme =
      specULiftZIsTerminal.from (universalSyntomicPreimage d).toScheme ≫ e from
    specZIsTerminal.hom_ext _ _]
  infer_instance

end AlgebraicGeometry

end
