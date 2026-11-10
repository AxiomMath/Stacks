module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartRigEtaleDiagonalMono
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# A flat formal space over a cdvr with rig-étale rig-surjective diagonal is a point or empty

The structure morphism `q : X' ⟶ Spf A` is a monomorphism, its diagonal being an isomorphism
over a covering by fibre products of charts; `Spf A` has a single point; so `q` is an isomorphism
if `X'` has a point and `X'` is initial otherwise.

## Main results

* `AlgebraicGeometry.FormalSpace.mono_of_isRigEtale_of_isRigSurjective_diagonal`
* `AlgebraicGeometry.FormalSpace.pointsULift_formalSpectrum_eq_residuePoint`
* `AlgebraicGeometry.FormalSpace.nonempty_isInitial_of_isEmpty_pointsULift`
* `isIso_or_isInitial_of_isFlat_of_isRigEtale_of_isRigSurjective_diagonal`, in the namespace
  `AlgebraicGeometry.FormalSpace`

## References

* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A] (D : QuotientSystem B S hS A)

/-- **A flat formal space over a cdvr with rig-étale rig-surjective diagonal is a subsheaf of the
base.** Under the hypotheses of
`isIso_pullback_map_of_isRigEtale_of_isRigSurjective_diagonal`, the structure morphism
`q : X' ⟶ Spf A` is a monomorphism: the relative diagonal of `q` is a monomorphism through which
every member of the covering `{Uᵢ ×_{Spf A} Uⱼ ⟶ X' ×_{Spf A} X'}` factors, since
`Uᵢ ×_{X'} Uⱼ ⟶ Uᵢ ×_{Spf A} Uⱼ` is an isomorphism; so it is an isomorphism. -/
theorem mono_of_isRigEtale_of_isRigSurjective_diagonal
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A) {X' : FppfSheaf B S hS}
    (q : X' ⟶ formalSpectrum D) (hX' : IsLocallyNoetherian B S hS X')
    (hq : IsLocallyOfFiniteType B S hS q) (hqflat : IsFlat B S hS q)
    (hdiagE : IsRigEtale B S hS (pullback.diagonal q))
    (hdiagS : IsRigSurjective B S hS (pullback.diagonal q)) : Mono q := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hX'fas, I, U, a, haff, haet, hsurj, hnoeth⟩ := id hX'
  have ha : ∀ i, IsRepresentableEtale B S hS (a i) := haet
  -- pulling back the atlas along any map to `X'` gives a covering
  have hcov : ∀ {Y : FppfSheaf B S hS} (f : Y ⟶ X'),
      Sheaf.IsLocallySurjective (Sigma.desc fun i ↦ pullback.snd (a i) f) := fun f ↦
    isLocallySurjective_sigmaDesc_of_isPullback B S hS f
      (fun i ↦ IsPullback.of_hasPullback (a i) f) hsurj
  -- the covering `{X' ×_{Spf A} Uⱼ ⟶ X' ×_{Spf A} X'}` and its refinement
  let e : ∀ j, pullback (a j) (pullback.snd q q) ⟶ pullback q q :=
    fun j ↦ pullback.snd (a j) (pullback.snd q q)
  let w : ∀ j i, pullback (a i) (e j ≫ pullback.fst q q) ⟶ pullback (a j) (pullback.snd q q) :=
    fun j i ↦ pullback.snd (a i) (e j ≫ pullback.fst q q)
  -- every member of the refined covering factors through the diagonal
  have hfac : ∀ s : Σ j, I, ∃ r : pullback (a s.2) (e s.1 ≫ pullback.fst q q) ⟶ X',
      r ≫ pullback.diagonal q = w s.1 s.2 ≫ e s.1 := by
    rintro ⟨j, i⟩
    set Z := pullback (a i) (e j ≫ pullback.fst q q)
    let u₁ : Z ⟶ U i := pullback.fst _ _
    let u₂ : Z ⟶ U j := w j i ≫ pullback.fst (a j) (pullback.snd q q)
    have hu₁ : u₁ ≫ a i = w j i ≫ e j ≫ pullback.fst q q := pullback.condition
    have hu₂ : u₂ ≫ a j = w j i ≫ e j ≫ pullback.snd q q := by
      simp only [u₂, Category.assoc, e]
      rw [pullback.condition]
    have hcond : u₁ ≫ a i ≫ q = u₂ ≫ a j ≫ q := by
      rw [reassoc_of% hu₁, reassoc_of% hu₂, pullback.condition]
    let ℓ : Z ⟶ pullback (a i ≫ q) (a j ≫ q) := pullback.lift u₁ u₂ hcond
    have hiso := isIso_pullback_map_of_isRigEtale_of_isRigSurjective_diagonal B S hS D hAadic hAc
      q hX' hq hqflat hdiagE hdiagS (a i) (a j)
      (haff i) (haff j) (ha i) (ha j)
    set g := pullback.map (a i) (a j) (a i ≫ q) (a j ≫ q) (𝟙 _) (𝟙 _) q (by simp) (by simp)
    have hg₁ : g ≫ pullback.fst (a i ≫ q) (a j ≫ q) = pullback.fst (a i) (a j) := by simp [g]
    have hg₂ : g ≫ pullback.snd (a i ≫ q) (a j ≫ q) = pullback.snd (a i) (a j) := by simp [g]
    refine ⟨ℓ ≫ inv g ≫ pullback.fst (a i) (a j) ≫ a i, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, ← hg₁, Category.assoc g,
        IsIso.inv_hom_id_assoc, ← Category.assoc, pullback.lift_fst, hu₁, Category.assoc]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.condition, ← hg₂,
        Category.assoc g, IsIso.inv_hom_id_assoc, ← Category.assoc, pullback.lift_snd, hu₂,
        Category.assoc]
  obtain ⟨r, hr⟩ := Sheaf.exists_comp_eq_of_isLocallySurjective_sigmaDesc (pullback.diagonal q)
    (𝟙 _) (fun s : Σ j, I ↦ w s.1 s.2 ≫ e s.1)
    (isLocallySurjective_sigmaDesc_comp_sigmaDesc B S hS e w (hcov _) fun j ↦ hcov _)
    (fun s ↦ (hfac s).imp fun r hr ↦ by rw [hr, Category.comp_id])
  have : IsSplitEpi (pullback.diagonal q) := ⟨⟨r, hr⟩⟩
  have : IsIso (pullback.diagonal q) := isIso_of_mono_of_epi _
  exact (pullback.isIso_diagonal_iff q).mp this

omit [IsLinearTopology A A] in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The formal spectrum of a complete discrete valuation ring has one point.** Every point of
`Spf A` is its closed point: a point is given by a ring map `A ⧸ I → Ω` into a field for a weak
ideal of definition `I`, whose kernel is a prime containing a power of the maximal ideal, hence
the maximal ideal. -/
theorem pointsULift_formalSpectrum_eq_residuePoint
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (z : Space.pointsULift.{u + 1} B S hS (formalSpectrum D).obj) :
    z = (residuePoint hAadic D).class B S hS _ := by
  classical
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS _)) :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of p.carrier)))
  obtain ⟨I, t, ht⟩ := exists_factorsThroughStage_of_compactSpace
    ⟨IsLocalRing.maximalIdeal A, TopologicalRing.isWeakIdealOfDefinition_of_isAdic hAadic⟩ D _ hcpt
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm p.value)
  have h₁ : p.value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫
        formalSpectrumInclusion D (OrderDual.toDual I)) :=
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).apply_symm_apply p.value).symm.trans
      (congrArg _ ht.symm)
  let f : Spec (CommRingCat.of p.carrier) ⟶ Spec (CommRingCat.of (A ⧸ I.1)) := t.left.hom
  let φ : A ⧸ I.1 →+* p.carrier := (Spec.preimage f).hom
  have hφ : t.left.hom = Spec.map (CommRingCat.ofHom φ) := (Spec.map_preimage f).symm
  -- `I` lies in the maximal ideal and contains a power of it
  have hIm : I.1 ≤ IsLocalRing.maximalIdeal A := by
    refine IsLocalRing.le_maximalIdeal fun htop => ?_
    have hmopen : IsOpen ((IsLocalRing.maximalIdeal A : Ideal A) : Set A) := by
      simpa using (isAdic_iff.mp hAadic).1 1
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
      (I.2.2 1 (htop ▸ Submodule.mem_top) (hmopen.mem_nhds (IsLocalRing.maximalIdeal A).zero_mem))
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr (by simpa using hn n le_rfl))
  obtain ⟨N, hN⟩ := (isAdic_iff.mp hAadic).2 (I.1 : Set A) (I.2.1.mem_nhds I.1.zero_mem)
  -- the closed point read on the stage `I`
  let mI : { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J } := residueStage hAadic
  let t₂ : (residuePoint hAadic D).siteObject B S hS _ ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.stage I) :=
    (BigAffineFppf.inclusion B S hS).map (D.transition (show I.1 ≤ mI.1 from hIm))
  have h₂ : (residuePoint hAadic D).value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t₂ ≫
        formalSpectrumInclusion D (OrderDual.toDual I)) :=
    congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) (colimit.w
      (formalSpectrumDiagram D)
      (homOfLE (show OrderDual.toDual mI ≤ OrderDual.toDual I from hIm))).symm
  let : Field (A ⧸ mI.1) := Ideal.Quotient.field _
  refine FieldValuedPointULift.class_eq_of_ker_eq B S hS D I p _ t t₂ h₁ h₂ φ
    (Ideal.Quotient.factor hIm) hφ (toScheme_map_transition D hIm) ?_
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change φ (Ideal.Quotient.mk I.1 r) = 0 ↔ Ideal.Quotient.mk mI.1 r = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hprime : (RingHom.ker (φ.comp (Ideal.Quotient.mk I.1))).IsPrime := RingHom.ker_isPrime _
  have heq := (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hprime.ne_top fun y hy ↦
    hprime.mem_of_pow_mem N (by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr
        (hN (Ideal.pow_mem_pow hy N)), map_zero])
  change r ∈ RingHom.ker (φ.comp (Ideal.Quotient.mk I.1)) ↔ r ∈ IsLocalRing.maximalIdeal A
  rw [← heq]

set_option synthInstance.maxHeartbeats 400000 in
-- synthesizing `Mono (initial.to F)` in the category of fppf sheaves exceeds the default
-- typeclass heartbeats
/-- **An fppf sheaf without points is initial.** A section of the sheaf over a nonempty object of
the site gives a field-valued point at the residue field of a point of that object, so all its
sections live over empty objects, which the empty sieve covers. Hence the morphism from the
initial sheaf is a surjection of sheaves; it is a monomorphism, initial objects of a category of
sheaves of sets being strict, so it is an isomorphism. -/
theorem nonempty_isInitial_of_isEmpty_pointsULift {F : FppfSheaf B S hS}
    (hF : IsEmpty (Space.pointsULift.{u + 1} B S hS F.obj)) : Nonempty (IsInitial F) := by
  classical
  have hT : ∀ (T : BigFppfOver B S hS) (_ : F.obj.obj (Opposite.op T)),
      IsEmpty ((BigFppfOver.toScheme B S hS).obj T) := by
    intro T s
    refine ⟨fun x => hF.false ?_⟩
    have hx := B.residueField_spec_contains T.left.property x
    exact Space.FieldValuedPointULift.class B S hS F.obj
      { carrier := T.left.1.residueField x
        contained := hx
        toBase := T.left.1.fromSpecResidueField x ≫ T.hom.1
        value := F.obj.map (Space.residueFieldMap B S hS T x hx).op s }
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let ι := initial.to F
  have : Epi ι := (Sheaf.isLocallySurjective_iff_epi ι).mp ⟨fun {T} s =>
    (BigFppfOver.topology B S hS).superset_covering bot_le
      (BigFppfOver.bot_mem_topology T (hT T s))⟩
  have : IsIso ι := isIso_of_mono_of_epi ι
  exact ⟨initialIsInitial.ofIso (asIso ι)⟩

/-- **A flat formal space over a cdvr with rig-étale rig-surjective diagonal is the base or
empty.** Let `A` be a complete discrete valuation ring with its maximal-adic topology and let
`q : X' ⟶ Spf A` be flat and locally of finite type, with `X'` locally Noetherian and relative
diagonal rig-étale and rig-surjective. Then `q` is an isomorphism or `X'` is initial.

`q` is a monomorphism (`mono_of_isRigEtale_of_isRigSurjective_diagonal`). If `X'` has a point,
some chart `a : U ⟶ X'` of an atlas has one, and `a ≫ q` is representable étale and surjective
on points, `Spf A` having a single point; so it is a surjection of sheaves, hence so is `q`. If
`X'` has no point it is initial (`nonempty_isInitial_of_isEmpty_pointsULift`). -/
theorem isIso_or_isInitial_of_isFlat_of_isRigEtale_of_isRigSurjective_diagonal
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A) {X' : FppfSheaf B S hS}
    (q : X' ⟶ formalSpectrum D) (hX' : IsLocallyNoetherian B S hS X')
    (hq : IsLocallyOfFiniteType B S hS q) (hqflat : IsFlat B S hS q)
    (hdiagE : IsRigEtale B S hS (pullback.diagonal q))
    (hdiagS : IsRigSurjective B S hS (pullback.diagonal q)) :
    IsIso q ∨ Nonempty (IsInitial X') := by
  classical
  have : Mono q := mono_of_isRigEtale_of_isRigSurjective_diagonal B S hS D hAadic hAc q hX' hq
    hqflat hdiagE hdiagS
  by_cases hpt : Nonempty (Space.pointsULift.{u + 1} B S hS X'.obj)
  · left
    obtain ⟨z⟩ := hpt
    let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    obtain ⟨-, I, U, a, haff, haet, hsurj, -⟩ := id hX'
    obtain ⟨i, zi, -⟩ := exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS a hsurj z
    have het := isRepresentableEtale_comp_of_isRigEtale_of_isRigSurjective_diagonal B S hS D hAadic
      hAc q hX' hq hqflat hdiagE hdiagS (a i) (haff i) (haet i)
    have hsurjpt : IsSurjective B S hS (a i ≫ q) := fun y =>
      ⟨zi, (pointsULift_formalSpectrum_eq_residuePoint B S hS D hAadic _).trans
        (pointsULift_formalSpectrum_eq_residuePoint B S hS D hAadic y).symm⟩
    have : Epi (a i ≫ q) := (Sheaf.isLocallySurjective_iff_epi _).mp
      (isLocallySurjective_of_isSurjective_of_isRepresentableEtale B S hS _ het hsurjpt)
    have : Epi q := epi_of_epi (a i) q
    exact isIso_of_mono_of_epi q
  · right
    exact nonempty_isInitial_of_isEmpty_pointsULift B S hS (not_nonempty_iff.mp hpt)

end AlgebraicGeometry.FormalSpace

end
