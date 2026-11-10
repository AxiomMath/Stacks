module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.GaloisAction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
public import Mathlib.Topology.Algebra.MulAction

/-!
# Picard classes of a base change descend to a finite subextension

Let `k` be a field, let `X` be a quasi-compact, quasi-separated scheme over `k`, and let `K/k` be
an algebraic extension. The base change `X_K` is the limit of the base changes `X_E` to the
finite subextensions `E/k`, so every invertible module on `X_K` is pulled back from one of the
`X_E` by [Stacks, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W) (2); hence so is every
Picard class.

When `K/k` is Galois this gives the continuity clause of
[Stacks, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT): a class pulled back from the stage
`E` is fixed by every automorphism fixing `E` pointwise, and `Gal(K/E)` is open in the Krull
topology, so every stabiliser of the Galois action on `Pic(X_K)` is open and the action is
continuous for the discrete topology.

## Main results

* `Stacks.Picard.exists_finiteSubextension_schemePullbackClass_eq`: **Tag 0B8W (2) for Picard
  classes.** Every class of `Pic(X_K)` is pulled back from `Pic(X_E)` for some finite
  subextension `E/k`, along a morphism `X_K ⟶ X_E` over `X` whose second leg is the inclusion
  `E ⊆ K`.
* `Stacks.Picard.galoisTwist_comp_eq_of_mem_fixingSubgroup`: a twist `id_X × Spec(σ)` with `σ`
  fixing `E` pointwise does not move such a morphism `X_K ⟶ X_E`.
* `Stacks.Picard.fixingSubgroup_le_stabilizer_galoisPicardAction` and
  `Stacks.Picard.isOpen_stabilizer_galoisPicardAction`: every stabiliser of the Galois action on
  `Pic(X_K)` contains `Gal(K/E)` for a stage `E` the class descends to, hence is open.
* `Stacks.Picard.continuousSMul_galoisPicardAction`: **the continuity clause of Tag 0CDT.** The
  action of `Gal(K/k)` on `Pic(X_K)` is continuous for the Krull topology on the Galois group and
  the discrete topology on the Picard group.

## Implementation notes

**The orientation of the base change.** `AlgebraicGeometry.SchemeOver.baseChange` is
`pullback X.hom (Spec.map (algebraMap k K))`, with the structure morphism of `X` as the *first*
leg, whereas the limit presentation `AlgebraicGeometry.fextPullbackConeIsLimit` has apex
`pullback (spectrumMap k K) X.hom`, with the field map first. The two are exchanged by
`CategoryTheory.Limits.pullbackSymmetry`, and the comparison morphism produced below is the
projection of that limit cone conjugated by the symmetry at both ends — the same morphism, and
the same two leg identities, as in
`AlgebraicGeometry.exists_finite_subextension_descending_isCompact_open`, which is Tag 04KU (1)
for quasi-compact opens.

**Why the conclusion is stated through a morphism and its two legs** rather than through the
limit cone: the objects of `AlgebraicGeometry.fextPullbackDiagram` are base changes in the
field-first orientation, and a statement about them would have to be transported before
`Stacks.Picard.galoisTwist` could be applied. The two leg identities are all the twist argument
uses.

**What this does not do.** The *surjectivity* clause of Tag 0CDT — that a Galois-fixed class
descends to `Pic(X)` — needs more than the reduction proved here: the fixed class must descend
to a finite *Galois* subextension and still be fixed there
(`Stacks.Picard.exists_finiteGaloisSubextension_galoisFixed` of
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageFixed.lean`),
and Galois descent must then be applied at that stage
(`Stacks.Picard.exists_schemePullbackClass_eq_of_galoisFixed` of
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageDescent.lean`,
which is Tag 0CDR with the descent cocycle normalised at the rational point). Both are proved,
and `Stacks.Picard.bijOn_schemePullbackClass_galoisFixedClasses` assembles them; it has no
remaining hypothesis beyond the tag's own.

## References

* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 04KU](https://stacks.math.columbia.edu/tag/04KU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (picardClass picardClass_eq_iff)

universe u

namespace Stacks.Picard

/-! ### A Picard class is the pullback of a class from a stage its representative descends to -/

/-- A Picard class whose chosen representative is isomorphic to the pullback of an invertible
module `N` along `f` is the pullback of the class of `N`. -/
lemma eq_schemePullbackClass_classOf {Y Z : Scheme.{u}} (f : Y ⟶ Z) (x : ofScheme Y)
    (N : Z.Modules)
    (hN : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) N)
    (e : (picardRepresentative Y.toRingedSpace x).obj ≅
      (Scheme.Modules.pullback f).obj N) :
    x = schemePullbackClass f (picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) N hN) :=
  (classOf_picardRepresentative Y.toRingedSpace x).symm.trans
    (((picardClass_eq_iff _ _ _ _ (picardRepresentative Y.toRingedSpace x).property
        (Stacks.RingedSpace.modulePullback_isInvertible_of f.toLRSHom.toShHom N hN)).2
      ⟨e⟩).trans (pullbackClass_classOf f.toLRSHom.toShHom N hN).symm)

section Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-- **Stacks Project, Tag 0B8W (2) for Picard classes.** Let `X` be a quasi-compact,
quasi-separated scheme over a field `k` and let `K/k` be an algebraic extension. Every Picard
class of the base change `X_K` is pulled back from a Picard class of the base change `X_E` to
some finite subextension `E/k`, along a morphism over `X` whose component on `Spec` is the
inclusion `E ⊆ K`. -/
theorem exists_finiteSubextension_schemePullbackClass_eq (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (x : ofScheme (SchemeOver.baseChange k K X)) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (p : SchemeOver.baseChange k K X ⟶ pullback X.hom (spectrumMap k E))
      (y : ofScheme (pullback X.hom (spectrumMap k E))),
      p ≫ pullback.fst X.hom (spectrumMap k E) =
          pullback.fst X.hom (spectrumMap k K) ∧
        p ≫ pullback.snd X.hom (spectrumMap k E) =
          pullback.snd X.hom (spectrumMap k K) ≫
            Spec.map (CommRingCat.ofHom (algebraMap E K)) ∧
        schemePullbackClass p y = x := by
  classical
  let D := fextPullbackDiagram (k := k) (K := K) X.left X.hom
  let c := fextPullbackCone (k := k) (K := K) X.left X.hom
  let eK : SchemeOver.baseChange k K X ≅ c.pt := pullbackSymmetry X.hom (spectrumMap k K)
  let _ : ∀ {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) :=
    fun {i j} g => fextPullbackTransition_isAffineHom X.left X.hom g
  let _ : ∀ i : (FExt k K)ᵒᵖ, IsAffineHom (pullback.snd (spectrumMap k i.unop.1) X.hom) :=
    fun i =>
      let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) X.hom :=
        ⟨fun sq H => isAffineHom_isStableUnderBaseChange.of_isPullback sq H⟩
      MorphismProperty.pullback_snd _ _ inferInstance
  let _ : ∀ i : (FExt k K)ᵒᵖ, CompactSpace (D.obj i) := fun i =>
    inferInstanceAs (CompactSpace (pullback (spectrumMap k i.unop.1) X.hom : Scheme.{u}))
  let _ : ∀ i : (FExt k K)ᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i =>
    let : QuasiSeparated (pullback.snd (spectrumMap k i.unop.1) X.hom) := inferInstance
    let : QuasiSeparatedSpace (pullback (spectrumMap k i.unop.1) X.hom : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (spectrumMap k i.unop.1) X.hom)
    inferInstanceAs
      (QuasiSeparatedSpace (pullback (spectrumMap k i.unop.1) X.hom : Scheme.{u}))
  -- the class, transported to the apex of the limit cone, and its chosen representative
  let x' : ofScheme c.pt := schemePullbackClass eK.inv x
  obtain ⟨i, Lᵢ, hLᵢ, ⟨e⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit D c
      (fextPullbackConeIsLimit (k := k) (K := K) X.left X.hom)
      (picardRepresentative c.pt.toRingedSpace x').obj
      (picardRepresentative c.pt.toRingedSpace x').property
  let E : IntermediateField k K := i.unop.1
  let _ : FiniteDimensional k E := i.unop.2
  let eE : pullback X.hom (spectrumMap k E) ≅ D.obj i :=
    pullbackSymmetry X.hom (spectrumMap k E)
  let p : SchemeOver.baseChange k K X ⟶ pullback X.hom (spectrumMap k E) :=
    eK.hom ≫ c.π.app i ≫ eE.inv
  -- the two legs of the cone projection
  have hq : c.π.app i ≫ pullback.fst (spectrumMap k E) X.hom =
        pullback.fst (spectrumMap k K) X.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap E K)) ∧
      c.π.app i ≫ pullback.snd (spectrumMap k E) X.hom =
        pullback.snd (spectrumMap k K) X.hom := by
    dsimp [c, fextPullbackCone, fextPullbackDiagram, fextOverCone, fextOverDiagram]
    simp only [Over.pullback_map_left, Over.homMk_left]
    exact ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hKfst : eK.hom ≫ pullback.fst (spectrumMap k K) X.hom =
      pullback.snd X.hom (spectrumMap k K) := pullbackSymmetry_hom_comp_fst ..
  have hKsnd : eK.hom ≫ pullback.snd (spectrumMap k K) X.hom =
      pullback.fst X.hom (spectrumMap k K) := pullbackSymmetry_hom_comp_snd ..
  have hEfst : eE.inv ≫ pullback.fst X.hom (spectrumMap k E) =
      pullback.snd (spectrumMap k E) X.hom := pullbackSymmetry_inv_comp_fst ..
  have hEsnd : eE.inv ≫ pullback.snd X.hom (spectrumMap k E) =
      pullback.fst (spectrumMap k E) X.hom := pullbackSymmetry_inv_comp_snd ..
  let y := picardClass (D.obj i).presheaf (structureIsSheaf (D.obj i).toRingedSpace) Lᵢ hLᵢ
  refine ⟨E, inferInstance, p, schemePullbackClass eE.hom y, ?_, ?_, ?_⟩
  · calc p ≫ pullback.fst X.hom (spectrumMap k E)
        = eK.hom ≫ c.π.app i ≫ (eE.inv ≫ pullback.fst X.hom (spectrumMap k E)) := by
          simp only [p, Category.assoc]
      _ = eK.hom ≫ c.π.app i ≫ pullback.snd (spectrumMap k E) X.hom := by rw [hEfst]
      _ = eK.hom ≫ pullback.snd (spectrumMap k K) X.hom := by rw [hq.2]
      _ = pullback.fst X.hom (spectrumMap k K) := hKsnd
  · have h1 : p ≫ pullback.snd X.hom (spectrumMap k E) =
        eK.hom ≫ (c.π.app i ≫ pullback.fst (spectrumMap k E) X.hom) := by
      simp only [p, Category.assoc]
      rw [hEsnd]
    rw [h1, hq.1]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap E K))) hKfst)
  · have hpe : p ≫ eE.hom = eK.hom ≫ c.π.app i := by
      simp only [p, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hx' : x' = schemePullbackClass (c.π.app i) y :=
      eq_schemePullbackClass_classOf (c.π.app i) x' Lᵢ hLᵢ e
    calc schemePullbackClass p (schemePullbackClass eE.hom y)
        = schemePullbackClass (p ≫ eE.hom) y :=
          schemePullbackClass_comp _ _ _
      _ = schemePullbackClass (eK.hom ≫ c.π.app i) y := by
          rw [hpe]
      _ = schemePullbackClass eK.hom x' := by
          rw [← schemePullbackClass_comp, ← hx']
      _ = schemePullbackClass eK.hom (schemePullbackClass eK.inv x) := rfl
      _ = x := by
          rw [schemePullbackClass_comp, eK.hom_inv_id, schemePullbackClass_id]

end Descent

/-! ### Continuity of the Galois action -/

section Continuity

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

omit [IsGalois k K] in
/-- A twist `id_X × Spec(σ)` with `σ` fixing the intermediate field `E` pointwise does not move a
morphism `X_K ⟶ X_E` over `X` whose `Spec` component is the inclusion `E ⊆ K`. -/
lemma galoisTwist_comp_eq_of_mem_fixingSubgroup (X : Over (Spec (.of k)))
    (E : IntermediateField k K) (σ : K ≃ₐ[k] K) (hσ : σ ∈ E.fixingSubgroup)
    (p : SchemeOver.baseChange k K X ⟶ pullback X.hom (spectrumMap k E))
    (hp₁ : p ≫ pullback.fst X.hom (spectrumMap k E) =
      pullback.fst X.hom (spectrumMap k K))
    (hp₂ : p ≫ pullback.snd X.hom (spectrumMap k E) =
      pullback.snd X.hom (spectrumMap k K) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E K))) :
    galoisTwist k K X σ ≫ p = p := by
  have hfix : ∀ y : K, y ∈ E → σ y = y := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    exact hσ
  have hincl : specMapAlgAut k K σ ≫ Spec.map (CommRingCat.ofHom (algebraMap E K)) =
      Spec.map (CommRingCat.ofHom (algebraMap E K)) := by
    rw [show specMapAlgAut k K σ =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) from rfl, ← Spec.map_comp,
      Spec.map_inj]
    ext y
    exact hfix y.1 y.2
  apply pullback.hom_ext
  · rw [Category.assoc, hp₁, galoisTwist_comp_fst]
  · rw [Category.assoc, hp₂, ← Category.assoc, galoisTwist_comp_snd, Category.assoc, hincl]

omit [IsGalois k K] in
/-- A Picard class of `X_K` pulled back from the stage `E` is fixed by every element of
`Gal(K/E)`: the stabiliser of the class contains that subgroup. -/
lemma fixingSubgroup_le_stabilizer_galoisPicardAction (X : Over (Spec (.of k)))
    (E : IntermediateField k K)
    (p : SchemeOver.baseChange k K X ⟶ pullback X.hom (spectrumMap k E))
    (hp₁ : p ≫ pullback.fst X.hom (spectrumMap k E) =
      pullback.fst X.hom (spectrumMap k K))
    (hp₂ : p ≫ pullback.snd X.hom (spectrumMap k E) =
      pullback.snd X.hom (spectrumMap k K) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E K)))
    (y : ofScheme (pullback X.hom (spectrumMap k E))) :
    letI := galoisPicardAction k K X
    E.fixingSubgroup ≤ MulAction.stabilizer (K ≃ₐ[k] K) (schemePullbackClass p y) := by
  let := galoisPicardAction k K X
  intro σ hσ
  change σ • schemePullbackClass p y = schemePullbackClass p y
  rw [galoisPicardAction_smul, schemePullbackClass_comp,
    galoisTwist_comp_eq_of_mem_fixingSubgroup X E σ hσ p hp₁ hp₂]

/-- **Every stabiliser of the Galois action on `Pic(X_K)` is open.** A class descends to a finite
subextension `E` by Tag 0B8W (2), and is then fixed by the open subgroup `Gal(K/E)`. -/
lemma isOpen_stabilizer_galoisPicardAction (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (x : ofScheme (SchemeOver.baseChange k K X)) :
    letI := galoisPicardAction k K X
    IsOpen (MulAction.stabilizer (K ≃ₐ[k] K) x : Set (K ≃ₐ[k] K)) := by
  let := galoisPicardAction k K X
  obtain ⟨E, hE, p, y, hp₁, hp₂, hpy⟩ :=
    exists_finiteSubextension_schemePullbackClass_eq X x
  have hle : E.fixingSubgroup ≤ MulAction.stabilizer (K ≃ₐ[k] K) x := by
    rw [← hpy]
    exact fixingSubgroup_le_stabilizer_galoisPicardAction X E p hp₁ hp₂ y
  exact Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen E)

/-- **The continuity clause of Stacks Tag 0CDT.** Let `k` be a field, let `X` be a quasi-compact,
quasi-separated scheme over `k`, and let `K/k` be a Galois extension. The action of `Gal(K/k)`
on `Pic(X_K)` by pullback along the twists `id_X × Spec(σ)` is continuous for the Krull topology
on the Galois group and the discrete topology on the Picard group: every class descends to a
finite subextension `E` (Tag 0B8W (2)), hence is fixed by the open subgroup `Gal(K/E)`. -/
@[stacks 0CDT "continuity of the action of `Gal(k'/k)` on `Pic(X_{k'})`, proved from Tag 0B8W \
(2) through `exists_finiteSubextension_schemePullbackClass_eq`"]
theorem continuousSMul_galoisPicardAction (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [TopologicalSpace (ofScheme (SchemeOver.baseChange k K X))]
    [DiscreteTopology (ofScheme (SchemeOver.baseChange k K X))] :
    letI := galoisPicardAction k K X
    ContinuousSMul (K ≃ₐ[k] K) (ofScheme (SchemeOver.baseChange k K X)) := by
  let := galoisPicardAction k K X
  exact continuousSMul_iff_stabilizer_isOpen.2 (isOpen_stabilizer_galoisPicardAction X)

end Continuity

end Stacks.Picard

end
