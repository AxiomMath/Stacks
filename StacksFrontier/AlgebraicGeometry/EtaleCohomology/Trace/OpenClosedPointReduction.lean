module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionFrobeniusTraceInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedFrobeniusTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LefschetzTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroStalkTrace

/-!
# Throwing out a finite set of closed points

Steps 1 to 3 of the proof of [Stacks, Tag 03UG]: let `Y` be a scheme over a finite field `k`,
`i : Z ⟶ Y` a closed immersion with `Z` finite étale over `k`, and `j : U ⟶ Y` the open
complement. For a bounded below complex `C` on `Y_étale`, the open and closed dévissage of
Step 1, the invariance of the canonical Frobenius trace under closed immersions, and the trace
formula in dimension zero of Step 2 give

`T''(Y, C) = T''(Y, j_! j^{-1} C) + ∑_{z ∈ Z(k)} Tr(π_z | (i^{-1} C)_z̄)`,

while the rational points of `Y` are those of `U` together with those of `Z`, so that

`T'(Y, C) = T'(U, j^{-1} C) + T'(Z, i^{-1} C)`.

## Main results

* `AlgebraicGeometry.exists_lift_of_isPreimmersion`: a point of a scheme over a field whose image
  lies in the image of a preimmersion lifts through it.
* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage`: the
  local trace of an inverse image.
* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_add_sum`.
* `Stacks.EtaleCohomology.sum_perfectDerivedTrace_rationalPointStalkFrobenius_eq_add`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_eq_sum_of_extensionByZero`: the trace formula for
  `C` follows from the one for `j_! j^{-1} C`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 1 to 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u r

namespace AlgebraicGeometry

/-- **Points over a field lift through a preimmersion.** For a preimmersion `i : Z ⟶ Y` and a
morphism `g : Spec K ⟶ Y` from the spectrum of a field whose point is the image of a point of
`Z`, `g` factors through `i`. -/
theorem exists_lift_of_isPreimmersion {K : Type u} [Field K] {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsPreimmersion i] (g : Spec (.of K) ⟶ Y) (z : Z) (hz : i z = g default) :
    ∃ g' : Spec (.of K) ⟶ Z, g' ≫ i = g := by
  have hsurj : Function.Surjective (i.residueFieldMap z) := by
    have hs : Function.Surjective (i.stalkMap z ≫ Z.residue z) :=
      (Z.residue_surjective z).comp (i.stalkMap_surjective z)
    rw [← Scheme.residue_residueFieldMap i z] at hs
    intro y
    obtain ⟨a, ha⟩ := hs y
    exact ⟨Y.residue (i z) a, ha⟩
  let e : Z.residueField z ≅ Y.residueField (i z) :=
    (RingEquiv.ofBijective (i.residueFieldMap z).hom
      ⟨(i.residueFieldMap z).hom.injective, hsurj⟩).toCommRingCatIso.symm
  have he : i.residueFieldMap z ≫ e.hom = 𝟙 _ := by
    ext x
    exact (RingEquiv.ofBijective (i.residueFieldMap z).hom
      ⟨(i.residueFieldMap z).hom.injective, hsurj⟩).symm_apply_apply x
  have hd := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g
  refine ⟨Spec.map (e.hom ≫
      (Y.residueFieldCongr (hz.trans (congrArg _ (Subsingleton.elim _ _)))).hom ≫
      Y.descResidueField (Scheme.stalkClosedPointTo g)) ≫ Z.fromSpecResidueField z, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, ← Spec.map_comp, reassoc_of% he, Spec.map_comp,
    Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField, hd]

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

section Stalk

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X X' : Scheme.{u}} (g : X' ⟶ X)
  (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (x' : Spec (.of k) ⟶ X')
  (x : Spec (.of k) ⟶ X) (hx : x' ≫ g = x)

include hx in
/-- The stalk of an inverse image at a rational point, degreewise on a bounded below complex:
`(g^{-1} M)_{x̄'} ≅ M_{x̄}` for `x' ≫ g = x`. -/
def inverseImageStalkComplexIso (M : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    rationalPointStalkComplex.{u, r} Λ K x'
        ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj M) ≅
      rationalPointStalkComplex.{u, r} Λ K x M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (rationalPointStalkPullbackIso Λ g K x' x hx).app (M.obj.X n))
    (fun a b _ => ((rationalPointStalkPullbackIso Λ g K x' x hx).hom.naturality (M.obj.d a b)).symm)

include hx in
/-- **The local trace of an inverse image**: `Tr(π_{x'} | (g^{-1} M)_{x̄'}) = Tr(π_x | M_x̄)` for
`x' ≫ g = x`. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage [Fintype k] (p q : ℕ)
    [Fact p.Prime] [CharP K p] (hcard : Fintype.card k = p ^ q)
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hX' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r}
      Λ K x' ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj M))))
    (hX : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ K x M))) :
    perfectDerivedTrace Λ ⟨_, hX'⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ K p q hcard x'
          ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj M))) =
      perfectDerivedTrace Λ ⟨_, hX⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ K p q hcard x M)) := by
  refine perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Q.mapIso (inverseImageStalkComplexIso Λ g K x' x hx M)) _ _ ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom Λ g K x' x hx
    p q hcard (M.obj.X n)

end Stalk

/-- **Stalks of an inverse image are perfect**: if every stalk of `C` is perfect, so is every
stalk of `g^{-1} C`. -/
theorem isPerfect_stalk_inverseImage (Λ : Type r) [Ring Λ] {X X' : Scheme.{u}} (g : X' ⟶ X)
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hC : ∀ s : GeometricPoint X, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          C.obj)))
    (s : GeometricPoint X') : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          ((etaleModuleInverseImage.{u, r} Λ g).mapCochainComplexPlus.obj C).obj)) := by
  refine StacksDraft.Perfect.isPerfect_of_iso ?_ (hC ⟨s.residueField, s.hom ≫ g⟩)
  exact DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
    (fun n => (etaleModuleStalkPullbackIso Λ g s.hom).app (C.obj.X n))
    (fun a b _ => ((etaleModuleStalkPullbackIso Λ g s.hom).hom.naturality (C.obj.d a b)).symm))

section RationalPoints

variable {k : Type u} [Field k] {Z U X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (i : Z ⟶ X)
  [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

/-- The rational points of `W` as rational points of `X`, along a morphism `g : W ⟶ X` over
`k`. -/
def rationalPointsMap {W : Scheme.{u}} (g : W ⟶ X) {fW : W ⟶ Spec (.of k)} (h : fW = g ≫ f)
    (x : rationalPoints fW) : rationalPoints f :=
  ⟨x.1 ≫ g, by rw [Category.assoc, ← h]; exact x.2⟩

omit [IsClosedImmersion i] [IsOpenImmersion j] in
include hij in
/-- A rational point of an open subscheme is not one of its closed complement. -/
lemma ne_of_rationalPoints (a : Spec (.of k) ⟶ U) (b : Spec (.of k) ⟶ Z) : a ≫ j ≠ b ≫ i := by
  intro h
  have h₁ : j (a default) ∈ Set.range j.base := ⟨_, rfl⟩
  rw [hij] at h₁
  apply h₁
  refine ⟨b default, ?_⟩
  have h₂ := congrArg (fun m : Spec (.of k) ⟶ X => m.base default) h
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h₂
  exact h₂.symm

include hij in
/-- **The rational points of `X` are those of an open subscheme and of its closed complement.** -/
def rationalPointsEquivSum {fU : U ⟶ Spec (.of k)} {fZ : Z ⟶ Spec (.of k)} (hU : fU = j ≫ f)
    (hZ : fZ = i ≫ f) : rationalPoints fU ⊕ rationalPoints fZ ≃ rationalPoints f :=
  Equiv.ofBijective (Sum.elim (rationalPointsMap f j hU) (rationalPointsMap f i hZ)) (by
    refine ⟨?_, fun x => ?_⟩
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr, rationalPointsMap] at h
      · exact congrArg Sum.inl (Subtype.ext ((cancel_mono j).1 (congrArg Subtype.val h)))
      · exact (ne_of_rationalPoints i j hij a.1 b.1 (congrArg Subtype.val h)).elim
      · exact (ne_of_rationalPoints i j hij b.1 a.1 (congrArg Subtype.val h).symm).elim
      · exact congrArg Sum.inr (Subtype.ext ((cancel_mono i).1 (congrArg Subtype.val h)))
    · by_cases hx : x.1 default ∈ Set.range j.base
      · obtain ⟨t, ht⟩ := hx
        obtain ⟨g, hg⟩ := exists_lift_of_isPreimmersion j x.1 t ht
        exact ⟨Sum.inl ⟨g, by rw [hU, ← Category.assoc, hg]; exact x.2⟩, Subtype.ext hg⟩
      · rw [hij, Set.notMem_compl_iff] at hx
        obtain ⟨t, ht⟩ := hx
        obtain ⟨g, hg⟩ := exists_lift_of_isPreimmersion i x.1 t ht
        exact ⟨Sum.inr ⟨g, by rw [hZ, ← Category.assoc, hg]; exact x.2⟩, Subtype.ext hg⟩)

include hij in
/-- **A sum over the rational points of `X` splits** into the sums over the rational points of an
open subscheme and of its closed complement. -/
theorem sum_rationalPoints_eq_add {M : Type*} [AddCommMonoid M] {fU : U ⟶ Spec (.of k)}
    {fZ : Z ⟶ Spec (.of k)} (hU : fU = j ≫ f) (hZ : fZ = i ≫ f) [Fintype (rationalPoints f)]
    [Fintype (rationalPoints fU)] [Fintype (rationalPoints fZ)]
    (F : (Spec (.of k) ⟶ X) → M) :
    ∑ x : rationalPoints f, F x.1 =
      ∑ x : rationalPoints fU, F (x.1 ≫ j) + ∑ x : rationalPoints fZ, F (x.1 ≫ i) := by
  rw [← Equiv.sum_comp (rationalPointsEquivSum f i j hij hU hZ), Fintype.sum_sum_type]
  rfl

end RationalPoints

/-- The local trace of an extension by zero vanishes at a rational point not lifting to the
open. -/
private theorem perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero_eq_zero_of_forall_ne
    (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
    (y : Spec (.of k) ⟶ Y) (hy : ∀ g : Spec (.of k) ⟶ U, g ≫ j ≠ y)
    (F : CochainComplex.Plus (EtaleModules.{u, r} Λ U))
    (hF : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r}
      Λ kbar y ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj F)))) :
    perfectDerivedTrace Λ ⟨_, hF⟩ (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar
      p q hcard y ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj F))) = 0 := by
  refine perfectDerivedTrace_eq_zero_of_isZero Λ _ ?_ _
  refine Functor.map_isZero DerivedCategory.Q
    (isZero_rationalPointStalkComplex_extensionByZero Λ j kbar y ?_ F)
  rintro ⟨t, ht⟩
  obtain ⟨g, hg⟩ := exists_lift_of_isPreimmersion j y t ht
  exact hy g hg

section Reduction

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) [IsClosedImmersion i.left] {U : Scheme.{u}} (j : U ⟶ Y.left) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.left.base)ᶜ) (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

include hij in
open scoped Classical in
/-- **Throwing out the closed points of a finite étale closed subscheme**, Steps 1 and 2 of
[Stacks, Tag 03UG]: for a closed immersion `i : Z ⟶ Y` with `Z` finite étale over `k`, its open
complement `j : U ⟶ Y`, and a bounded below complex `C` on `Y_étale`,
`T''(Y, C) = T''(Y, j_! j^{-1} C) + ∑_{z ∈ Z(k)} Tr(π_z | (i^{-1} C)_z̄)`. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_add_sum [Etale Z.hom]
    [IsFinite Z.hom] [Fintype (rationalPoints Z.hom)]
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))))
    (hstalk : ∀ s : GeometricPoint Z.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          ((etaleModuleInverseImage.{u, r} Λ i.left).mapCochainComplexPlus.obj C).obj))) :
    perfectDerivedTrace Λ ⟨_, hp₂⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) =
      perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))) +
        ∑ z : rationalPoints Z.hom, perfectDerivedTrace Λ
          ⟨_, hstalk (rationalGeometricPoint kbar z.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard z.1
            ((etaleModuleInverseImage.{u, r} Λ i.left).mapCochainComplexPlus.obj C))) := by
  have hZ := isPerfect_frobeniusRestriction_of_etale Λ Z kbar _ hstalk
  have hp₃ := (isPerfect_frobeniusRestriction_directImage_iff Λ i kbar _).2 hZ
  rw [perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_add_openClosed Λ Y i.left j hij
    kbar p q hcard C hp₁ hp₂ hp₃]
  congr 1
  exact (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage Λ i p q hcard kbar _
    hp₃ hZ).trans (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale' Λ Z kbar
      p q hcard _ hZ hstalk)

/-- A degreewise isomorphism of complexes induces an isomorphism of stalk complexes at a rational
point. -/
def rationalPointStalkComplexMapIso {X : Scheme.{u}} (x : Spec (.of k) ⟶ X)
    {M M' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (e : ∀ n, M.obj.X n ≅ M'.obj.X n)
    (he : ∀ a b, M.obj.d a b ≫ (e b).hom = (e a).hom ≫ M'.obj.d a b) :
    rationalPointStalkComplex.{u, r} Λ kbar x M ≅ rationalPointStalkComplex.{u, r} Λ kbar x M' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (rationalPointStalkFunctor.{u, r} Λ kbar x).mapIso (e n))
    (fun a b _ => by
      have h := congrArg (rationalPointStalkFunctor.{u, r} Λ kbar x).map (he a b)
      rw [Functor.map_comp, Functor.map_comp] at h
      exact h.symm)

omit [CharP k p] in
/-- **The local trace is invariant under isomorphism of complexes.** -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_congr {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X) {M M' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    (e : ∀ n, M.obj.X n ≅ M'.obj.X n)
    (he : ∀ a b, M.obj.d a b ≫ (e b).hom = (e a).hom ≫ M'.obj.d a b)
    (hM : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x M)))
    (hM' : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x M'))) :
    perfectDerivedTrace Λ ⟨_, hM⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x M)) =
      perfectDerivedTrace Λ ⟨_, hM'⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x M')) := by
  refine perfectDerivedTrace_congr Λ _ _ (DerivedCategory.Q.mapIso
    (rationalPointStalkComplexMapIso Λ kbar x e he)) _ _ ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact ((geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) kbar p q hcard x).naturality
    (e n).hom).symm

omit [Fintype k] in
/-- The degreewise identification `j^{-1} ≅ j|` of inverse image and restriction along an open
immersion commutes with the differentials of a bounded below complex. -/
lemma inverseImageRestrictionIso_comm (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (a b : ℤ) :
    ((etaleModuleInverseImage.{u, r} Λ j).mapCochainComplexPlus.obj C).obj.d a b ≫
        ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j).app (C.obj.X b)).hom =
      ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j).app (C.obj.X a)).hom ≫
        ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C).obj.d a b :=
  (etaleModuleInverseImageRestrictionIso.{u, r} Λ j).hom.naturality (C.obj.d a b)

omit [CharP k p] in
include hij in
open scoped Classical in
/-- **The local side of the reduction**:
`T'(Y, C) = T'(Y, j_! j^{-1} C) + ∑_{z ∈ Z(k)} Tr(π_z | (i^{-1} C)_z̄)`. -/
theorem sum_perfectDerivedTrace_rationalPointStalkFrobenius_eq_add
    [Fintype (rationalPoints Y.hom)] [Finite (rationalPoints (j ≫ Y.hom))]
    [Fintype (rationalPoints Z.hom)] (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hC : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          C.obj)))
    (hC' : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)).obj))) :
    ∑ y : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hC (rationalGeometricPoint kbar y.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y.1 C)) =
      ∑ y : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hC' (rationalGeometricPoint kbar y.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y.1
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))) +
      ∑ z : rationalPoints Z.hom, perfectDerivedTrace Λ
        ⟨_, isPerfect_stalk_inverseImage Λ i.left C hC (rationalGeometricPoint kbar z.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard z.1
          ((etaleModuleInverseImage.{u, r} Λ i.left).mapCochainComplexPlus.obj C))) := by
  have := Fintype.ofFinite (rationalPoints (j ≫ Y.hom))
  have hZ : Z.hom = i.left ≫ Y.hom := (Over.w i).symm
  have e₁ := sum_rationalPoints_eq_add Y.hom i.left j hij rfl hZ (fun y =>
    perfectDerivedTrace Λ ⟨_, hC (rationalGeometricPoint kbar y)⟩
      (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y C)))
  have e₂ := sum_rationalPoints_eq_add Y.hom i.left j hij rfl hZ (fun y =>
    perfectDerivedTrace Λ ⟨_, hC' (rationalGeometricPoint kbar y)⟩
      (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y
        ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
          ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))))
  refine e₁.trans (Eq.trans ?_ (congrArg (· + _) e₂.symm))
  rw [Fintype.sum_eq_zero (fun z : rationalPoints Z.hom => perfectDerivedTrace Λ
      ⟨_, hC' (rationalGeometricPoint kbar (z.1 ≫ i.left))⟩
      (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard (z.1 ≫ i.left)
        ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
          ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C))))) (fun z => ?_),
    add_zero]
  · congr 1
    · refine Fintype.sum_congr _ _ fun v => ?_
      have hv := isPerfect_stalk_inverseImage Λ j C hC (rationalGeometricPoint kbar v.1)
      have hv' := StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso
        (rationalPointStalkComplexMapIso Λ kbar v.1
          (M := (etaleModuleInverseImage.{u, r} Λ j).mapCochainComplexPlus.obj C)
          (M' := (etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C) _
          (inverseImageRestrictionIso_comm Λ j C))).symm hv
      exact ((perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage Λ j kbar v.1 _ rfl
        p q hcard C hv _).symm.trans (perfectDerivedTrace_rationalPointStalkFrobenius_congr Λ kbar
          p q hcard v.1 (M := (etaleModuleInverseImage.{u, r} Λ j).mapCochainComplexPlus.obj C)
          (M' := (etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C) _
          (inverseImageRestrictionIso_comm Λ j C) hv hv')).trans
        (perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero Λ j kbar v.1 _ rfl
          p q hcard _ _ hv').symm
    · refine Fintype.sum_congr _ _ fun z => ?_
      exact (perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage Λ i.left kbar z.1 _ rfl
        p q hcard C _ _).symm
  · exact perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero_eq_zero_of_forall_ne Λ j
      kbar p q hcard _ (fun g hg => ne_of_rationalPoints i.left j hij g z.1 hg) _ _

include hij in
open scoped Classical in
/-- **Step 3 of [Stacks, Tag 03UG]: one may throw out a finite étale closed subscheme.** If the
trace formula `T'' = T'` holds on `Y` for `j_! j^{-1} C`, it holds for `C`. -/
theorem perfectDerivedTrace_eq_sum_of_extensionByZero [Etale Z.hom] [IsFinite Z.hom]
    [Fintype (rationalPoints Y.hom)] [Finite (rationalPoints (j ≫ Y.hom))]
    [Finite (rationalPoints Z.hom)] (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))))
    (hC : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          C.obj)))
    (hC' : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)).obj)))
    (h : perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard
            ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C)))) =
      ∑ y : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hC' (rationalGeometricPoint kbar y.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y.1
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj C))))) :
    perfectDerivedTrace Λ ⟨_, hp₂⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) =
      ∑ y : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hC (rationalGeometricPoint kbar y.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y.1 C)) := by
  have := Fintype.ofFinite (rationalPoints Z.hom)
  rw [perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_add_sum Λ i j hij kbar p q hcard C
    hp₁ hp₂ (isPerfect_stalk_inverseImage Λ i.left C hC),
    sum_perfectDerivedTrace_rationalPointStalkFrobenius_eq_add Λ i j hij kbar p q hcard C hC hC', h]

omit [CharP k p] in
open scoped Classical in
/-- **The local side vanishes off the rational points of the open**: if `U` has no rational point,
`T'(Y, j_! F) = 0`. -/
theorem sum_perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero_eq_zero
    [IsEmpty (rationalPoints (j ≫ Y.hom))] [Fintype (rationalPoints Y.hom)]
    (F : CochainComplex.Plus (EtaleModules.{u, r} Λ U))
    (hF : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj F).obj))) :
    ∑ y : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hF (rationalGeometricPoint kbar y.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y.1
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj F))) = 0 := by
  refine Fintype.sum_eq_zero _ fun y =>
    perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero_eq_zero_of_forall_ne Λ j kbar
      p q hcard y.1 (fun g hg => IsEmpty.false (α := rationalPoints (j ≫ Y.hom))
        ⟨g, by rw [← Category.assoc, hg]; exact y.2⟩) F _

end Reduction

section Compactification

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {Y : Over (Spec (.of k))} (j : X ⟶ Y.left) [IsOpenImmersion j]
  (hj : j ≫ Y.hom = f) (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

include hj in
open scoped Classical in
/-- **The local side of an extension by zero**: `T'(Y, j_! K) = T'(X, K)` for an open immersion
`j : X ⟶ Y` over `k`. -/
theorem sum_perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero
    [Fintype (rationalPoints Y.hom)] [Fintype (rationalPoints f)]
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hK : ∀ s : GeometricPoint X, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          K.obj)))
    (hK' : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj K).obj))) :
    ∑ y : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hK' (rationalGeometricPoint kbar y.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard y.1
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj K))) =
      ∑ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hK (rationalGeometricPoint kbar x.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x.1 K)) := by
  refine (Fintype.sum_of_injective (rationalPointsMap Y.hom j hj.symm)
    (fun a b h => Subtype.ext ((cancel_mono j).1 (congrArg Subtype.val h))) _ _ ?_ ?_).symm
  · intro y hy
    exact perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero_eq_zero_of_forall_ne Λ j
      kbar p q hcard y.1 (fun g hg => hy ⟨⟨g, by rw [← hj, ← Category.assoc, hg]; exact y.2⟩,
        Subtype.ext hg⟩) K _
  · intro x
    exact (perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero Λ j kbar x.1 _ rfl
      p q hcard K _ _).symm

end Compactification

end Stacks.EtaleCohomology

end
