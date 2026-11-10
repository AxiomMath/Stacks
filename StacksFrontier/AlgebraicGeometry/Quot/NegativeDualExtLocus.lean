module

public import StacksFrontier.AlgebraicGeometry.Quot.FieldTestSchemeOpenDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDualVanishing
public import StacksFrontier.Homology.Perfect.FibreBettiFieldBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback

/-!
# The open locus where a pseudo-coherent complex has no positive fibre cohomology

Let `Y` be an algebraic space over a scheme `S` and `L` a pseudo-coherent object of `D(𝒪_Y)`, on
the small étale site.  This file proves that there is an open subspace `W ⊆ Y` characterized by:
a point `y : Spec(k) ⟶ Y` with values in a field lies in `|W|` if and only if
`Ext^i(L_y, 𝒪_y) = Hom(Ly^*L, 𝒪[i]) = 0` for all `i < 0`, that is (over a field) if and only if
the derived fibre `L ⊗^L κ(y)` has no cohomology in positive degrees.

This is the step of the proof of Stacks 0DLC, part (1), which the source attributes to
Stacks 0BDI: "the set `W` of `y ∈ Y` where `H^i(L ⊗^L κ(y)) = 0` for `i > 0` defines an open
of `Y`", read on the small étale site of an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.HasNoNegativeDualExt`: `Ext^i(Lq^*L, 𝒪_Z) = 0` for every `i < 0`,
  for a morphism `q : Z ⟶ Y` of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.exists_openSubspace_hasNoNegativeDualExt_iff`: **Stacks 0BDI on the
  small étale site**, in the form the proof of Stacks 0DLC uses it.
* `AlgebraicGeometry.Space.hasNoNegativeDualExt_chartPoint_iff`: on an affine étale chart
  `Spec(A) ⟶ Y` on which `L` is modelled by a bounded above complex `P` of finite free
  `A`-modules, the condition at a point `Spec(k) ⟶ Spec(A)` is the vanishing of the derived
  fibre Betti numbers `dim_{κ(p)} H^j(P ⊗^L κ(p))`, `j > 0`, at its image `p`.
* `AlgebraicGeometry.Space.hasNoNegativeDualExt_iff_of_hom`: the condition does not change under
  a field extension over `Y`.

## The argument

On an affine étale chart, `L` is `ε^*(P~)` with `P` bounded above and finite free
(`AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso`), and the
derived pullback of `L` to a point `Spec(k) ⟶ Spec(A)` is the chart model of `P ⊗_A k`
(`AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_chartModel_iso`).  If
`H^j(P ⊗_A k) = 0` for `j > 0`, the pullback has no cohomology in positive degrees and its
negative extensions into the structure sheaf vanish; otherwise, with `n > 0` the top degree of
the cohomology, `k[-n]` is a retract of a finite free model of `P ⊗_A k` vanishing above `n`,
which makes `𝒪[-n]` a retract of the pullback and gives a nonzero map into `𝒪[-n]` (as in
`AlgebraicGeometry.Space.isLE_zero_of_chartModel_of_forall_field`).  The dimension of
`H^j(P ⊗_A k)` is the derived fibre Betti number of `P` at the image prime
(`StacksDraft.Perfect.fibreBetti_eq_finrank_homology_extendScalars`), so the condition depends
only on that prime, and the locus on the chart is open by Stacks 0BDI, part (2), in its affine
form (`StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent`): only the
finitely many degrees `0 < j ≤ b` with `P` vanishing above `b` matter.  Independence of the
field extension is the same computation on the chart `Spec(k) ⟶ Spec(k)` of the field point
itself, whose spectrum has one prime.  The locus then descends from the charts to `Y` by
`AlgebraicGeometry.Space.exists_openSubspace_forall_isFieldObject_iff`.

## Implementation notes

The chart model, the derived pullback of algebraic spaces and `ε^*` are built at the standard
model of the derived categories involved, so the section working with them pins that model at
priority `10000`, as `StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreDualVanishing.lean` does
and for the same reason: at the default priority the global model of `SheafOfModules` wins and
the statements of the chart model no longer elaborate.  The definition and the main statement
do not depend on the pin.  Nothing is registered.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The condition -/

section Condition

/-- **`Ext^i(Lq^*L, 𝒪_Z) = 0` for every `i < 0`**, for an object `L` of `D(𝒪_Y)` and a morphism
`q : Z ⟶ Y` of algebraic spaces.  At a point `q : Spec(k) ⟶ Y` with values in a field this is the
vanishing of the positive cohomology of the derived fibre `L ⊗^L k`. -/
def HasNoNegativeDualExt {Z Y : AlgebraicSpaces B S hS} (L : derivedModules B S hS Y)
    (q : Z ⟶ Y) : Prop :=
  ∀ i : ℤ, i < 0 →
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull q).obj L ⟶
      (structureObject B S hS Z)⟦i⟧)

/-- The condition along a composite `f ≫ g` is the condition for the pullback along `g` along
`f` (Stacks 0D6D). -/
theorem hasNoNegativeDualExt_comp_iff {Z Y' Y : AlgebraicSpaces B S hS}
    (L : derivedModules B S hS Y) (f : Z ⟶ Y') (g : Y' ⟶ Y) :
    HasNoNegativeDualExt L (f ≫ g) ↔
      HasNoNegativeDualExt (((smallEtaleDerivedPullbackData B S hS).pull g).obj L) f :=
  forall₂_congr fun i _ => subsingleton_hom_shift_congr
    (((smallEtaleDerivedPullbackData B S hS).compIso f g).app L) (Iso.refl _) i

/-- Along an isomorphism `φ : Z ≅ Z'`, the derived pullback is an equivalence commuting with the
shift and preserving the structure sheaf, so the condition for `M` at the identity is the
condition for `M` along `φ`. -/
theorem hasNoNegativeDualExt_iso_iff {Z Z' : AlgebraicSpaces B S hS} (φ : Z ≅ Z')
    (M : derivedModules B S hS Z') :
    (∀ i : ℤ, i < 0 → Subsingleton (M ⟶ (structureObject B S hS Z')⟦i⟧)) ↔
      HasNoNegativeDualExt M φ.hom := by
  let P := smallEtaleDerivedPullbackData B S hS
  let F := (P.pullEquivalence φ).functor
  have : F.CommShift ℤ := smallEtaleDerivedPullbackData_pull_commShift φ.hom
  have hF : F.FullyFaithful := (P.pullEquivalence φ).fullyFaithfulFunctor
  refine forall₂_congr fun i _ => ?_
  let e : (M ⟶ (structureObject B S hS Z')⟦i⟧) ≃
      (F.obj M ⟶ (F.obj (structureObject B S hS Z'))⟦i⟧) :=
    hF.homEquiv.trans ((Iso.refl _).homCongr ((F.commShiftIso i).app _))
  exact e.subsingleton_congr.trans (subsingleton_hom_shift_congr (Iso.refl _)
    (smallEtaleDerivedPullStructureIso B S hS φ.hom) i)

/-- **The condition is invariant under isomorphisms of the source.**  For `φ : Z ≅ Z'` and
`q = φ ≫ p`, the condition along `p` is the condition along `q`. -/
theorem hasNoNegativeDualExt_iff_of_iso {Z Z' Y : AlgebraicSpaces B S hS}
    (L : derivedModules B S hS Y) (φ : Z ≅ Z') {p : Z' ⟶ Y} {q : Z ⟶ Y}
    (hq : φ.hom ≫ p = q) : HasNoNegativeDualExt L p ↔ HasNoNegativeDualExt L q := by
  rw [← hq, hasNoNegativeDualExt_comp_iff]
  exact hasNoNegativeDualExt_iso_iff φ _

end Condition

/-! ### Spectra of fields among the objects of the site -/

section FieldObjects

/-- **An object of the site whose scheme is the spectrum of a field is isomorphic to a field
spectrum over `S`.** -/
theorem exists_specFppfOver_iso_of_isFieldObject {U : BigFppfOver B S hS}
    (hU : Stack.IsFieldObject B S hS U) :
    ∃ (k : Type u) (_ : Field k) (hk : B.Contains (Spec (CommRingCat.of k)))
      (gk : B.obj hk ⟶ B.obj hS), Nonempty (specFppfOver B S hS hk gk ≅ U) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hU
  let := hk
  have hk' : B.Contains (Spec (CommRingCat.of k)) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.inv) U.left.2
  exact ⟨k, hk, hk', ObjectProperty.homMk e.inv ≫ U.hom,
    ⟨Over.isoMk (B.inclusion.preimageIso e.symm) (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      rfl))⟩⟩

/-- A morphism of the site between two spectra over `S` is the spectrum of a ring map: with the
algebra structure of that ring map, it is `AlgebraicGeometry.Space.specFppfOverMap`. -/
theorem exists_eq_specFppfOverMap {A k : Type u} [CommRing A] [CommRing k]
    {hA : B.Contains (Spec (CommRingCat.of A))} {gA : B.obj hA ⟶ B.obj hS}
    {hk : B.Contains (Spec (CommRingCat.of k))} {gk : B.obj hk ⟶ B.obj hS}
    (h : specFppfOver B S hS hk gk ⟶ specFppfOver B S hS hA gA) :
    ∃ (φ : A →+* k), letI := φ.toAlgebra; ∃ w, specFppfOverMap B S hS hA gA hk gk w = h := by
  let φ : A →+* k := (Spec.preimage h.left.hom).hom
  let := φ.toAlgebra
  have hleft : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A k))) :
      B.obj hk ⟶ B.obj hA) = h.left := by
    refine ObjectProperty.hom_ext _ ?_
    change Spec.map (CommRingCat.ofHom φ) = h.left.hom
    rw [show CommRingCat.ofHom φ = Spec.preimage h.left.hom from rfl, Spec.map_preimage]
  exact ⟨φ, hleft ▸ Over.w h, Over.OverMorphism.ext hleft⟩

end FieldObjects

/-! ### Linear algebra over the field of a point -/

section Algebra

/-- A module of finite type stays of finite type under extension of scalars to a field. -/
theorem module_finite_extendScalars {A k : Type u} [CommRing A] [Field k] (g : A →+* k)
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite k ((ModuleCat.extendScalars g).obj M) := by
  let := g.toAlgebra
  exact inferInstanceAs (Module.Finite k (TensorProduct A k M))

/-- The cohomology of a complex of vector spaces is finite dimensional in a degree where the
term is. -/
theorem module_finite_homology_of_field {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) [Module.Finite k (C.X i)] :
    Module.Finite k (C.homology i) := by
  have hmono : Function.Injective (ModuleCat.Hom.hom (C.iCycles i)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hfin : Module.Finite k (C.cycles i) :=
    Module.Finite.of_injective (ModuleCat.Hom.hom (C.iCycles i)) hmono
  have hepi : Function.Surjective (ModuleCat.Hom.hom (C.homologyπ i)) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  exact Module.Finite.of_surjective _ hepi

/-- Extension of scalars to a field of a bounded above complex of finite free modules is a
bounded above complex of finite free vector spaces. -/
theorem isBoundedAboveFiniteFree_extendScalars {A k : Type u} [CommRing A] [Field k]
    (g : A →+* k) {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P) :
    StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree
      ((CochainComplex.extendScalars g).obj P) := by
  obtain ⟨b, hb⟩ := hP.upperBound
  refine ⟨⟨b, (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
    (ModuleCat.extendScalars g).map_isZero (P.isZero_of_isStrictlyLE b i hi)⟩, fun i => ?_⟩
  have := (hP.finiteFree i).1
  exact ⟨module_finite_extendScalars g (P.X i), inferInstance⟩

/-- A point of the spectrum of a field `k`, mapped to `Spec(A)` along `A →+* k`, is the kernel. -/
theorem ker_eq_comap_asIdeal {A k : Type u} [CommRing A] [Field k] (g : A →+* k)
    (x : PrimeSpectrum k) : RingHom.ker g = (PrimeSpectrum.comap g x).asIdeal := by
  rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime x.asIdeal, RingHom.ker_eq_comap_bot]

end Algebra

/-! ### The computation on an affine étale chart -/

section Chart

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived fibre Betti number at the prime of a field point.**  For a bounded above
complex `P` of finite free `A`-modules and `g : A →+* k` to a field with kernel the prime `p`,
the `j`-th derived fibre Betti number of `P` at `p` vanishes exactly when `H^j(P ⊗_A k) = 0`. -/
theorem fibreBetti_eq_zero_iff_isZero_homology {A k : Type u} [CommRing A] [Field k]
    (g : A →+* k) {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P) (p : PrimeSpectrum A)
    (hp : RingHom.ker g = p.asIdeal) (j : ℤ) :
    StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0 ↔
      IsZero (((CochainComplex.extendScalars g).obj P).homology j) := by
  obtain ⟨b, hb⟩ := hP.upperBound
  have : ∀ j, Projective (P.X j) := fun j => by
    have := (hP.finiteFree j).2
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis A (P.X j))
  rw [StacksDraft.Perfect.fibreBetti_eq_finrank_homology_extendScalars P b g p hp j]
  let K := (CochainComplex.extendScalars g).obj P
  have : Module.Finite k (K.X j) := by
    have := (hP.finiteFree j).1
    exact module_finite_extendScalars g (P.X j)
  have := module_finite_homology_of_field K j
  change Module.finrank k (K.homology j) = 0 ↔ _
  rw [Module.finrank_zero_iff]
  exact ⟨fun _ => ModuleCat.isZero_of_subsingleton _, ModuleCat.subsingleton_of_isZero⟩

variable {Y : AlgebraicSpaces B S hS}

/-- **The condition at a point of an affine étale chart.**  Let `φ : Spec(A) ⟶ Y` be a morphism
on which `L ∈ D(𝒪_Y)` is modelled by a bounded above complex `P` of finite free `A`-modules,
`Lφ^*L ≅ ε^*(P~)`, and let `Spec(k) ⟶ Spec(A)` be a point with values in a field.  Then
`Ext^i(L_y, 𝒪_y) = 0` for all `i < 0` at the composite `y : Spec(k) ⟶ Y` exactly when
`H^j(P ⊗_A k) = 0` for all `j > 0`. -/
theorem hasNoNegativeDualExt_chartPoint_iff_isZero (L : derivedModules B S hS Y)
    {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (gA : B.obj hA ⟶ B.obj hS)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ Y)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : ((smallEtaleDerivedPullbackData B S hS).pull φ).obj L ≅
      (chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P))
    {k : Type u} [Field k] [Algebra A k] (hk : B.Contains (Spec (CommRingCat.of k)))
    (gk : B.obj hk ⟶ B.obj hS)
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A k))) :
      B.obj hk ⟶ B.obj hA) ≫ gA = gk) :
    HasNoNegativeDualExt L
        (representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hk gk w) ≫ φ) ↔
      ∀ j : ℤ, 0 < j →
        IsZero (((CochainComplex.extendScalars (algebraMap A k)).obj P).homology j) := by
  classical
  let rg := representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hk gk w)
  let K := (CochainComplex.extendScalars (algebraMap A k)).obj P
  have hK : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree K :=
    isBoundedAboveFiniteFree_extendScalars _ hP
  obtain ⟨e₆⟩ := nonempty_smallEtaleDerivedModulePullback_chartModel_iso B S hS hA gA hk gk w
    P hP
  let E : ((smallEtaleDerivedPullbackData B S hS).pull (rg ≫ φ)).obj L ≅
      (chartModelFunctor B S hS hk gk).obj (DerivedCategory.Q.obj K) :=
    ((smallEtaleDerivedPullbackData B S hS).compIso rg φ).app L ≪≫
      ((smallEtaleDerivedPullbackData B S hS).pull rg).mapIso eP ≪≫ e₆
  constructor
  · intro hsub
    by_contra hne
    push Not at hne
    obtain ⟨b, hb⟩ := hK.upperBound
    have hne' : ∃ n : ℤ, 0 < n ∧
        ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj
          (DerivedCategory.Q.obj K)) := by
      obtain ⟨j, hj, hjK⟩ := hne
      exact ⟨j, hj, fun h => hjK
        (h.of_iso (StacksDraft.PseudoCoherence.homologyQObjIso K j).symm)⟩
    obtain ⟨n, ⟨hn0, hn⟩, htop⟩ := Int.exists_greatest_of_bdd (P := fun n => 0 < n ∧
        ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj
          (DerivedCategory.Q.obj K)))
      ⟨b, fun n hn => by
        by_contra hlt
        exact hn.2 (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj K) b n (by omega))⟩
      hne'
    have hvan : ∀ i, n < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        (DerivedCategory.Q.obj K)) := fun i hi => by
      by_contra h
      have := htop i ⟨by omega, h⟩
      omega
    obtain ⟨K', α, -, hK'le, hα⟩ :=
      StacksDraft.PseudoCoherence.IsPseudoCoherentIn.exists_finiteFree_representative_le
        ⟨K, hK, ⟨Iso.refl _⟩⟩ n hvan
    have hH' : ¬ IsZero (K'.homology n) := fun h => hn
      ((h.of_iso (StacksDraft.PseudoCoherence.homologyQObjIso K' n)).of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso (asIso α)).symm)
    have hK'1 : IsZero (K'.X (n + 1)) := K'.isZero_of_isStrictlyLE n (n + 1) (by omega)
    obtain ⟨s, r, hsr⟩ := exists_single_retract_of_not_isZero_homology K' n hK'1 hH'
    let ι := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} k) n).app
      (ModuleCat.of k k)
    let s' := ι.hom ≫ DerivedCategory.Q.map s ≫ α
    let r' := inv α ≫ DerivedCategory.Q.map r ≫ ι.inv
    have hQsr : DerivedCategory.Q.map s ≫ DerivedCategory.Q.map r = 𝟙 _ :=
      (DerivedCategory.Q.map_comp s r).symm.trans
        ((congrArg DerivedCategory.Q.map hsr).trans (DerivedCategory.Q.map_id _))
    have hsr' : s' ≫ r' = 𝟙 _ := by
      simp only [s', r', Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% hQsr, ι.hom_inv_id]
    let Fk := chartModelFunctor B S hS hk gk
    let U := chartModelFunctorSingleIso B S hS hk gk n
    have hFsr : Fk.map s' ≫ Fk.map r' = 𝟙 _ :=
      (Fk.map_comp s' r').symm.trans ((congrArg Fk.map hsr').trans (Fk.map_id _))
    have hip := comp_retract_eq_id U.symm E (Fk.map s') (Fk.map r') hFsr
    have hEnd := subsingleton_hom_of_retract _ _ hip (hsub (-n) (by omega))
    have hEnd' : Subsingleton (structureObject B S hS (schemeSpace (specFppfOver B S hS hk gk)) ⟶
        structureObject B S hS (schemeSpace (specFppfOver B S hS hk gk))) :=
      ⟨fun f g => (shiftFunctor (derivedModules B S hS
        (schemeSpace (specFppfOver B S hS hk gk))) (-n)).map_injective (hEnd.elim _ _)⟩
    exact not_isZero_structureObject_specFppfOver B S hS hk gk
      ((IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _))
  · intro hzero i hi
    have hKLE : (DerivedCategory.Q.obj K).IsLE 0 :=
      (DerivedCategory.isLE_iff _ 0).2 fun j hj =>
        (hzero j hj).of_iso (StacksDraft.PseudoCoherence.homologyQObjIso K j)
    have hM : ((chartModelFunctor B S hS hk gk).obj (DerivedCategory.Q.obj K)).IsLE 0 := by
      have := hKLE
      have := Stacks.Homology.isLE_mapDerivedCategory_obj
        (tilde.functor (CommRingCat.of k) ⋙
          Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hk gk))).hom)
        (DerivedCategory.Q.obj K) 0
      exact Stacks.Homology.isLE_mapDerivedCategory_obj (representedAssociatedModule B S hS
        (specFppfOver B S hS hk gk) (isAlgebraicSpace_yoneda B S hS _)) _ 0
    have hLE : (((smallEtaleDerivedPullbackData B S hS).pull (rg ≫ φ)).obj L).IsLE 0 := by
      have : ((representedDerivedAssociatedModule B S hS (specFppfOver B S hS hk gk)).obj
          ((tilde.functor (CommRingCat.of k) ⋙
            Scheme.Modules.restrictFunctor
              (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hk gk))).hom
              ).mapDerivedCategory.obj (DerivedCategory.Q.obj K))).IsLE 0 := hM
      exact DerivedCategory.TStructure.t.isLE_of_iso E.symm 0
    have : ((structureObject B S hS (⟨yoneda.obj (specFppfOver B S hS hk gk),
        isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS))⟦i⟧).IsGE 1 := by
      have : ((structureObject B S hS (⟨yoneda.obj (specFppfOver B S hS hk gk),
          isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS))⟦i⟧).IsGE
          (-i) := DerivedCategory.TStructure.t.isGE_shift _ 0 i (-i)
      exact DerivedCategory.TStructure.t.isGE_of_ge _ 1 (-i) (by omega)
    exact ⟨fun a b => (DerivedCategory.TStructure.t.zero a 0 1).trans
      (DerivedCategory.TStructure.t.zero b 0 1).symm⟩

/-- **The condition at a point of an affine étale chart, through the derived fibre Betti
numbers.**  In the situation of
`AlgebraicGeometry.Space.hasNoNegativeDualExt_chartPoint_iff_isZero`, the condition at
`Spec(k) ⟶ Spec(A) ⟶ Y` holds exactly when the derived fibre Betti numbers
`dim_{κ(p)} H^j(P ⊗^L κ(p))`, `j > 0`, of `P` vanish at the image `p` of the point. -/
theorem hasNoNegativeDualExt_chartPoint_iff (L : derivedModules B S hS Y)
    {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (gA : B.obj hA ⟶ B.obj hS)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ Y)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : ((smallEtaleDerivedPullbackData B S hS).pull φ).obj L ≅
      (chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P))
    {k : Type u} [Field k] [Algebra A k] (hk : B.Contains (Spec (CommRingCat.of k)))
    (gk : B.obj hk ⟶ B.obj hS)
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A k))) :
      B.obj hk ⟶ B.obj hA) ≫ gA = gk) (x : PrimeSpectrum k) :
    HasNoNegativeDualExt L
        (representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hk gk w) ≫ φ) ↔
      ∀ j : ℤ, 0 < j → StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j
        (PrimeSpectrum.comap (algebraMap A k) x) = 0 := by
  rw [hasNoNegativeDualExt_chartPoint_iff_isZero L hA gA φ P hP eP hk gk w]
  exact forall₂_congr fun j _ => (fibreBetti_eq_zero_iff_isZero_homology (algebraMap A k) hP
    _ (ker_eq_comap_asIdeal _ x) j).symm

/-- **The locus on the chart is open (Stacks 0BDI, part (2), affine case).**  For a bounded
above complex `P` of finite free `A`-modules, the set of primes `p` of `A` at which the derived
fibre Betti numbers `dim_{κ(p)} H^j(P ⊗^L κ(p))`, `j > 0`, all vanish is open: if `P` vanishes
above `b`, only the degrees `0 < j ≤ b` matter, and each of those Betti numbers is upper
semicontinuous. -/
theorem isOpen_setOf_forall_fibreBetti_eq_zero {A : Type u} [CommRing A]
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P) :
    IsOpen {p : PrimeSpectrum A | ∀ j : ℤ, 0 < j →
      StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0} := by
  obtain ⟨b, hb⟩ := hP.upperBound
  have hvan : ∀ (p : PrimeSpectrum A) (j : ℤ), b < j →
      StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0 := by
    intro p j hj
    rw [fibreBetti_eq_zero_iff_isZero_homology (algebraMap A p.asIdeal.ResidueField) hP p
      (Ideal.ker_algebraMap_residueField p.asIdeal) j]
    let K := (CochainComplex.extendScalars (algebraMap A p.asIdeal.ResidueField)).obj P
    have : (DerivedCategory.Q.obj K).IsLE b := by
      have : K.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
        (ModuleCat.extendScalars _).map_isZero (P.isZero_of_isStrictlyLE b i hi)
      infer_instance
    exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj K) b j hj).of_iso
      (StacksDraft.PseudoCoherence.homologyQObjIso K j).symm
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj P) :=
    ⟨P, hP, ⟨Iso.refl _⟩⟩
  have heq : {p : PrimeSpectrum A | ∀ j : ℤ, 0 < j →
      StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0} =
      ⋂ j ∈ Finset.Ioc 0 b,
        StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j ⁻¹' Set.Iio 1 := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iio, Finset.mem_Ioc,
      Nat.lt_one_iff]
    exact ⟨fun h j hj => h j hj.1, fun h j hj =>
      if hjb : j ≤ b then h j ⟨hj, hjb⟩ else hvan p j (by omega)⟩
  rw [heq]
  exact isOpen_biInter_finset fun j _ =>
    (StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent.{u, u}
      _ hpc j).isOpen_preimage 1

/-- **The condition at a test scheme over an affine étale chart.**  Let `φ : Spec(A) ⟶ Y` be a
morphism on which `L` is modelled by a bounded above complex `P` of finite free `A`-modules, and
let `T` be a test scheme over `Spec(A)` with values in a field.  Then the condition at
`T ⟶ Spec(A) ⟶ Y` holds exactly when the derived fibre Betti numbers of `P` in positive degrees
vanish at the prime of `A` through which `T` passes. -/
theorem hasNoNegativeDualExt_comp_chart_iff (L : derivedModules B S hS Y)
    {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (gA : B.obj hA ⟶ B.obj hS)
    (φ : schemeSpace (specFppfOver B S hS hA gA) ⟶ Y)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : ((smallEtaleDerivedPullbackData B S hS).pull φ).obj L ≅
      (chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P))
    (T : SchemesOver (schemeSpace (specFppfOver B S hS hA gA)))
    (hT : Stack.IsFieldObject B S hS T.left) (w : points B S hS (yoneda.obj T.left)) :
    HasNoNegativeDualExt L (T.hom ≫ φ) ↔
      ∀ j : ℤ, 0 < j → StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j
        (pointsToScheme B S hS (specFppfOver B S hS hA gA)
          (pointsMap B S hS _ (schemesOverHom T) w)) = 0 := by
  obtain ⟨k, _, hk, gk, ⟨σ⟩⟩ := exists_specFppfOver_iso_of_isFieldObject hT
  let t : T.left ⟶ specFppfOver B S hS hA gA := Yoneda.fullyFaithful.preimage (schemesOverHom T)
  have ht : yoneda.map t = schemesOverHom T := Yoneda.fullyFaithful.map_preimage _
  obtain ⟨g, w', hh⟩ := exists_eq_specFppfOverMap (σ.hom ≫ t)
  let := g.toAlgebra
  let Φ := (schemeSpaceFunctor B S hS).mapIso σ
  have hq : Φ.hom ≫ (T.hom ≫ φ) =
      schemeSpaceMap (specFppfOverMap B S hS hA gA hk gk w') ≫ φ := by
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map σ.hom ≫ schemesOverHom T ≫ φ.hom =
      yoneda.map (specFppfOverMap B S hS hA gA hk gk w') ≫ φ.hom
    rw [hh, yoneda.map_comp, ht]
    exact (Category.assoc _ _ _).symm
  have hpt : pointsToScheme B S hS (specFppfOver B S hS hA gA)
      (pointsMap B S hS _ (schemesOverHom T) w) =
      PrimeSpectrum.comap (algebraMap A k)
        ((BigFppfOver.toScheme B S hS).map σ.inv (pointsToScheme B S hS T.left w)) := by
    rw [← ht, pointsToScheme_pointsMap_yoneda]
    have : (BigFppfOver.toScheme B S hS).map t = (BigFppfOver.toScheme B S hS).map σ.inv ≫
        (BigFppfOver.toScheme B S hS).map (σ.hom ≫ t) := by
      rw [← Functor.map_comp, ← Category.assoc, σ.inv_hom_id, Category.id_comp]
    rw [this, Scheme.Hom.comp_apply, ← hh]
    rfl
  exact (hasNoNegativeDualExt_iff_of_iso L Φ hq).trans
    ((hasNoNegativeDualExt_chartPoint_iff L hA gA φ P hP eP hk gk w'
      ((BigFppfOver.toScheme B S hS).map σ.inv (pointsToScheme B S hS T.left w))).trans
      (by rw [hpt]))

/-- **The locus is open on an affine étale chart.**  For an étale `φ : Spec(A) ⟶ Y` and a
pseudo-coherent `L`, there is an open set of points of `Spec(A)` through which a test scheme
`T` over `Spec(A)` with values in a field passes exactly when the condition holds at
`T ⟶ Spec(A) ⟶ Y`. -/
theorem exists_isOpen_chart_hasNoNegativeDualExt_iff (L : derivedModules B S hS Y)
    (hL : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L)
    {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (gA : B.obj hA ⟶ B.obj hS) (φ : schemeSpace (specFppfOver B S hS hA gA) ⟶ Y)
    (hφ : IsEtale B S hS φ.hom) :
    ∃ Wc : Set (points B S hS (yoneda.obj (specFppfOver B S hS hA gA))),
      @IsOpen _ (pointTopology B S hS _) Wc ∧
        ∀ T : SchemesOver (schemeSpace (specFppfOver B S hS hA gA)),
          Stack.IsFieldObject B S hS T.left →
          (schemesOverPoints T ⊆ Wc ↔ HasNoNegativeDualExt L
            ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) φ).obj T).hom) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hA gA φ hφ L hL
  obtain ⟨e₁⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ L
  let O : Set ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)) :=
    {p | ∀ j : ℤ, 0 < j →
    StacksDraft.Perfect.fibreBetti.{u, u} (DerivedCategory.Q.obj P) j p = 0}
  refine ⟨pointsToScheme B S hS (specFppfOver B S hS hA gA) ⁻¹' O, ?_, fun T hT => ?_⟩
  · exact (isOpen_yoneda_iff_isSchemeOpen B S hS _ _).2
      ⟨O, isOpen_setOf_forall_fibreBetti_eq_zero hP, fun _ => Iff.rfl⟩
  · obtain ⟨w⟩ := nonempty_points_yoneda_of_isFieldObject hT
    exact (schemesOverPoints_subset_iff hT ⟨w, rfl⟩ _).trans
      (hasNoNegativeDualExt_comp_chart_iff L hA gA φ P hP (e₁.symm ≪≫ eP) T hT w).symm

/-- **The condition does not change under a field extension over `Y`.**  For a morphism
`T₁ ⟶ T₀` of test schemes over `Y` with values in fields and a pseudo-coherent `L`, the
condition holds at `T₀` exactly when it holds at `T₁`.

Both are read on the chart `Spec(k) ≅ T₀` of the space `T₀` itself, on which the pullback of `L`
is modelled by a complex of vector spaces: by
`AlgebraicGeometry.Space.hasNoNegativeDualExt_comp_chart_iff` each condition is the vanishing of
its derived fibre Betti numbers in positive degrees at a prime of `k`, and `k` has one prime. -/
theorem hasNoNegativeDualExt_iff_of_hom (L : derivedModules B S hS Y)
    (hL : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L) {T₁ T₀ : SchemesOver Y}
    (g : T₁ ⟶ T₀) (hT₁ : Stack.IsFieldObject B S hS T₁.left)
    (hT₀ : Stack.IsFieldObject B S hS T₀.left) :
    HasNoNegativeDualExt L T₀.hom ↔ HasNoNegativeDualExt L T₁.hom := by
  let M := ((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj L
  have hM : (smallEtaleRingedSite B S hS _ ((schemeSpaceFunctor B S hS).obj T₀.left).2
      ).IsPseudoCoherent M := isPseudoCoherent_smallEtaleDerivedModulePullback T₀.hom L hL
  obtain ⟨k₀, _, hk₀, gk₀, ⟨σ₀⟩⟩ := exists_specFppfOver_iso_of_isFieldObject hT₀
  let Φ₀ := (schemeSpaceFunctor B S hS).mapIso σ₀
  have hφ₀ : IsEtale B S hS Φ₀.hom.hom :=
    isEtale_of_presheaf_etale B S hS (presheaf_etale_of_iso B S hS (yoneda.mapIso σ₀))
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hk₀ gk₀ Φ₀.hom hφ₀ M hM
  obtain ⟨e₁⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso Φ₀.hom hφ₀ M
  let T₀' : SchemesOver (schemeSpace (specFppfOver B S hS hk₀ gk₀)) :=
    CostructuredArrow.mk (𝟙 _)
  let T₁' : SchemesOver (schemeSpace (specFppfOver B S hS hk₀ gk₀)) :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left ≫ Φ₀.inv)
  have hT₀' : Stack.IsFieldObject B S hS T₀'.left := ⟨k₀, inferInstance, ⟨Iso.refl _⟩⟩
  obtain ⟨w₀⟩ := nonempty_points_yoneda_of_isFieldObject hT₀'
  obtain ⟨w₁⟩ := nonempty_points_yoneda_of_isFieldObject hT₁
  have h₀ := hasNoNegativeDualExt_comp_chart_iff M hk₀ gk₀ Φ₀.hom P hP (e₁.symm ≪≫ eP) T₀'
    hT₀' w₀
  have h₁ := hasNoNegativeDualExt_comp_chart_iff M hk₀ gk₀ Φ₀.hom P hP (e₁.symm ≪≫ eP) T₁'
    hT₁ w₁
  have e₀ : HasNoNegativeDualExt L T₀.hom ↔ HasNoNegativeDualExt M (T₀'.hom ≫ Φ₀.hom) := by
    rw [hasNoNegativeDualExt_iff_of_iso L Φ₀ rfl, hasNoNegativeDualExt_comp_iff]
    change _ ↔ HasNoNegativeDualExt M (𝟙 _ ≫ Φ₀.hom)
    rw [Category.id_comp]
  have e₁' : HasNoNegativeDualExt L T₁.hom ↔ HasNoNegativeDualExt M (T₁'.hom ≫ Φ₀.hom) := by
    rw [← CostructuredArrow.w g, hasNoNegativeDualExt_comp_iff]
    change _ ↔ HasNoNegativeDualExt M (((schemeSpaceFunctor B S hS).map g.left ≫ Φ₀.inv) ≫
      Φ₀.hom)
    rw [Category.assoc, Φ₀.inv_hom_id, Category.comp_id]
  have hpt : pointsToScheme B S hS (specFppfOver B S hS hk₀ gk₀)
        (pointsMap B S hS _ (schemesOverHom T₀') w₀) =
      pointsToScheme B S hS (specFppfOver B S hS hk₀ gk₀)
        (pointsMap B S hS _ (schemesOverHom T₁') w₁) :=
    Subsingleton.elim (α := PrimeSpectrum k₀) _ _
  rw [e₀, e₁', h₀, h₁, hpt]

end Chart

/-! ### The open locus -/

section Locus

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory

/-- **Stacks 0BDI on the small étale site of an algebraic space**, in the form the proof of
Stacks 0DLC, part (1), uses it.  Let `L` be a pseudo-coherent object of `D(𝒪_Y)`.  There is an
open subspace `W` of `Y` such that a point `y : Spec(k) ⟶ Y` with values in a field lies in
`|W|` exactly when `Ext^i(L_y, 𝒪_y) = Hom(Ly^*L, 𝒪[i]) = 0` for every `i < 0`, that is, when the
derived fibre `L ⊗^L κ(y)` has no cohomology in positive degrees.

On every affine étale chart the locus is open
(`AlgebraicGeometry.Space.exists_isOpen_chart_hasNoNegativeDualExt_iff`, from the upper
semicontinuity of the derived fibre Betti numbers), the condition does not change under field
extensions (`AlgebraicGeometry.Space.hasNoNegativeDualExt_iff_of_hom`), and the locus descends to
`Y` (`AlgebraicGeometry.Space.exists_openSubspace_forall_isFieldObject_iff`). -/
theorem exists_openSubspace_hasNoNegativeDualExt_iff (Y : AlgebraicSpaces B S hS)
    (L : derivedModules B S hS Y)
    (hL : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L) :
    ∃ W : OpenSubspaces B S hS Y.1, ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
      (testPoint T₀ ∈ W.1.obj (op T₀.left) ↔ HasNoNegativeDualExt L T₀.hom) :=
  exists_openSubspace_forall_isFieldObject_iff (fun T => HasNoNegativeDualExt L T.hom)
    (fun g hT₁ hT₀ => hasNoNegativeDualExt_iff_of_hom L hL g hT₁ hT₀)
    (fun hA gA φ hφ => exists_isOpen_chart_hasNoNegativeDualExt_iff L hL hA gA φ hφ)

end Locus

end AlgebraicGeometry.Space

end
