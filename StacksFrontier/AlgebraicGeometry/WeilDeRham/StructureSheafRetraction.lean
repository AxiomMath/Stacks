module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsDerivedSectionsAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.ProperSmoothLocalModel
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.ProperSmoothStructureSheafDerivedImage
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.GlobalSections
public import StacksFrontier.Homology.PseudoCoherent.BaseChangeFlat
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.ProjectiveAmplitude
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# Retractions of the structure sheaf of a proper smooth scheme

Let `A` be a ring and let `f : X ⟶ Spec A` be proper and smooth, with `Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`
an isomorphism. Write `A' = Γ(Spec A, 𝒪)` and `R = RΓ(X, 𝒪_X)` in `D(A')`. Given morphisms
`u : A'[0] ⟶ R` and `s : R ⟶ A'[0]` with `u ≫ s = 𝟙`, every morphism `φ : R ⟶ M` to an object
`M` concentrated in degrees `≤ 0` satisfies `s ≫ u ≫ φ = φ`: the idempotent `s ≫ u` of `R` acts
as the identity on morphisms into `D^{≤ 0}(A')`. This is the vanishing used in the proof of
[Stacks, Tag 0G8J].

The proof is the one of the source. Let `C` be the cone of `u`. Since `u ≫ (𝟙 - s ≫ u) = 0`, the
morphism `φ - s ≫ u ≫ φ` factors through `R ⟶ C`, so it suffices that `Hom(C, M) = 0`. The
degree-zero cohomology of `R` is `Γ(X, 𝒪_X) ≅ A'`, and `H⁰(u)` is a split injection of a free
module of rank one into a module isomorphic to it, hence an isomorphism. Locally on `Spec A`, over
a standard open `D(g)`, the derived global sections split as `R_g ≅ N ⊕ P` with `N` concentrated
in degree `0` and `P` a bounded complex of finite free modules in degrees `[1, b]`
([Stacks, Tag 0G8H]); as `H⁰(u_g)` is an isomorphism onto `H⁰(N)`, the cone `C_g` is `P`. So `C`
is perfect ([Stacks, Tag 066Y]) of Tor amplitude in `[1, b]` ([Stacks, Tag 066N]), hence of
projective amplitude in `[1, b]`, and morphisms out of it into `D^{≤ 0}` vanish
([Stacks, Tag 0BCG]).

The same holds with the structure sheaf and the base ring placed in an arbitrary degree `k ≥ 0`
and `M` concentrated in degrees `≤ k`, by shifting.

## Main definitions

* `Stacks.WeilDeRham.structureSheafSections`: `RΓ(X, 𝒪_X)` in `D(Γ(Spec A, 𝒪))`.
* `Stacks.WeilDeRham.baseUnitObject`: `Γ(Spec A, 𝒪)` placed in degree zero.
* `Stacks.WeilDeRham.RetractionVanishing`: the vanishing statement above.

## Main results

* `Stacks.WeilDeRham.retractionVanishing`: the vanishing for `f` proper and smooth with
  `f.appTop` invertible.
* `Stacks.WeilDeRham.retractionVanishing_single`: the same in degree `k`.
* `Stacks.WeilDeRham.comp_eq_self_of_localization_split`: the algebraic statement behind it, for
  an object `T` of `D(B)` with `H⁰(T) ≅ B` which splits locally on `Spec B` as an object in
  degree `0` plus a perfect object of Tor amplitude in `[1, b]`.
* `Stacks.WeilDeRham.hasProjectiveAmplitude_of_localizationSpan`: projective amplitude descends
  from a finite cover of `Spec B` by standard opens on which the object is perfect with a flat
  representative in the given window.
* `Stacks.WeilDeRham.exists_localizationAway_derivedGlobalSectionsOver_iso_biprod`: the local
  splitting of `RΓ(X, 𝒪_X)` of [Stacks, Tag 0G8H], read on modules over a standard open.

## Implementation notes

The local splitting is computed on modules: over a standard open `D(g) ⊆ Spec A` the derived
localization of `RΓ(X, 𝒪_X)` is `RΓ(X_g, 𝒪)` by flat base change for the structure sheaf, and
`X_g` is also the base change of the scheme `X'` over `Spec Γ(Spec A, D(g))` over which
`exists_nhds_globalFunctions_finiteEtale_and_split` (in
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections`) computes `RΓ(X', 𝒪)`. The flat base
change used, `Stacks.WeilDeRham.nonempty_extendScalarsDerived_derivedGlobalSectionsOver_unit_iso`,
is obtained from the base change of `Rh_*𝒪` of
`AlgebraicGeometry.nonempty_derivedPullback_derivedPushforwardModules_unit_iso`, and so asks the
morphism to be separated rather than quasi-separated.

The derived global sections `RΓ(X, 𝒪_X)` of `structureSheafSections` are `Γ(Spec A, 𝒪)`-linear,
while those of `AlgebraicGeometry.derivedGlobalSectionsOver` are `A`-linear; the two are related
by restriction of scalars along `A ≅ Γ(Spec A, 𝒪)`
(`Stacks.WeilDeRham.nonempty_derivedGlobalSectionsOver_iso_restrictScalars`), which induces an
equivalence of derived categories, so the statement over `Γ(Spec A, 𝒪)` follows from the one
over `A`.

Neither a Noetherian base nor a bound on the relative dimension is needed: smoothness is used
only through the local splitting.

All derived categories are taken at the standard model, fixed by the scope
`Stacks.StandardDerivedModel`.

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Tag 0G8H](https://stacks.math.columbia.edu/tag/0G8H)
* [Stacks Project, Tag 0BCG](https://stacks.math.columbia.edu/tag/0BCG)
* [Stacks Project, Tag 066N](https://stacks.math.columbia.edu/tag/066N)
* [Stacks Project, Tag 066Y](https://stacks.math.columbia.edu/tag/066Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase singleD)
open Stacks.Cohomology.DerivedSectionsLeray
  (preimageSections homotopyPreimageSections derivedPreimageSectionsUnit)
open StacksDraft.PseudoCoherence (localizationAwayFunctorAux extendScalarsDerived)
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
  (exists_nhds_globalFunctions_finiteEtale_and_split)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (isRightDerivedFunctor_of_isIso_app_isKInjective exists_quasiIso_isKInjective)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.WeilDeRham

/-! ### A split injection between free modules of rank one -/

section Algebra

variable {B : Type u} [CommRing B]

/-- **A split injection between modules isomorphic to `B` is an isomorphism.** If `i : M ⟶ N`
has a left inverse and `M ≅ B ≅ N`, then `i` is an isomorphism: transported to `B`, it is
multiplication by an element with a left inverse in a commutative ring, that is by a unit. -/
theorem isIso_of_comp_eq_id_of_iso_self {M N : ModuleCat.{u} B} (i : M ⟶ N) (r : N ⟶ M)
    (hir : i ≫ r = 𝟙 M) (eM : M ≅ ModuleCat.of B B) (eN : N ≅ ModuleCat.of B B) : IsIso i := by
  let j : ModuleCat.of B B ⟶ ModuleCat.of B B := eM.inv ≫ i ≫ eN.hom
  let q : ModuleCat.of B B ⟶ ModuleCat.of B B := eN.inv ≫ r ≫ eM.hom
  have hjq : j ≫ q = 𝟙 _ := by
    simp only [j, q, Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hir, Iso.inv_hom_id]
  have hlin : ∀ (h : ModuleCat.of B B ⟶ ModuleCat.of B B) (x : B), h.hom x = x * h.hom 1 := by
    intro h x
    have := h.hom.map_smul x 1
    simpa [smul_eq_mul] using this
  have h1 : q.hom (j.hom 1) = 1 := by
    have := congrArg (fun h => h.hom 1) hjq
    simpa using this
  have hqj : q ≫ j = 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change j.hom (q.hom x) = x
    rw [hlin j, hlin q, mul_assoc, mul_comm (q.hom 1), ← hlin q (j.hom 1), h1, mul_one]
  have : IsIso j := ⟨q, hjq, hqj⟩
  have hi : i = eM.hom ≫ j ≫ eN.inv := by simp [j]
  rw [hi]
  infer_instance

end Algebra

/-! ### The cone of a map into a sum -/

section Triangulated

/-- A morphism `v : X ⟶ N ⊞ P` whose first component is invertible, together with the
inclusion of the second summand, is an isomorphism `X ⊞ P ≅ N ⊞ P`. -/
theorem exists_biprodIso_inl_comp_eq {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [HasBinaryBiproducts 𝒞] {X N P : 𝒞} (v : X ⟶ N ⊞ P)
    (w : N ⟶ X) (h₁ : v ≫ biprod.fst ≫ w = 𝟙 X) (h₂ : w ≫ v ≫ biprod.fst = 𝟙 N) :
    ∃ Θ : X ⊞ P ≅ N ⊞ P, biprod.inl ≫ Θ.hom = v := by
  let Θ : X ⊞ P ⟶ N ⊞ P := biprod.desc v biprod.inr
  let Ξ : N ⊞ P ⟶ X ⊞ P :=
    biprod.lift (biprod.fst ≫ w) (biprod.snd - biprod.fst ≫ w ≫ v ≫ biprod.snd)
  have e₁ : Θ ≫ Ξ = 𝟙 _ := by
    ext
    · simp [Θ, Ξ, h₁, reassoc_of% h₁]
    · simp [Θ, Ξ, h₁, reassoc_of% h₁]
    · simp [Θ, Ξ]
    · simp [Θ, Ξ]
  have e₂ : Ξ ≫ Θ = 𝟙 _ := by
    simp only [Θ, Ξ, biprod.lift_desc]
    ext
    · simp [Preadditive.add_comp, Preadditive.sub_comp, h₂]
    · simp [Preadditive.sub_comp]
    · simp [Preadditive.sub_comp]
    · simp [Preadditive.sub_comp]
  exact ⟨⟨Θ, Ξ, e₁, e₂⟩, biprod.inl_desc _ _⟩

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

/-- **The cone of a map into a sum, off a summand it hits isomorphically.** In a distinguished
triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with `Y ≅ N ⊞ P`, if the composite `X ⟶ Y ≅ N ⊞ P ⟶ N` is an
isomorphism, then `Z ≅ P`. -/
theorem nonempty_iso_obj₃_of_isIso_comp_fst [HasBinaryBiproducts 𝒞] (T : Triangle 𝒞)
    (hT : T ∈ distTriang 𝒞) {N P : 𝒞} (e : T.obj₂ ≅ N ⊞ P)
    (h : IsIso (T.mor₁ ≫ e.hom ≫ biprod.fst)) : Nonempty (T.obj₃ ≅ P) := by
  obtain ⟨Θ, hΘ⟩ := exists_biprodIso_inl_comp_eq (P := P) (T.mor₁ ≫ e.hom)
    (inv (T.mor₁ ≫ e.hom ≫ biprod.fst))
    (by
      have := IsIso.hom_inv_id (T.mor₁ ≫ e.hom ≫ biprod.fst)
      simpa only [Category.assoc] using this)
    (by
      have := IsIso.inv_hom_id (T.mor₁ ≫ e.hom ≫ biprod.fst)
      simpa only [Category.assoc] using this)
  obtain ⟨e', -, -⟩ := exists_iso_of_arrow_iso _ _ (binaryBiproductTriangle_distinguished T.obj₁ P)
    hT (Arrow.isoMk (Iso.refl _) (Θ ≪≫ e.symm) (by
      dsimp [binaryBiproductTriangle]
      simp [reassoc_of% hΘ]))
  exact ⟨(Triangle.π₃.mapIso e').symm⟩

end Triangulated

/-! ### Objects concentrated in degree zero -/

section DegreeZero

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- A morphism between objects of `D(C)` whose cohomology vanishes outside degree `0` is an
isomorphism as soon as it induces one on `H⁰`. -/
theorem isIso_of_isIso_homologyFunctor_zero {X Y : DerivedCategory C} (f : X ⟶ Y)
    (h0 : IsIso ((DerivedCategory.homologyFunctor C 0).map f))
    (hX : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C n).obj X))
    (hY : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C n).obj Y)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  by_cases hn : n = 0
  · subst hn
    exact h0
  · exact ⟨⟨0, (hX n hn).eq_of_src _ _, (hY n hn).eq_of_src _ _⟩⟩

/-- The projection `N ⊞ P ⟶ N` is an isomorphism on `Hⁿ` when `Hⁿ(P) = 0`. -/
theorem isIso_homologyFunctor_map_biprod_fst (N P : DerivedCategory C) (n : ℤ)
    (hP : IsZero ((DerivedCategory.homologyFunctor C n).obj P)) :
    IsIso ((DerivedCategory.homologyFunctor C n).map (biprod.fst : N ⊞ P ⟶ N)) := by
  let H := DerivedCategory.homologyFunctor C n
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts _
  have h : H.map (biprod.fst : N ⊞ P ⟶ N) = (H.mapBiprod N P).hom ≫ biprod.fst := by
    rw [Functor.mapBiprod_hom, biprod.lift_fst]
  have : IsIso (biprod.fst : H.obj N ⊞ H.obj P ⟶ H.obj N) :=
    ⟨⟨biprod.inl, biprod.hom_ext' _ _ (by simp) (hP.eq_of_src _ _), by simp⟩⟩
  rw [h]
  infer_instance

end DegreeZero

/-! ### Descent of projective amplitude -/

/-- Extension of scalars from `B` to a localization `B_g` preserves finite limits. -/
private theorem preservesFiniteLimits_extendScalars_away {B : Type u} [CommRing B] (g : B) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.Away g))) :=
  have : Module.Flat B (Localization.Away g) :=
    IsLocalization.flat (Localization.Away g) (Submonoid.powers g)
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- **Projective amplitude descends along a standard open cover.** Let the elements `g i`
generate the unit ideal of `B`, and let `K` be an object of `D(B)` whose derived localization at
every `g i` is perfect with a flat representative supported in `[a, b]`. Then `K` has projective
amplitude in `[a, b]`.

`K` is perfect by [Stacks, Tag 066Y], hence represented by a bounded complex `E` of finite
projective modules; the Tor amplitude of `E` descends by [Stacks, Tag 066N], and a perfect object
of Tor amplitude in `[a, b]` has a finite projective representative in `[a, b]`
([Stacks, Tag 0658]). -/
theorem hasProjectiveAmplitude_of_localizationSpan {B : Type u} [CommRing B] {ι : Type*}
    [Finite ι] (g : ι → B) (hg : Ideal.span (Set.range g) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} B)) (a b : ℤ)
    (hK : ∀ i, StacksDraft.Perfect.IsPerfect ((localizationAwayFunctorAux.{u, u} (g i)).obj K) ∧
      StacksDraft.Perfect.HasFlatRepresentative
        ((localizationAwayFunctorAux.{u, u} (g i)).obj K) a b) :
    StacksDraft.ProjectiveAmplitude.HasProjectiveAmplitude K a b := by
  have hperf : StacksDraft.Perfect.IsPerfect K :=
    StacksDraft.Perfect.isPerfect_of_localizationSpan g hg K fun i => (hK i).1
  have hpc := ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u}
    K).1.mp hperf).1
  obtain ⟨E, a', b', hGE, hLE, hfin, hproj, ⟨eE⟩⟩ := hperf
  have : ∀ n, Module.Flat B (E.X n) := fun n => by have := hproj n; infer_instance
  have hKE : E.KFlat := CochainComplex.KFlat.kFlat_of_flat.{u, u} E b'
  have hbdd : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (E.X i) :=
    ⟨b', fun i hi => CochainComplex.isZero_of_isStrictlyLE E b' i hi⟩
  have hloc : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude E a b := by
    refine StacksDraft.TorAmplitude.hasTorAmplitude_of_localizationSpan (Set.range g) hg E a b ?_
    rintro ⟨_, i, rfl⟩
    let F := ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.Away (g i)))
    have := preservesFiniteLimits_extendScalars_away (g i)
    have := StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars.{u, u, u}
      (algebraMap B (Localization.Away (g i)))
    let E' := (CochainComplex.extendScalars (algebraMap B (Localization.Away (g i)))).obj E
    have hflat' : ∀ n, Module.Flat (Localization.Away (g i)) (E'.X n) := fun n =>
      Module.Flat.of_linearEquiv
        (StacksDraft.PseudoCoherence.extendScalarsTensorIso
          (S := Localization.Away (g i)) (E.X n)).toLinearEquiv
    have : E'.IsStrictlyLE b' := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro n hn
      exact F.map_isZero (CochainComplex.isZero_of_isStrictlyLE E b' n hn)
    have := hflat'
    have hKE' : E'.KFlat := CochainComplex.KFlat.kFlat_of_flat.{u, u} E' b'
    have hbdd' : ∃ n : ℤ, ∀ m : ℤ, n < m → IsZero (E'.X m) :=
      ⟨b', fun m hm => CochainComplex.isZero_of_isStrictlyLE E' b' m hm⟩
    have e : (localizationAwayFunctorAux.{u, u} (g i)).obj K ≅ DerivedCategory.Q.obj E' :=
      (localizationAwayFunctorAux.{u, u} (g i)).mapIso eE ≪≫ F.mapDerivedCategoryFactors.app E
    have hfr : StacksDraft.TorAmplitude.HasFlatRepresentative (DerivedCategory.Q.obj E') a b :=
      StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso e (hK i).2
    exact (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF
      (StacksDraft.TorAmplitude.canonicalTensorComparison _)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived _) E' hKE' hbdd' hflat' a b).1
      ((StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
        (StacksDraft.TorAmplitude.canonicalTensorComparison _)
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived _) _ a b).2 hfr)
  have hfr : StacksDraft.TorAmplitude.HasFlatRepresentative K a b :=
    StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso eE.symm
      ((StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
        (StacksDraft.TorAmplitude.canonicalTensorComparison _)
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived _) _ a b).1
        ((StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF
          (StacksDraft.TorAmplitude.canonicalTensorComparison _)
          (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived _) E hKE hbdd
          (fun n => inferInstance) a b).2 hloc))
  obtain ⟨P, hP, hPGE, hPLE, ⟨eP⟩⟩ :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u} K).2 a b hpc hfr
  exact ⟨P, ⟨eP.symm⟩, fun n => (hP n).2, hPGE, hPLE⟩

/-! ### The algebraic statement -/

/-- An object of `D(B)` with a flat representative supported in degrees `≥ 1` has no degree-zero
cohomology. -/
theorem isZero_homologyFunctor_zero_of_hasFlatRepresentative {B : Type u} [CommRing B]
    (P : DerivedCategory (ModuleCat.{u} B)) (b : ℤ)
    (hP : StacksDraft.Perfect.HasFlatRepresentative P 1 b) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj P) := by
  obtain ⟨E, -, hGE, -, ⟨e⟩⟩ := hP
  exact (DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj E) 1 0 (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).mapIso e)

/-- **The localized cone.** Let `B[0] ⟶ T ⟶ C ⟶ B[1]` be a distinguished triangle in `D(B)`
whose first map is an isomorphism on `H⁰`. If the derived localization of `T` away from `g` is
`N ⊞ P` with `N` concentrated in degree `0` and `H⁰(P) = 0`, then the derived localization of `C`
is `P`. -/
theorem nonempty_localizationAway_cone_iso {B : Type u} [CommRing B] (g : B)
    {T C : DerivedCategory (ModuleCat.{u} B)}
    {u : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) ⟶ T}
    {v : T ⟶ C} {w : C ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
      (ModuleCat.of B B))⟦(1 : ℤ)⟧} (hT : Triangle.mk u v w ∈ distTriang _)
    (hu0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map u))
    (N P : DerivedCategory (ModuleCat.{u} (Localization.Away g))) [N.IsGE 0] [N.IsLE 0]
    (hP : IsZero ((DerivedCategory.homologyFunctor _ 0).obj P))
    (e : (localizationAwayFunctorAux.{u, u} g).obj T ≅ N ⊞ P) :
    Nonempty ((localizationAwayFunctorAux.{u, u} g).obj C ≅ P) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.Away g))
  have := preservesFiniteLimits_extendScalars_away g
  have := StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars.{u, u, u}
    (algebraMap B (Localization.Away g))
  let L := F.mapDerivedCategory
  have hLT := L.map_distinguished _ hT
  let eL : L.obj T ≅ N ⊞ P := e
  let eT : (L.mapTriangle.obj (Triangle.mk u v w)).obj₂ ≅ N ⊞ P := eL
  have key : IsIso ((L.mapTriangle.obj (Triangle.mk u v w)).mor₁ ≫ eT.hom ≫ biprod.fst) := by
    refine isIso_of_isIso_homologyFunctor_zero _ ?_ ?_ ?_
    · have h1 : IsIso ((DerivedCategory.homologyFunctor _ 0).map (L.map u)) :=
        (NatIso.isIso_map_iff
          (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F 0) u).2
          (by change IsIso (F.map _); infer_instance)
      have h2 := isIso_homologyFunctor_map_biprod_fst N P 0 hP
      change IsIso ((DerivedCategory.homologyFunctor _ 0).map (L.map u ≫ eL.hom ≫ biprod.fst))
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      infer_instance
    · intro n hn
      refine IsZero.of_iso ?_
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F n).app _)
      refine F.map_isZero ?_
      rcases lt_or_gt_of_ne hn with h | h
      · exact DerivedCategory.isZero_of_isGE
          ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of B B)) 0 n h
      · exact DerivedCategory.isZero_of_isLE
          ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of B B)) 0 n h
    · intro n hn
      rcases lt_or_gt_of_ne hn with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 n h
      · exact DerivedCategory.isZero_of_isLE _ 0 n h
  obtain ⟨eC⟩ := nonempty_iso_obj₃_of_isIso_comp_fst _ hLT eT key
  exact ⟨eC⟩

/-- **Retractions of a locally split object act trivially on morphisms into `D^{≤ 0}`.** Let
`T` be an object of `D(B)` with `H⁰(T) ≅ B`, such that around every maximal ideal of `B` there is
a standard open `D(g)` over which the derived localization of `T` is `N ⊞ P`, with `N`
concentrated in degree `0` and `P` perfect with a flat representative supported in `[1, b]`. Then
for `u : B[0] ⟶ T` and `s : T ⟶ B[0]` with `u ≫ s = 𝟙`, every morphism `φ : T ⟶ M` with `M`
concentrated in degrees `≤ 0` satisfies `s ≫ u ≫ φ = φ`.

The cone `C` of `u` is, locally, `P` (`Stacks.WeilDeRham.nonempty_localizationAway_cone_iso`),
hence has projective amplitude in `[1, b]`
(`Stacks.WeilDeRham.hasProjectiveAmplitude_of_localizationSpan`), so morphisms from it to `M`
vanish ([Stacks, Tag 0BCG]); and `φ - s ≫ u ≫ φ` factors through `T ⟶ C`. -/
theorem comp_eq_self_of_localization_split {B : Type u} [CommRing B]
    (T : DerivedCategory (ModuleCat.{u} B))
    (h0 : Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj T ≅
      ModuleCat.of B B))
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ g : B, g ∉ m ∧
      ∃ (N P : DerivedCategory (ModuleCat.{u} (Localization.Away g))) (b : ℤ),
        N.IsGE 0 ∧ N.IsLE 0 ∧ StacksDraft.Perfect.IsPerfect P ∧
        StacksDraft.Perfect.HasFlatRepresentative P 1 b ∧
        Nonempty ((localizationAwayFunctorAux.{u, u} g).obj T ≅ N ⊞ P))
    (u : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) ⟶ T)
    (s : T ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))
    (hus : u ≫ s = 𝟙 _) (M : DerivedCategory (ModuleCat.{u} B)) [M.IsLE 0] (φ : T ⟶ M) :
    s ≫ u ≫ φ = φ := by
  classical
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle u
  have hu0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map u) :=
    isIso_of_comp_eq_id_of_iso_self _ ((DerivedCategory.homologyFunctor _ 0).map s)
      (by rw [← CategoryTheory.Functor.map_comp, hus, CategoryTheory.Functor.map_id])
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).app _) h0.some
  let S : Set B := {g | ∃ (P : DerivedCategory (ModuleCat.{u} (Localization.Away g))) (b : ℤ),
    StacksDraft.Perfect.IsPerfect P ∧ StacksDraft.Perfect.HasFlatRepresentative P 1 b ∧
      Nonempty ((localizationAwayFunctorAux.{u, u} g).obj C ≅ P)}
  have hS : ∀ m : Ideal B, m.IsMaximal → ∃ g ∈ S, g ∉ m := by
    intro m hm
    obtain ⟨g, hgm, N, P, b, hN0, hN0', hP, hPb, ⟨e⟩⟩ := hloc m hm
    exact ⟨g, ⟨P, b, hP, hPb, nonempty_localizationAway_cone_iso g hT hu0 N P
      (isZero_homologyFunctor_zero_of_hasFlatRepresentative P b hPb) e⟩, hgm⟩
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hg, hgm⟩ := hS m hm
    exact hgm (hle (Ideal.subset_span hg))
  obtain ⟨t, hts, ht1⟩ := Submodule.mem_span_finite_of_mem_span
    (show (1 : B) ∈ Ideal.span S by simp [hspan])
  have htspan : Ideal.span (Set.range ((↑) : {x // x ∈ t} → B)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    refine Submodule.span_mono ?_ ht1
    rintro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  choose P b hP hPb e using fun i : {x // x ∈ t} => hts i.2
  obtain ⟨c, hc⟩ := Finite.bddAbove_range b
  have hamp : StacksDraft.ProjectiveAmplitude.HasProjectiveAmplitude C 1 c := by
    refine hasProjectiveAmplitude_of_localizationSpan _ htspan C 1 c fun i => ?_
    refine ⟨StacksDraft.Perfect.isPerfect_of_iso (e i).some (hP i), ?_⟩
    obtain ⟨E, hflat, hGE, hLE, ⟨eE⟩⟩ := hPb i
    have := CochainComplex.isStrictlyLE_of_le E (b i) c (hc ⟨i, rfl⟩)
    exact ⟨E, hflat, hGE, inferInstance, ⟨(e i).some ≪≫ eE⟩⟩
  have hvan := (StacksDraft.ProjectiveAmplitude.hom_eq_zero_and_existsUnique_iso_biprod M C 1 c
    hamp).1 fun i hi => DerivedCategory.isZero_of_isLE M 0 i (by omega)
  obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₂ _ hT (φ - s ≫ u ≫ φ)
    (by simp [Preadditive.comp_sub, reassoc_of% hus])
  rw [hvan γ, comp_zero, sub_eq_zero] at hγ
  exact hγ.symm

/-! ### Derived extension of scalars -/

/-- Extension of scalars of a free module is free. -/
theorem free_extendScalars_obj {B B' : Type u} [CommRing B] [CommRing B'] (ψ : B →+* B')
    (M : ModuleCat.{u} B) [Module.Free B M] :
    Module.Free B' ((ModuleCat.extendScalars.{u, u, u} ψ).obj M) := by
  let := ψ.toAlgebra
  exact Module.Free.of_equiv
    (StacksDraft.PseudoCoherence.extendScalarsTensorIso (S := B') M).toLinearEquiv.symm

/-- Extension of scalars of a finite module is finite. -/
theorem finite_extendScalars_obj {B B' : Type u} [CommRing B] [CommRing B'] (ψ : B →+* B')
    (M : ModuleCat.{u} B) [Module.Finite B M] :
    Module.Finite B' ((ModuleCat.extendScalars.{u, u, u} ψ).obj M) := by
  let := ψ.toAlgebra
  exact Module.Finite.equiv
    (StacksDraft.PseudoCoherence.extendScalarsTensorIso (S := B') M).toLinearEquiv.symm

/-- The terms of a free module placed in degree `0` are free. -/
theorem free_singleFunctor_obj_X {B : Type u} [CommRing B] (M : ModuleCat.{u} B)
    [Module.Free B M] (n : ℤ) :
    Module.Free B (((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj M).X n) := by
  by_cases hn : n = 0
  · subst hn
    exact Module.Free.of_equiv
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).toLinearEquiv.symm
  · have : Subsingleton (((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj M).X n) :=
      ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)
    exact Module.Free.of_subsingleton B _

/-- A biproduct of free modules is free. -/
theorem free_moduleCat_biprod {B : Type u} [CommRing B] (M N : ModuleCat.{u} B)
    [Module.Free B M] [Module.Free B N] : Module.Free B (M ⊞ N : ModuleCat.{u} B) := by
  have : Module.Free B (M × N) := Module.Free.prod B M N
  exact Module.Free.of_equiv
    ((ModuleCat.biprodIsoProd M N).toLinearEquiv : (M ⊞ N : ModuleCat.{u} B) ≃ₗ[B] (M × N)).symm

/-- **Derived base change of a free module plus a finite free complex.** For a ring map
`ψ : B ⟶ B'`, a free `B`-module `M` and a complex `K` of finite free modules supported in
`[1, b]`, the derived base change of `M[0] ⊞ K` is `N ⊞ P` with `N` concentrated in degree `0`
and `P` perfect with a flat representative supported in `[1, b]`. -/
theorem exists_extendScalarsDerived_obj_iso_biprod {B B' : Type u} [CommRing B] [CommRing B']
    (ψ : B →+* B') (M : ModuleCat.{u} B) [Module.Free B M]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (b : ℤ) [K.IsStrictlyGE 1] [K.IsStrictlyLE b]
    (hK : ∀ i, Module.Free B (K.X i) ∧ Module.Finite B (K.X i)) :
    ∃ (N P : DerivedCategory (ModuleCat.{u} B')), N.IsGE 0 ∧ N.IsLE 0 ∧
      StacksDraft.Perfect.IsPerfect P ∧ StacksDraft.Perfect.HasFlatRepresentative P 1 b ∧
      Nonempty ((extendScalarsDerived ψ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M ⊞ DerivedCategory.Q.obj K) ≅
          N ⊞ P) := by
  let G := ModuleCat.extendScalars.{u, u, u} ψ
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj M
  let L := S ⊞ K
  have : ∀ n, Module.Flat B (L.X n) := fun n => by
    have := free_singleFunctor_obj_X M n
    have := (hK n).1
    have := free_moduleCat_biprod (S.X n) (K.X n)
    have : Module.Free B (L.X n) :=
      Module.Free.of_equiv (HomologicalComplex.biprodXIso S K n).toLinearEquiv.symm
    infer_instance
  have : L.IsStrictlyLE (max 0 b) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso S K n)
    rw [biprod_isZero_iff]
    exact ⟨CochainComplex.isZero_of_isStrictlyLE S 0 n (by omega),
      CochainComplex.isZero_of_isStrictlyLE K b n (by omega)⟩
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} B)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} B')) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts (G.mapHomologicalComplex (ComplexShape.up ℤ)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : ∀ i, Module.Free B' ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K |>.X i) :=
    fun i => have := (hK i).1; free_extendScalars_obj ψ (K.X i)
  have : ∀ i, Module.Finite B' ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K |>.X i) :=
    fun i => have := (hK i).2; finite_extendScalars_obj ψ (K.X i)
  refine ⟨DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj S),
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
    inferInstance, inferInstance,
    ⟨_, 1, b, inferInstance, inferInstance, fun i => inferInstance, fun i => inferInstance,
      ⟨Iso.refl _⟩⟩,
    ⟨_, fun i => inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩,
    ⟨(extendScalarsDerived ψ).mapIso (DerivedCategory.Q.mapBiprod S K).symm ≪≫
    StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat ψ L (max 0 b) ≪≫
    DerivedCategory.Q.mapIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapBiprod S K) ≪≫
    DerivedCategory.Q.mapBiprod _ _⟩⟩

/-- **Along an exact extension of scalars, derived extension of scalars is degreewise.** If
extension of scalars along `φ` is exact, its degreewise action on `D(B)` is the total left
derived functor `StacksDraft.PseudoCoherence.extendScalarsDerived φ`, the two being left derived
functors of degreewise extension of scalars. -/
theorem nonempty_mapDerivedCategory_obj_iso_extendScalarsDerived {B B' : Type u} [CommRing B]
    [CommRing B'] (φ : B →+* B') [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ)]
    [PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ)]
    (T : DerivedCategory (ModuleCat.{u} B)) :
    Nonempty ((ModuleCat.extendScalars.{u, u, u} φ).mapDerivedCategory.obj T ≅
      (extendScalarsDerived φ).obj T) := by
  let G := ModuleCat.extendScalars.{u, u, u} φ
  have : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ G.mapDerivedCategory G.mapDerivedCategoryFactors
  exact ⟨(Functor.leftDerivedNatIso G.mapDerivedCategory (extendScalarsDerived φ)
    G.mapDerivedCategoryFactors.hom (StacksDraft.PseudoCoherence.extendScalarsDerivedCounit φ)
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) (Iso.refl _)).app T⟩

/-! ### Flat base change for the structure sheaf -/

/-- **Cohomology and base change for the structure sheaf over an affine base.** For a ring map
`φ : A ⟶ A'`, a flat, quasi-compact and separated `h : W ⟶ Spec A` and its base change
`h' : W' ⟶ Spec A'` along `Spec φ`, the derived base change `RΓ(W, 𝒪_W) ⊗^L_{A, φ} A'` is
`RΓ(W', 𝒪_{W'})`: global sections over `Spec A'` of the base change isomorphism
`Lφ^* Rh_*𝒪_W ≅ Rh'_*𝒪_{W'}` of
`AlgebraicGeometry.nonempty_derivedPullback_derivedPushforwardModules_unit_iso`, read through
`AlgebraicGeometry.derivedGlobalSectionsSpecPullbackIso` and Leray. -/
theorem nonempty_extendScalarsDerived_derivedGlobalSectionsOver_unit_iso {A A' : Type u}
    [CommRing A] [CommRing A'] (φ : A →+* A') {W W' : Scheme.{u}}
    (h : W ⟶ Spec (.of A)) (h' : W' ⟶ Spec (.of A')) (q : W' ⟶ W)
    (hsq : IsPullback q h' h (Spec.map (CommRingCat.ofHom φ))) [QuasiCompact h]
    [IsSeparated h] [Flat h] :
    Nonempty ((extendScalarsDerived φ).obj
        ((derivedGlobalSectionsOver h).obj
          ((DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf))) ≅
      (derivedGlobalSectionsOver h').obj
        ((DerivedCategory.singleFunctor W'.Modules 0).obj
          (SheafOfModules.unit W'.ringCatSheaf))) := by
  let K := (DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)
  obtain ⟨e⟩ := nonempty_derivedPullback_derivedPushforwardModules_unit_iso hsq
  have hqc := fun i : ℤ => isQuasicoherent_homology_derivedPushforward_single_zero h
    (SheafOfModules.unit W.ringCatSheaf)
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W) i
  exact ⟨(extendScalarsDerived φ).mapIso ((derivedGlobalSectionsOverPushforwardIso h).app K) ≪≫
    (derivedGlobalSectionsSpecPullbackIso φ _ hqc).symm ≪≫
    (derivedGlobalSectionsOver (𝟙 (Spec (.of A')))).mapIso e ≪≫
    ((derivedGlobalSectionsOverPushforwardIso h').app _).symm⟩

/-! ### The local splitting of `RΓ(X, 𝒪_X)` -/

/-- **[Stacks, Tag 0G8H] on modules over a standard open.** For `f : X ⟶ Spec A` proper and
smooth and a prime `p` of `A` there is `g ∉ p` such that the derived localization of
`RΓ(X, 𝒪_X)` away from `g` is `N ⊞ P`, with `N` concentrated in degree `0` and `P` perfect with
a flat representative supported in `[1, b]`.

Over the affine open `D(g)` inside the neighbourhood of
`exists_nhds_globalFunctions_finiteEtale_and_split` (in
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections`) the base change `X'` of `X` to
`Spec Γ(Spec A, D(g))` has `RΓ(X', 𝒪) ≅ Γ^r[0] ⊞ K` with `K` finite free in `[1, b]`; the
base change `X_g` of `X'` to `Spec A_g` is the base change of `X` along `Spec A_g ⟶ Spec A`, and
flat base change on both sides identifies the derived localization of `RΓ(X, 𝒪_X)` with the
derived base change of `Γ^r[0] ⊞ K`. -/
theorem exists_localizationAway_derivedGlobalSectionsOver_iso_biprod {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] [Smooth f] (p : PrimeSpectrum A) :
    ∃ g : A, g ∉ p.asIdeal ∧
      ∃ (N P : DerivedCategory (ModuleCat.{u} (Localization.Away g))) (b : ℤ),
        N.IsGE 0 ∧ N.IsLE 0 ∧ StacksDraft.Perfect.IsPerfect P ∧
        StacksDraft.Perfect.HasFlatRepresentative P 1 b ∧
        Nonempty ((localizationAwayFunctorAux.{u, u} g).obj ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))) ≅
            N ⊞ P) := by
  obtain ⟨G, hpG, r, b, H⟩ := exists_nhds_globalFunctions_finiteEtale_and_split f p
  obtain ⟨_, ⟨g, rfl⟩, hpg, hgG⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpG G.2
  let ι : Spec (.of (Localization.Away g)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))
  let V := ι.opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange ι
  have hVG : V ≤ G := by
    intro x hx
    apply hgG
    have hxι : x ∈ Set.range ι := hx
    rwa [show Set.range ι = (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hxι
  obtain ⟨X', f', j, hsq, -, K, hK1, hKb, hKfree, ⟨eR⟩⟩ := H V hV hVG
  have hrange : Set.range ι ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact subset_rfl
  let σ := IsOpenImmersion.lift hV.fromSpec ι hrange
  have hσ : σ ≫ hV.fromSpec = ι := IsOpenImmersion.lift_fac _ _ _
  let ψ : Γ(Spec (.of A), V) →+* Localization.Away g := (Spec.preimage σ).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = σ := by
    simp only [ψ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have : IsProper f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : Smooth f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have sq₁ : IsPullback (pullback.fst f' σ) (pullback.snd f' σ) f'
      (Spec.map (CommRingCat.ofHom ψ)) := by
    rw [hψ]
    exact IsPullback.of_hasPullback f' σ
  have sq₂ : IsPullback (pullback.fst f' σ ≫ j) (pullback.snd f' σ) f
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))) := by
    have hpaste := (IsPullback.of_hasPullback f' σ).paste_horiz hsq
    rwa [hσ] at hpaste
  obtain ⟨bc₁⟩ := nonempty_extendScalarsDerived_derivedGlobalSectionsOver_unit_iso
    (algebraMap A (Localization.Away g)) f (pullback.snd f' σ) _ sq₂
  obtain ⟨bc₂⟩ := nonempty_extendScalarsDerived_derivedGlobalSectionsOver_unit_iso
    ψ f' (pullback.snd f' σ) _ sq₁
  have := hK1
  have := hKb
  obtain ⟨N, P, hN0, hN0', hP, hPb, ⟨eNP⟩⟩ := exists_extendScalarsDerived_obj_iso_biprod ψ
    (ModuleCat.of _ (Fin r → Γ(Spec (.of A), V))) K b hKfree
  have := preservesFiniteLimits_extendScalars_away g
  have := StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars.{u, u, u}
    (algebraMap A (Localization.Away g))
  obtain ⟨cmp⟩ := nonempty_mapDerivedCategory_obj_iso_extendScalarsDerived
    (algebraMap A (Localization.Away g)) ((derivedGlobalSectionsOver f).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)))
  exact ⟨g, hpg, N, P, b, hN0, hN0', hP, hPb,
    ⟨cmp ≪≫ bc₁ ≪≫ bc₂.symm ≪≫ (extendScalarsDerived ψ).mapIso eR ≪≫ eNP⟩⟩

/-! ### The two spellings of `RΓ(X, 𝒪_X)` -/

section Spellings

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The `A`-linear derived global sections are the `Γ(Spec A, 𝒪)`-linear ones with scalars
restricted along `A ≅ Γ(Spec A, 𝒪)`.** Restriction of scalars is exact and the derived sections
over the base are computed by K-injective resolutions, so the composite is a right derived
functor of `A`-linear global sections, and so is `AlgebraicGeometry.derivedGlobalSectionsOver f`.
-/
theorem nonempty_derivedGlobalSectionsOver_iso_restrictScalars (E : DerivedCategory X.Modules) :
    Nonempty ((derivedGlobalSectionsOver f).obj E ≅
      (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (.of A)).inv.hom).mapDerivedCategory.obj
        ((sectionsOverBase f.toLRSHom.toShHom).obj E)) := by
  let G := ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (.of A)).inv.hom
  let RF : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
    sectionsOverBase f.toLRSHom.toShHom ⋙ G.mapDerivedCategory
  have : (preimageSections f.toLRSHom.toShHom ⊤).Additive := ⟨rfl⟩
  let e : homotopyGlobalSectionsOver f ≅
      homotopyPreimageSections f.toLRSHom.toShHom ⊤ ⋙ G.mapDerivedCategory :=
    Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (F := preimageSections f.toLRSHom.toShHom ⊤)
          (G := G) (H := preimageSections f.toLRSHom.toShHom ⊤ ⋙ G)
          (Iso.refl _) (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
      Functor.associator
        ((preimageSections f.toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
        (G.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft
        ((preimageSections f.toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator
        ((preimageSections f.toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
        DerivedCategory.Qh G.mapDerivedCategory).symm
  let α : homotopyGlobalSectionsOver f ⟶ DerivedCategory.Qh ⋙ RF :=
    e.hom ≫ Functor.whiskerRight (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
        G.mapDerivedCategory ≫
      (Functor.associator DerivedCategory.Qh (sectionsOverBase f.toLRSHom.toShHom)
        G.mapDerivedCategory).hom
  have : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_isKInjective _
      (exists_quasiIso_isKInjective X.toRingedSpace) DerivedCategory.Qh _ _ fun I hI => ?_
    have := hI
    have h : IsIso ((derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)).obj I)) :=
      Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
        (preimageSections f.toLRSHom.toShHom ⊤) I
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
    · exact (e.app _).isIso_hom
    · exact Functor.map_isIso G.mapDerivedCategory _
    · infer_instance
  have hiso := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
    (derivedGlobalSectionsOverUnit f) (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    RF α).1 inferInstance
  exact ⟨(@asIso _ _ _ _ _ hiso).app E⟩

/-- **`H⁰(X, 𝒪_X) ≅ A` over `A`** when `Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` is an isomorphism: the
degree-zero cohomology of `RΓ(X, 𝒪_X)` is `Γ(X, 𝒪_X)`, with `A` acting through the bijective
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`. -/
theorem nonempty_homologyFunctor_zero_derivedGlobalSectionsOver_iso [IsIso f.appTop] :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((derivedGlobalSectionsOver f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))) ≅
      ModuleCat.of A A) := by
  let G := ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (.of A)).inv.hom
  have : PreservesFiniteLimits (preimageSections f.toLRSHom.toShHom ⊤) := by
    have h₁ : PreservesFiniteLimits
        (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace
          ((opensMap f.toLRSHom.toShHom).obj ⊤)) :=
      ⟨fun _ _ _ ↦ SheafOfModules.evaluationPreservesLimitsOfShape _ _ _⟩
    have h₂ : PreservesFiniteLimits (ModuleCat.restrictScalars.{u}
        ((structureSheafHom f.toLRSHom.toShHom).hom.app (Opposite.op ⊤)).hom) :=
      ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂
  obtain ⟨eR⟩ := nonempty_derivedGlobalSectionsOver_iso_restrictScalars f
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
  let e₁ := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso eR ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G 0).app _ ≪≫
    G.mapIso (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso
      (preimageSections f.toLRSHom.toShHom ⊤) (sectionsOverBase f.toLRSHom.toShHom)
      (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
      (exists_quasiIso_isKInjective X.toRingedSpace) (SheafOfModules.unit X.ringCatSheaf) 0)
  let θ : A →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
  have hθ : Function.Bijective θ :=
    ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop)
  let l : A →ₗ[A] G.obj ((preimageSections f.toLRSHom.toShHom ⊤).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
    { toFun := fun a => (θ a : Γ(X, ⊤))
      map_add' := fun a b => map_add θ a b
      map_smul' := fun a b => map_mul θ a b }
  exact ⟨e₁ ≪≫ (LinearEquiv.ofBijective l hθ).toModuleIso.symm⟩

end Spellings

/-! ### The vanishing -/

section Vanishing

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Transport of the retraction statement along a faithful functor `Φ` and isomorphisms
`Φ B ≅ B'`, `Φ T ≅ T'`: if retractions `B' ⟶ T'` act trivially on morphisms `T' ⟶ Φ M`, then
retractions `B ⟶ T` act trivially on morphisms `T ⟶ M`. -/
private theorem comp_eq_self_of_map_iso {D D' : Type*} [Category D] [Category D'] (Φ : D ⥤ D')
    [Φ.Faithful] {B T M : D} {B' T' : D'} (eB : Φ.obj B ≅ B') (eT : Φ.obj T ≅ T')
    (key : ∀ (u' : B' ⟶ T') (s' : T' ⟶ B'), u' ≫ s' = 𝟙 _ →
      ∀ φ' : T' ⟶ Φ.obj M, s' ≫ u' ≫ φ' = φ')
    (u : B ⟶ T) (s : T ⟶ B) (hus : u ≫ s = 𝟙 _) (φ : T ⟶ M) : s ≫ u ≫ φ = φ := by
  have h := key (eB.inv ≫ Φ.map u ≫ eT.hom) (eT.inv ≫ Φ.map s ≫ eB.hom)
    (by simp [← Φ.map_comp_assoc, hus]) (eT.inv ≫ Φ.map φ)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, cancel_epi] at h
  apply Φ.map_injective
  rwa [Φ.map_comp, Φ.map_comp]

/-- `RΓ(X, 𝒪_X)`, the derived global sections of the structure sheaf of `X` placed in degree
`0`, as an object of `D(Γ(Spec A, 𝒪))`. -/
abbrev structureSheafSections :
    DerivedCategory (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace)) :=
  (sectionsOverBase f.toLRSHom.toShHom).obj
    (singleD (SheafOfModules.unit (structureSheafRing X.toRingedSpace)))

/-- The base ring `Γ(Spec A, 𝒪)` placed in degree zero, as an object of `D(Γ(Spec A, 𝒪))`. -/
abbrev baseUnitObject : DerivedCategory (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace) (baseRing (Spec (.of A)).toRingedSpace))

/-- **Retractions of `RΓ(X, 𝒪_X)` act trivially on morphisms into `D^{≤ 0}`.** For every
`u : A'[0] ⟶ RΓ(X, 𝒪_X)` with a left inverse `s`, where `A' = Γ(Spec A, 𝒪)`, and every morphism
`φ : RΓ(X, 𝒪_X) ⟶ M` with `M` concentrated in degrees `≤ 0`, one has `s ≫ u ≫ φ = φ`. -/
def RetractionVanishing : Prop :=
  ∀ (u : baseUnitObject (A := A) ⟶ structureSheafSections f)
    (s : structureSheafSections f ⟶ baseUnitObject (A := A)) (_ : u ≫ s = 𝟙 _)
    (M : DerivedCategory (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))) [M.IsLE 0]
    (φ : structureSheafSections f ⟶ M), s ≫ u ≫ φ = φ

/-- **The vanishing of the proof of [Stacks, Tag 0G8J].** For `f : X ⟶ Spec A` proper and
smooth with `Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` an isomorphism, retractions of `RΓ(X, 𝒪_X)` onto
`Γ(Spec A, 𝒪)[0]` act trivially on morphisms into `D^{≤ 0}`.

Restriction of scalars along `A ≅ Γ(Spec A, 𝒪)` is an equivalence of derived categories carrying
`RΓ(X, 𝒪_X)` to the `A`-linear derived global sections, which satisfy the hypotheses of
`Stacks.WeilDeRham.comp_eq_self_of_localization_split` by
`Stacks.WeilDeRham.nonempty_homologyFunctor_zero_derivedGlobalSectionsOver_iso` and
`Stacks.WeilDeRham.exists_localizationAway_derivedGlobalSectionsOver_iso_biprod`. -/
theorem retractionVanishing [IsProper f] [Smooth f] [IsIso f.appTop] : RetractionVanishing f := by
  intro u s hus M _ φ
  let G := ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (.of A)).inv.hom
  let Φ := G.mapDerivedCategory
  have : G.IsEquivalence := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm).isEquivalence_functor
  have : Φ.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence G
  obtain ⟨eR⟩ := nonempty_derivedGlobalSectionsOver_iso_restrictScalars f
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
  let l : A →ₗ[A] G.obj (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
      (baseRing (Spec (.of A)).toRingedSpace)) :=
    { toFun := fun a => ((Scheme.ΓSpecIso (.of A)).inv.hom a :
        (baseRing (Spec (.of A)).toRingedSpace))
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a b => map_mul (Scheme.ΓSpecIso (.of A)).inv.hom a b }
  have hl : Function.Bijective l :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv
  let e₁ : Φ.obj (baseUnitObject (A := A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
    (G.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (LinearEquiv.ofBijective l hl).toModuleIso.symm
  let e₂ : _ ≅ Φ.obj (structureSheafSections f) := eR
  have : (Φ.obj M).IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact IsZero.of_iso (G.map_isZero (DerivedCategory.isZero_of_isLE M 0 i hi))
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G i).app M)
  refine comp_eq_self_of_map_iso Φ e₁ e₂.symm (fun u' s' hus' φ' => ?_) u s hus φ
  exact comp_eq_self_of_localization_split _
    (nonempty_homologyFunctor_zero_derivedGlobalSectionsOver_iso f)
    (fun m hm => exists_localizationAway_derivedGlobalSectionsOver_iso_biprod f ⟨m, hm.isPrime⟩)
    u' s' hus' (Φ.obj M) φ'

/-- **The vanishing in degree `k`.** For `f : X ⟶ Spec A` proper and smooth with
`Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` an isomorphism and `k ≥ 0`, let `A' = Γ(Spec A, 𝒪)`. For every
`u : A'[-k] ⟶ RΓ(X, 𝒪_X[-k])` with a left inverse `s` and every morphism
`φ : RΓ(X, 𝒪_X[-k]) ⟶ M` with `M` concentrated in degrees `≤ k`, one has `s ≫ u ≫ φ = φ`; here
`𝒪_X[-k]` and `A'[-k]` are placed in degree `k`.

Shifting by `k` reduces to `Stacks.WeilDeRham.retractionVanishing`: the derived sections over
the base commute with the shift, being a right derived functor. -/
theorem retractionVanishing_single [IsProper f] [Smooth f] [IsIso f.appTop] (k : ℕ)
    (u : (DerivedCategory.singleFunctor _ (k : ℤ)).obj
        (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
          (baseRing (Spec (.of A)).toRingedSpace)) ⟶
      (sectionsOverBase f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (k : ℤ)).obj (SheafOfModules.unit (structureSheafRing X.toRingedSpace))))
    (s : (sectionsOverBase f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (k : ℤ)).obj (SheafOfModules.unit (structureSheafRing X.toRingedSpace))) ⟶
      (DerivedCategory.singleFunctor _ (k : ℤ)).obj
        (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
          (baseRing (Spec (.of A)).toRingedSpace)))
    (hus : u ≫ s = 𝟙 _)
    (M : DerivedCategory (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace))) [M.IsLE k]
    (φ : (sectionsOverBase f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (k : ℤ)).obj (SheafOfModules.unit (structureSheafRing X.toRingedSpace))) ⟶ M) :
    s ≫ u ≫ φ = φ := by
  let RF := sectionsOverBase f.toLRSHom.toShHom
  let := Functor.IsRightDerivedFunctor.commShift RF
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ
  let O := SheafOfModules.unit (structureSheafRing X.toRingedSpace)
  let e : (DerivedCategory.singleFunctor _ (k : ℤ)).obj O ≅
      ((DerivedCategory.singleFunctor _ 0).obj O)⟦-(k : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors _).shiftIso (-(k : ℤ)) k 0 (by omega)).symm.app O
  let eT : (RF.obj ((DerivedCategory.singleFunctor _ (k : ℤ)).obj O))⟦(k : ℤ)⟧ ≅
      structureSheafSections f :=
    (shiftFunctor _ (k : ℤ)).mapIso (RF.mapIso e ≪≫ (RF.commShiftIso (-(k : ℤ))).app _) ≪≫
      (shiftFunctorCompIsoId _ (-(k : ℤ)) k (by omega)).app _
  let eB : ((DerivedCategory.singleFunctor _ (k : ℤ)).obj
        (ModuleCat.of (baseRing (Spec (.of A)).toRingedSpace)
          (baseRing (Spec (.of A)).toRingedSpace)))⟦(k : ℤ)⟧ ≅ baseUnitObject (A := A) :=
    ((DerivedCategory.singleFunctors _).shiftIso (k : ℤ) 0 k (by omega)).app _
  have : (M⟦(k : ℤ)⟧).IsLE 0 := DerivedCategory.TStructure.t.isLE_shift M k k 0 (by omega)
  exact comp_eq_self_of_map_iso (shiftFunctor _ (k : ℤ)) eB eT
    (fun u' s' hus' φ' => retractionVanishing f u' s' hus' (M⟦(k : ℤ)⟧) φ') u s hus φ

end Vanishing

end Stacks.WeilDeRham

end
