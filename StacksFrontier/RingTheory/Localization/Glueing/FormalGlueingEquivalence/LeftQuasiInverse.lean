module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.Modules
public import StacksFrontier.Topology.Sheaves.Glueing.Equivalence

/-!
# Formal glueing of module categories: compatible sections as a left quasi-inverse

Let `R → S` be a flat map of commutative rings, let `f = (f₁, …, f_t)` be a finite family in `R`
and let `I = (f₁, …, f_t)`. If `R → S` induces an isomorphism `R / I ≅ S / IS`, then the canonical
functor `Can` from `R`-modules to module glueing data and the functor `H⁰` of compatible sections
are quasi-inverse equivalences of categories. This is the formal glueing theorem. It is proved in
three steps: `H⁰` is always a left quasi-inverse of `Can`; when `f` generates the unit ideal the
two functors are already an equivalence, which is ordinary glueing of modules along a Zariski
cover; and the general case follows.

The development, split over the files of `FormalGlueingEquivalence/`, also records two companions
of the theorem. Flat base change carries module glueing data for `R → S` to module glueing data
for the base-changed map `R' → S ⊗[R] R'`, compatibly with both `Can` and `H⁰`. And an `S`-linear
map to or from a module obtained by extension of scalars descends to an `R`-linear map when its
kernel and cokernel are `I`-power torsion, its kernel and cokernel descending as well.

Finally the development registers Stacks 05EV (in `FormalGlueingEquivalence.MainTheorem`), a
remark: a sheaf on a space is equivalent to sheaves on the members of an open cover together with
compatible identifications on their overlaps, and a
tubular neighbourhood of a closed submanifold together with its complement is such a cover;
formal neighbourhoods and the module glueing results of this directory play the analogous role
in algebraic geometry. Its formalizable content is the general sheaf-glueing equivalence
`TopCat.Sheaf.sheafEquivGlueData`, which applies to an arbitrary open cover of an arbitrary
topological space and so is more general than the source's tubular neighbourhood.

This file proves the first step and constructs the counit from the canonical glueing datum of the
compatible sections of a module glueing datum to that datum, showing that `Can` and `H⁰` are an
equivalence once `f` generates the unit ideal and the projections from compatible sections to the
local pieces are localizations. The later steps are in
`FormalGlueingEquivalence.UnitIdeal`, `FormalGlueingEquivalence.BaseChangeFunctor`,
`FormalGlueingEquivalence.BaseChange` and `FormalGlueingEquivalence.MainTheorem`.

## Main results

* `FormalGlueing.canonicalSectionsUnit_isIso`: the canonical natural transformation
  `𝟙 ⟶ Can ⋙ H⁰` is an isomorphism, i.e. `H⁰` is a left quasi-inverse of `Can`.

## Implementation notes

The category of module glueing data and its canonical and compatible-sections functors are
provided by `FormalGlueing.moduleGlueingConstruction`. The ideal `I = (f₁, …, f_t)` is
represented by `Ideal.span (Set.range f)`, the hypothesis that `R / I → S / IS` is an isomorphism
by bijectivity of `Ideal.quotientMap`, and the hypothesis `(f₁, …, f_t) = R` by
`Ideal.span (Set.range f) = ⊤`. A left quasi-inverse is expressed by invertibility of the natural
transformation `𝟙 ⟶ Can ⋙ H⁰`. An `Equivalence` packages both natural isomorphisms and their
compatibility, while the equalities of its functor fields specify that the equivalence uses the
source's canonical functor and `H⁰`, rather than merely asserting that the two categories are
abstractly equivalent. Surjectivity up to torsion of the projection from compatible local
sections is obtained from `ModuleGluingData.proj_isLocalizedModule`.

## References

* [Stacks Project, Tag 05EM](https://stacks.math.columbia.edu/tag/05EM)
-/

/-! ### Compatible sections as a left quasi-inverse -/

section

namespace FormalGlueing

universe u v w

open CategoryTheory Cech FormalGlueing TensorProduct

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

private noncomputable def localCechEquiv (M : ModuleCat.{w} R) (i : Fin r) :
    restrictFromAway f i (canonicalLocalPiece f M i) ≃ₗ[R] cechMod f M {i} :=
  IsLocalizedModule.linearEquiv (Submonoid.closure (f '' (↑({i} : Finset (Fin r)) : Set (Fin r))))
    (canonicalLocalMk f M i) (LocalizedModule.mkLinearMap (cechSub f {i}) M)

private lemma localCechEquiv_mk (M : ModuleCat.{w} R) (i : Fin r) (m : M) :
    localCechEquiv f M i (canonicalLocalMk f M i m) =
      LocalizedModule.mkLinearMap (cechSub f {i}) M m :=
  IsLocalizedModule.linearEquiv_apply _ _ _ m

private lemma exists_singleton_family {ι : Type*}
    (P : Finset ι → Type*) (x : ∀ i, P {i}) :
    ∃ y : (s : {s : Finset ι // s.card = 1}) → P s.val,
      ∀ i, y ⟨{i}, Finset.card_singleton i⟩ = x i := by
  classical
  have h : ∀ s : {s : Finset ι // s.card = 1},
      ∃ z : P s.val, ∀ i (e : s.val = {i}), e ▸ z = x i := by
    rintro ⟨s, hs⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
    refine ⟨x i, ?_⟩
    intro j h
    have : i = j := Finset.singleton_injective h
    subst j
    rfl
  choose y hy using h
  exact ⟨y, fun i ↦ hy ⟨{i}, Finset.card_singleton i⟩ i rfl⟩

variable (S : Type v) [CommRing S] [Algebra R S]

private noncomputable def tensorCechEquiv (M : ModuleCat.{w} R) (i : Fin r) :
    cechMod f (M ⊗[R] S) {i} ≃ₗ[R]
      S ⊗[R] (restrictFromAway f i (canonicalLocalPiece f M i)) := by
  let T := Submonoid.closure (f '' (↑({i} : Finset (Fin r)) : Set (Fin r)))
  let l := (canonicalLocalMk f M i).lTensor S
  have : IsLocalizedModule T l := isLocalized_lTensor S T (canonicalLocalMk f M i)
  have := IsLocalizedModule.of_linearEquiv_right T l (TensorProduct.comm R M S)
  exact IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap (cechSub f {i}) _)
    (l.comp (TensorProduct.comm R M S).toLinearMap)

private lemma tensorCechEquiv_mk (M : ModuleCat.{w} R) (i : Fin r) (m : M) (s : S) :
    tensorCechEquiv f S M i
      (LocalizedModule.mkLinearMap (cechSub f {i}) _ (m ⊗ₜ[R] s)) =
      s ⊗ₜ[R] canonicalLocalMk f M i m := by
  let T := Submonoid.closure (f '' (↑({i} : Finset (Fin r)) : Set (Fin r)))
  let l := (canonicalLocalMk f M i).lTensor S
  have : IsLocalizedModule T l := isLocalized_lTensor S T (canonicalLocalMk f M i)
  have := IsLocalizedModule.of_linearEquiv_right T l (TensorProduct.comm R M S)
  exact IsLocalizedModule.linearEquiv_apply T _ _ (m ⊗ₜ[R] s)

private lemma tensorCechEquiv_comm (M : ModuleCat.{w} R) (i : Fin r) (x : S ⊗[R] M) :
    tensorCechEquiv f S M i (LocalizedModule.mkLinearMap (cechSub f {i}) _
      (TensorProduct.comm R S M x)) =
    canonicalAlpha S f M i
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    exact (tensorCechEquiv_mk f S M i m s).trans (canonicalAlpha_mk S f M i s m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma tensorCechEquiv_map (M : ModuleCat.{w} R) (i : Fin r)
    (x : restrictFromAway f i (canonicalLocalPiece f M i)) :
    tensorCechEquiv f S M i
      (LocalizedModule.map (cechSub f {i}) ((TensorProduct.mk R M S).flip 1)
        (localCechEquiv f M i x)) = 1 ⊗ₜ[R] x := by
  have h : (tensorCechEquiv f S M i).toLinearMap.comp
      (((LocalizedModule.map (cechSub f {i})
        ((TensorProduct.mk R M S).flip 1)).restrictScalars R).comp
        (localCechEquiv f M i).toLinearMap) = TensorProduct.mk R S _ 1 := by
    apply IsLocalizedModule.ext
      (Submonoid.closure (f '' (↑({i} : Finset (Fin r)) : Set (Fin r))))
      (canonicalLocalMk f M i)
      (fun a ↦ (isLocalized_lTensor S _ (canonicalLocalMk f M i)).map_units a)
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, localCechEquiv_mk]
    change tensorCechEquiv f S M i
      (LocalizedModule.map _ _ (LocalizedModule.mk m 1)) = _
    rw [LocalizedModule.map_mk]
    exact tensorCechEquiv_mk f S M i m 1
  exact LinearMap.congr_fun h x

private lemma overlap_isLocalized_pair (M : ModuleCat.{w} R) (i j : Fin r) :
    IsLocalizedModule (Submonoid.closure (f '' (↑({i, j} : Finset (Fin r)) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f {j}) _).comp (canonicalLocalMk f M i)) := by
  simpa only [Finset.singleton_union] using canonicalOverlap_isLocalized f M i {j}

attribute [local instance] overlap_isLocalized_pair

private noncomputable def overlapCechEquiv (M : ModuleCat.{w} R) (i j : Fin r) :
    cechMod f (restrictFromAway f i (canonicalLocalPiece f M i)) {j} ≃ₗ[R]
      cechMod f M {i, j} :=
  IsLocalizedModule.linearEquiv
    (Submonoid.closure (f '' (↑({i, j} : Finset (Fin r)) : Set (Fin r))))
    ((LocalizedModule.mkLinearMap (cechSub f {j}) _).comp (canonicalLocalMk f M i))
    (LocalizedModule.mkLinearMap (cechSub f {i, j}) M)

private lemma overlapCechEquiv_mk_mk (M : ModuleCat.{w} R) (i j : Fin r) (m : M) :
    overlapCechEquiv f M i j
      (LocalizedModule.mkLinearMap (cechSub f {j}) _ (canonicalLocalMk f M i m)) =
      LocalizedModule.mkLinearMap (cechSub f {i, j}) M m :=
  IsLocalizedModule.linearEquiv_apply _ _ _ m

/-- Linear maps out of the localization of `M` at `f i` into the localization at a larger
family agree if they agree on the image of `M`. -/
private lemma canonicalLocalPiece_linearMap_apply_eq (M : ModuleCat.{w} R) (i : Fin r)
    (s : Finset (Fin r)) (hs : ({i} : Finset (Fin r)) ⊆ s)
    (φ ψ : restrictFromAway f i (canonicalLocalPiece f M i) →ₗ[R] cechMod f M s)
    (h : ∀ m : M, φ (canonicalLocalMk f M i m) = ψ (canonicalLocalMk f M i m))
    (x : restrictFromAway f i (canonicalLocalPiece f M i)) : φ x = ψ x :=
  LinearMap.congr_fun (IsLocalizedModule.ext
    (Submonoid.closure (f '' (↑({i} : Finset (Fin r)) : Set (Fin r))))
    (canonicalLocalMk f M i)
    (fun a ↦ IsLocalizedModule.map_units
      (S := Submonoid.closure (f '' (↑s : Set (Fin r))))
      (LocalizedModule.mkLinearMap (cechSub f s) M) ⟨a, closure_mono_of_subset f hs a.2⟩)
    (LinearMap.ext h)) x

private lemma overlapCechEquiv_mk (M : ModuleCat.{w} R) (i j : Fin r)
    (x : restrictFromAway f i (canonicalLocalPiece f M i)) :
    overlapCechEquiv f M i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ x) =
      cechι f M (by simp : ({i} : Finset (Fin r)) ⊆ {i, j}) (localCechEquiv f M i x) :=
  canonicalLocalPiece_linearMap_apply_eq f M i {i, j} (by simp)
    ((overlapCechEquiv f M i j).toLinearMap.comp (LocalizedModule.mkLinearMap (cechSub f {j}) _))
    ((cechι f M (by simp : ({i} : Finset (Fin r)) ⊆ {i, j})).comp
      (localCechEquiv f M i).toLinearMap)
    (fun m ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, overlapCechEquiv_mk_mk,
        localCechEquiv_mk, cechι_mk]) x

private lemma overlapCechEquiv_alphaIJ (M : ModuleCat.{w} R) (i j : Fin r)
    (x : restrictFromAway f i (canonicalLocalPiece f M i)) :
    overlapCechEquiv f M j i
      (canonicalAlphaIJ f M i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ x)) =
      cechι f M (by simp : ({i} : Finset (Fin r)) ⊆ {j, i}) (localCechEquiv f M i x) :=
  canonicalLocalPiece_linearMap_apply_eq f M i {j, i} (by simp)
    ((overlapCechEquiv f M j i).toLinearMap.comp
      ((canonicalAlphaIJ f M i j).toLinearMap.comp
        (LocalizedModule.mkLinearMap (cechSub f {j}) _)))
    ((cechι f M (by simp : ({i} : Finset (Fin r)) ⊆ {j, i})).comp
      (localCechEquiv f M i).toLinearMap)
    (fun m ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, canonicalAlphaIJ_mk,
        overlapCechEquiv_mk_mk, localCechEquiv_mk, cechι_mk]) x

private lemma compatibleSections_pair (M : ModuleCat.{max u v w} R)
    (x : compatibleSections S f (localizationComparisons f) (canonicalDatum S f M))
    (i j : Fin r) :
    cechι f M (by simp : ({i} : Finset (Fin r)) ⊆ {i, j})
        (localCechEquiv f M i (x.1.2 i)) =
      cechι f M (by simp : ({j} : Finset (Fin r)) ⊆ {i, j})
        (localCechEquiv f M j (x.1.2 j)) :=
  (overlapCechEquiv_mk f M i j (x.1.2 i)).symm.trans
    ((congrArg (overlapCechEquiv f M i j) (x.2.2 j i)).symm.trans
      (overlapCechEquiv_alphaIJ f M j i (x.1.2 j)))

/-- If a flat ring map is an isomorphism modulo the ideal generated by `f`, then the map from
a module to the compatible sections of its canonical glueing datum is injective. -/
private theorem canonicalToCompatibleSections_injective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) :
    Function.Injective (canonicalToCompatibleSections S f M) := by
  intro x y hxy
  apply (FormalGlueing.glueingComplex_exact R S f M hflat hq).1
  apply Prod.ext
  · exact (TensorProduct.comm R M S).injective (congrArg (fun z ↦ z.1.1) hxy)
  · funext s
    rcases s with ⟨s, hs⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
    change LocalizedModule.mkLinearMap (cechSub f {i}) M x =
      LocalizedModule.mkLinearMap (cechSub f {i}) M y
    rw [← localCechEquiv_mk f M i x, ← localCechEquiv_mk f M i y]
    exact congrArg (localCechEquiv f M i) (congrArg (fun z ↦ z.1.2 i) hxy)

-- The componentwise comparisons involve several scalar restriction and localization instances.
/-- If a flat ring map is an isomorphism modulo the ideal generated by `f`, then compatible
sections are a left quasi-inverse to the canonical module glueing functor. -/
@[stacks 05EM]
public theorem canonicalSectionsUnit_isIso
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map)) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    IsIso c.canonicalSectionsUnit := by
  dsimp
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [ConcreteCategory.isIso_iff_bijective]
  let e : TensorProduct R M S ≃ₗ[R] TensorProduct R S M := TensorProduct.comm R M S
  change Function.Bijective (canonicalToCompatibleSections S f M)
  refine ⟨canonicalToCompatibleSections_injective R S f hflat hq M, fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := exists_singleton_family (cechMod f M)
    (fun i ↦ localCechEquiv f M i (x.1.2 i))
  let z : TensorProduct R M S × GlueingTerm f M 1 := (e.symm x.1.1, y)
  have hz : glueingBeta S f M z = 0 := by
    apply Prod.ext
    · funext s
      rcases s with ⟨s, hs⟩
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
      change LocalizedModule.mkLinearMap (cechSub f {i}) _ (e.symm x.1.1) -
        LocalizedModule.map (cechSub f {i}) ((TensorProduct.mk R M S).flip 1)
          (y ⟨{i}, Finset.card_singleton i⟩) = 0
      apply sub_eq_zero.mpr
      apply (tensorCechEquiv f S M i).injective
      rw [hy]
      exact (tensorCechEquiv_comm f S M i x.1.1).trans
        ((x.2.1 i).trans (tensorCechEquiv_map f S M i (x.1.2 i)).symm)
    · change -(glueingDifferential f M 1 y) = 0
      have hcy : glueingDifferential f M 1 y = 0 := by
        refine (glueingDifferential_eq_zero_iff f y).mpr ?_
        intro i j
        rw [hy, hy]
        exact compatibleSections_pair f S M x i j
      rw [hcy, neg_zero]
  obtain ⟨m, hm⟩ := ((FormalGlueing.glueingComplex_exact R S f M hflat hq).2 z).mp hz
  refine ⟨m, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · have h : e ((glueingAlpha S f M m).1) = x.1.1 := by
      rw [congrArg Prod.fst hm]
      exact e.apply_symm_apply _
    exact h
  · funext i
    apply (localCechEquiv f M i).injective
    change localCechEquiv f M i (canonicalLocalMk f M i m) = _
    rw [localCechEquiv_mk]
    exact (congrArg (fun z ↦ z.2 (singletonIndex i)) hm).trans (hy i)

end FormalGlueing


end

/-! ### Module glueing equivalence for a unit ideal -/

section

namespace FormalGlueing

universe u v w

open CategoryTheory FormalGlueing TensorProduct Cech

private theorem quotientMap_bijective_of_eq_top
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hI : I = ⊤) :
    Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) := by
  subst I
  have hmap : Ideal.map φ ⊤ = ⊤ := Ideal.map_top φ
  let : Subsingleton (S ⧸ Ideal.map φ ⊤) := by
    rw [hmap]
    infer_instance
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

private theorem canonicalSectionsUnit_isIso_of_span_eq_top
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hf : Ideal.span (Set.range f) = ⊤) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    IsIso c.canonicalSectionsUnit :=
  FormalGlueing.canonicalSectionsUnit_isIso R S f hflat
    (quotientMap_bijective_of_eq_top (algebraMap R S) _ hf)

private theorem restrictScalars_isScalarTower
    {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (M : ModuleCat.{w} A) :
    IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

attribute [local instance] restrictScalars_isScalarTower

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

private noncomputable abbrev sections
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :=
  compatibleSections S f (localizationComparisons f) X

private noncomputable abbrev sectionsGenericProjection
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    sections S f X →ₗ[R] restrictFromTarget (R := R) S X.generic :=
  (LinearMap.fst R _ _).comp (sections S f X).subtype

private noncomputable abbrev sectionsLocalProjection
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    sections S f X →ₗ[R] restrictFromAway f i (X.localPiece i) :=
  (LinearMap.proj i).comp ((LinearMap.snd R _ _).comp (sections S f X).subtype)

private noncomputable def sectionsGenericCounit
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    S ⊗[R] sections S f X →ₗ[S] X.generic :=
  (sectionsGenericProjection S f X).liftBaseChange S

private theorem sectionsGenericCounit_tmul
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (s : S) (x : sections S f X) :
    sectionsGenericCounit S f X (s ⊗ₜ[R] x) = s • (show X.generic from x.1.1) := rfl

private theorem localPiece_map_units
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (i : Fin r) (a : Submonoid.powers (f i)) :
    IsUnit (algebraMap R (Module.End R (restrictFromAway f i (X.localPiece i))) a) :=
  (IsLocalization.map_units (Localization.Away (f i)) a).map
    (Algebra.lsmul R R (restrictFromAway f i (X.localPiece i)))

private noncomputable def sectionsLocalCounit
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    canonicalLocalPiece f (ModuleCat.of R (sections S f X)) i →ₗ[Localization.Away (f i)]
      X.localPiece i := by
  letI := canonicalLocalMk_isLocalized f (ModuleCat.of R (sections S f X)) i
  exact LinearMap.extendScalarsOfIsLocalization (Submonoid.powers (f i))
    (Localization.Away (f i))
    (M := restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R (sections S f X)) i))
    (N := restrictFromAway f i (X.localPiece i))
    (IsLocalizedModule.lift (Submonoid.powers (f i))
      (canonicalLocalMk f (ModuleCat.of R (sections S f X)) i)
      (sectionsLocalProjection S f X i) (localPiece_map_units S f X i))

private theorem sectionsLocalCounit_mk
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (i : Fin r) (x : sections S f X) :
    sectionsLocalCounit S f X i
      (canonicalLocalMk f (ModuleCat.of R (sections S f X)) i x) = x.1.2 i := by
  have := canonicalLocalMk_isLocalized f (ModuleCat.of R (sections S f X)) i
  exact IsLocalizedModule.lift_apply (Submonoid.powers (f i))
    (canonicalLocalMk f (ModuleCat.of R (sections S f X)) i)
    (sectionsLocalProjection S f X i) (localPiece_map_units S f X i) x

private theorem singletonLocalization_isLocalized
    (M : Type*) [AddCommGroup M] [Module R M] (i : Fin r) :
    IsLocalizedModule (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (cechSub f {i}) M) := by
  simpa only [cechSub, Finset.prod_singleton] using
    (inferInstance : IsLocalizedModule (cechSub f {i})
      (LocalizedModule.mkLinearMap (cechSub f {i}) M))

-- Elaborating the scalar restrictions and both compatibility diagrams needs a larger budget.
private noncomputable def sectionsCounit
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    ModuleGlueingMap S f (localizationComparisons f)
      (canonicalDatum S f (ModuleCat.of R (sections S f X))) X where
  generic := ModuleCat.ofHom (sectionsGenericCounit S f X)
  localPiece i := ModuleCat.ofHom (sectionsLocalCounit S f X i)
  alpha_compatibility i m := by
    dsimp only [canonicalDatum] at m ⊢
    change S ⊗[R] sections S f X at m
    change X.alpha i (LocalizedModule.mkLinearMap _ _ (sectionsGenericCounit S f X m)) =
      TensorProduct.map _ _ (canonicalAlpha S f (ModuleCat.of R (sections S f X)) i
        (LocalizedModule.mkLinearMap _ _ m))
    induction m using TensorProduct.inductionOn with
    | tmul s x =>
      rw [sectionsGenericCounit_tmul, map_smul, map_smul, x.2.1 i]
      change s • ((1 : S) ⊗ₜ[R] x.1.2 i) =
        TensorProduct.map _ _ (canonicalAlpha S f (ModuleCat.of R (sections S f X)) i
          (LocalizedModule.mkLinearMap _ _ (s ⊗ₜ[R] x)))
      rw [canonicalAlpha_mk, TensorProduct.map_tmul]
      change s • ((1 : S) ⊗ₜ[R] x.1.2 i) =
        s ⊗ₜ[R] (show restrictFromAway f i (X.localPiece i) from
          sectionsLocalCounit S f X i (canonicalLocalMk f _ i x))
      rw [sectionsLocalCounit_mk, smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simp only [map_add, hx, hy]
  alphaIJ_compatibility i j m := by
    let M := ModuleCat.of R (sections S f X)
    let li := (((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).map
        (ModuleCat.ofHom (sectionsLocalCounit S f X i))).hom)
    let lj := (((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f j)))).map
        (ModuleCat.ofHom (sectionsLocalCounit S f X j))).hom)
    have := canonicalLocalMk_isLocalized f M i
    have := singletonLocalization_isLocalized f (restrictFromAway f j (X.localPiece j)) i
    have h : (X.alphaIJ i j).toLinearMap.comp
        ((LocalizedModule.mkLinearMap (cechSub f {j}) _).comp li) =
      (localizedMap f {i} lj).comp
        ((canonicalAlphaIJ f M i j).toLinearMap.comp
          (LocalizedModule.mkLinearMap (cechSub f {j}) _)) := by
      apply IsLocalizedModule.ext (Submonoid.powers (f i)) (canonicalLocalMk f M i)
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (cechSub f {i})
          (restrictFromAway f j (X.localPiece j))))
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [canonicalAlphaIJ_mk]
      rw [localizedMap_mk f {i} lj (canonicalLocalMk f M j x)]
      change X.alphaIJ i j (LocalizedModule.mkLinearMap _ _
        (sectionsLocalCounit S f X i (canonicalLocalMk f M i x))) =
        LocalizedModule.mkLinearMap (cechSub f {i}) (restrictFromAway f j (X.localPiece j))
          (sectionsLocalCounit S f X j (canonicalLocalMk f M j x))
      rw [sectionsLocalCounit_mk, sectionsLocalCounit_mk]
      exact x.2.2 i j
    exact LinearMap.congr_fun h m

-- Elaborating the scalar restrictions and both compatibility diagrams needs a larger budget.
private noncomputable def sectionsCanonicalCounit :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    compatibleSectionsFunctor S f (localizationComparisons f) ⋙ canonicalFunctor S f ⟶
      𝟭 (ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) := by
  letI := moduleGlueingCategory S f (localizationComparisons f)
  exact
    { app X := sectionsCounit S f X
      naturality {X Y} g := by
        apply ModuleGlueingMap.ext
        · let : Module R Y.generic := Module.compHom _ (algebraMap R S)
          have : IsScalarTower R S Y.generic :=
            IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
          apply ModuleCat.hom_ext
          change (sectionsGenericCounit S f Y).comp
            (AlgebraTensorModule.lTensor S S (compatibleSectionsMap S f g)) =
              g.generic.hom.comp (sectionsGenericCounit S f X)
          apply AlgebraTensorModule.ext
          intro s x
          change sectionsGenericCounit S f Y
            (s ⊗ₜ[R] compatibleSectionsMap S f g x) =
              g.generic (sectionsGenericCounit S f X (s ⊗ₜ[R] x))
          rw [sectionsGenericCounit_tmul, sectionsGenericCounit_tmul]
          exact (g.generic.hom.map_smul s (show X.generic from x.1.1)).symm
        · funext i
          apply (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map_injective
          apply ModuleCat.hom_ext
          have := canonicalLocalMk_isLocalized f (ModuleCat.of R (sections S f X)) i
          apply IsLocalizedModule.ext (Submonoid.powers (f i))
            (canonicalLocalMk f (ModuleCat.of R (sections S f X)) i)
            (localPiece_map_units S f Y i)
          ext x
          change sectionsLocalCounit S f Y i
            (canonicalLocalMap f (ModuleCat.ofHom (compatibleSectionsMap S f g)) i
              (canonicalLocalMk f (ModuleCat.of R (sections S f X)) i x)) =
            g.localPiece i (sectionsLocalCounit S f X i
              (canonicalLocalMk f (ModuleCat.of R (sections S f X)) i x))
          rw [canonicalLocalMap_mk, sectionsLocalCounit_mk, sectionsLocalCounit_mk]
          rfl }

-- Elaborating the scalar restrictions and both compatibility diagrams needs a larger budget.
private theorem sectionsGenericCounit_bijective_of_local
    (hf : Ideal.span (Set.range f) = ⊤)
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (hl : ∀ i, Function.Bijective (sectionsLocalCounit S f X i)) :
    Function.Bijective (sectionsGenericCounit S f X) := by
  have hfS : Ideal.span (Set.range (fun i ↦ algebraMap R S (f i))) = ⊤ := by
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, Ideal.map_top] using
      congrArg (Ideal.map (algebraMap R S)) hf
  apply bijective_of_localized_span _ hfS (sectionsGenericCounit S f X)
  rintro ⟨a, i, rfl⟩
  let M := ModuleCat.of R (sections S f X)
  let li := (((ModuleCat.restrictScalars
    (algebraMap R (Localization.Away (f i)))).map
      (ModuleCat.ofHom (sectionsLocalCounit S f X i))).hom)
  let e := (canonicalAlpha S f M i).trans
    ((AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (LinearEquiv.ofBijective li (hl i))).trans (X.alpha i).symm)
  have h : (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
      (sectionsGenericCounit S f X)).restrictScalars S = e.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers (algebraMap R S (f i)))
      (LocalizedModule.mkLinearMap _ (S ⊗[R] sections S f X))
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S (f i))) X.generic))
    ext m
    apply (X.alpha i).injective
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, e]
    exact (sectionsCounit S f X).alpha_compatibility i m
  change Function.Bijective
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
      (sectionsGenericCounit S f X)).restrictScalars S)
  rw [h]
  exact e.bijective

private theorem sectionsLocalCounit_bijective_of_isLocalized
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r)
    (h : IsLocalizedModule (Submonoid.powers (f i)) (sectionsLocalProjection S f X i)) :
    Function.Bijective (sectionsLocalCounit S f X i) := by
  let M := ModuleCat.of R (sections S f X)
  have := canonicalLocalMk_isLocalized f M i
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers (f i))
    (canonicalLocalMk f M i) (sectionsLocalProjection S f X i)
  let li := (((ModuleCat.restrictScalars
    (algebraMap R (Localization.Away (f i)))).map
      (ModuleCat.ofHom (sectionsLocalCounit S f X i))).hom)
  have he : li = e.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers (f i)) (canonicalLocalMk f M i)
      (localPiece_map_units S f X i)
    ext x
    change sectionsLocalCounit S f X i (canonicalLocalMk f M i x) = e (canonicalLocalMk f M i x)
    rw [sectionsLocalCounit_mk]
    exact (IsLocalizedModule.linearEquiv_apply (Submonoid.powers (f i))
      (canonicalLocalMk f M i) (sectionsLocalProjection S f X i) x).symm
  change Function.Bijective li
  rw [he]
  exact e.bijective

-- Elaborating the scalar restrictions and both compatibility diagrams needs a larger budget.
public theorem glueingMap_isIso_of_bijective
    {comparison : LocalizationComparisons.{u, max u v w} f}
    {X Y : ModuleGlueingDatum.{u, v, w} S f comparison}
    (g : ModuleGlueingMap S f comparison X Y)
    (hg : Function.Bijective g.generic) (hl : ∀ i, Function.Bijective (g.localPiece i)) :
    letI := moduleGlueingCategory S f comparison
    IsIso (show X ⟶ Y from g) := by
  let := moduleGlueingCategory S f comparison
  let eg := LinearEquiv.ofBijective g.generic.hom hg
  let el i := LinearEquiv.ofBijective (g.localPiece i).hom (hl i)
  let er i : restrictFromAway f i (X.localPiece i) ≃ₗ[R]
      restrictFromAway f i (Y.localPiece i) :=
    restrictAwayLinearEquiv f i (N := restrictFromAway f i (Y.localPiece i)) (el i)
  let h : ModuleGlueingMap S f comparison Y X :=
    { generic := ModuleCat.ofHom eg.symm.toLinearMap
      localPiece i := ModuleCat.ofHom (el i).symm.toLinearMap
      alpha_compatibility i m := by
        apply (TensorProduct.congr (LinearEquiv.refl R S) (er i)).injective
        have hc := g.alpha_compatibility i (eg.symm m)
        have hge : g.generic (eg.symm m) = m := eg.apply_symm_apply m
        rw [hge] at hc
        change TensorProduct.map LinearMap.id (er i).toLinearMap
            (X.alpha i (LocalizedModule.mkLinearMap _ _ (eg.symm m))) =
          TensorProduct.map LinearMap.id (er i).toLinearMap
            (TensorProduct.map LinearMap.id (er i).symm.toLinearMap
              (Y.alpha i (LocalizedModule.mkLinearMap _ _ m)))
        rw [TensorProduct.map_map]
        simp only [LinearMap.id_comp, LinearEquiv.comp_symm, TensorProduct.map_id,
          LinearMap.id_apply]
        exact hc.symm
      alphaIJ_compatibility i j m := by
        apply LocalizedModule.map_injective (cechSub f {i}) (er j).toLinearMap (er j).injective
        have hc := g.alphaIJ_compatibility i j ((er i).symm m)
        have hle : g.localPiece i ((er i).symm m) = m := (er i).apply_symm_apply m
        rw [hle] at hc
        change localizedMap f {i} (er j).toLinearMap
            (X.alphaIJ i j (LocalizedModule.mkLinearMap _ _ ((er i).symm m))) =
          localizedMap f {i} (er j).toLinearMap
            (localizedMap f {i} (er j).symm.toLinearMap
              (Y.alphaIJ i j (LocalizedModule.mkLinearMap _ _ m)))
        change _ = ((localizedMap f {i} (er j).toLinearMap).comp
          (localizedMap f {i} (er j).symm.toLinearMap)) _
        rw [← localizedMap_comp, LinearEquiv.comp_symm, localizedMap_id, LinearMap.id_apply]
        exact hc.symm }
  refine ⟨⟨h, ?_, ?_⟩⟩
  · apply ModuleGlueingMap.ext
    · apply ModuleCat.hom_ext
      ext x
      exact eg.symm_apply_apply x
    · funext i
      apply ModuleCat.hom_ext
      ext x
      exact (el i).symm_apply_apply x
  · apply ModuleGlueingMap.ext
    · apply ModuleCat.hom_ext
      ext x
      exact eg.apply_symm_apply x
    · funext i
      apply ModuleCat.hom_ext
      ext x
      exact (el i).apply_symm_apply x

private theorem canonicalFunctor_sections_areQuasiInverse_of_isLocalized
    (hflat : Module.Flat R S) (hf : Ideal.span (Set.range f) = ⊤)
    (hl : ∀ (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) i,
      IsLocalizedModule (Submonoid.powers (f i)) (sectionsLocalProjection S f X i)) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    ∃ e : ModuleCat.{max u v w} R ≌ ModuleGlueingDatum.{u, v, w} S f c.comparison,
      e.functor = c.canonical ∧ e.inverse = c.sections := by
  dsimp only [moduleGlueingConstruction]
  let := moduleGlueingCategory S f (localizationComparisons f)
  have : IsIso (canonicalSectionsUnit.{u, v, w} S f) :=
    canonicalSectionsUnit_isIso_of_span_eq_top R S f hflat hf
  have : IsIso (sectionsCanonicalCounit.{u, v, w} S f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have hb i := sectionsLocalCounit_bijective_of_isLocalized S f X i (hl X i)
    exact glueingMap_isIso_of_bijective S f (sectionsCounit S f X)
      (sectionsGenericCounit_bijective_of_local S f hf X hb) hb
  exact ⟨CategoryTheory.Equivalence.mk (canonicalFunctor S f)
    (compatibleSectionsFunctor S f (localizationComparisons f))
    (asIso (canonicalSectionsUnit S f)) (asIso (sectionsCanonicalCounit.{u, v, w} S f)), rfl, rfl⟩

end FormalGlueing

end
