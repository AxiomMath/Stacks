module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Constructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# Noetherian approximation preserving the dimension of the fibres

An affine morphism of finite presentation all of whose fibres have dimension `d` admits an affine
finite-type model, in the sense of `AlgebraicGeometry.FiniteTypeAffineModel`, all of whose fibres
again have dimension `d`. The same holds with the dimension bounded by `d` instead of equal to
`d`, which is the form that covers morphisms with empty fibres.

The proof is the source's. Start from any affine finite-type model `f₀ : X₀ ⟶ S₀` of `f`
(Tag 05FB). Since `S₀` is of finite type over `ℤ`, it is Noetherian, so `f₀` is of finite
presentation and the locus `E ⊆ S₀` where the fibre of `f₀` has dimension `d` is locally
constructible (Tag 05F9). The base-change formula (Tag 05F8) shows that the image of `S` in `S₀`
lands in `E`. Writing `Γ(S, ⊤)` as the filtered colimit of its finite-type `Γ(S₀, ⊤)`-subalgebras
exhibits `S` as the limit of a directed system of affine schemes over `S₀`, and a locally
constructible subset containing the image of the limit already contains the image of a
sufficiently late stage (Tag 05F4). Base changing the model to that stage gives a model whose
fibres all have dimension `d`, again by the base-change formula.

## Main results

* `AlgebraicGeometry.exists_finiteTypeAffineModel_fiberDimension_eq` is **Stacks Tag 05FJ**.
* `AlgebraicGeometry.exists_finiteTypeAffineModel_fiberDimension_le` is the variant with the
  dimension of the fibres bounded by `d`.

## Implementation notes

The two variants are instances of one argument, parameterized by a predicate `P` on
`WithBot ℕ∞` whose only input is that the locus where the fibre dimension satisfies `P` is
locally constructible for every morphism of finite presentation. For equality that is Tag 05F9
directly; for the bound it is the finite union of the level sets at `⊥` and at the naturals at
most `d`, which is why no separate treatment of the empty fibres is needed.

The directed system over `S₀` is `Algebra.FiniteTypeSystem`, whose index type is the finite-type
subalgebras of `Γ(S, ⊤)` containing the chosen finitely generated subring, and the inverse system
of schemes is its spectrum. Tag 05F4 is applied through
`AlgebraicGeometry.DescentSituation`.

## References

* [Stacks Project, Tag 05FJ](https://stacks.math.columbia.edu/tag/05FJ)
* [Stacks Project, Tag 05FB](https://stacks.math.columbia.edu/tag/05FB)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 05F8](https://stacks.math.columbia.edu/tag/05F8)
* [Stacks Project, Tag 05F9](https://stacks.math.columbia.edu/tag/05F9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry

/-- The locus where the dimension of the fibre is at most a natural number is locally
constructible for a morphism of finite presentation: it is the union of the level sets at `⊥`
and at the naturals at most `d`, finitely many of the level sets of Tag 05F9. -/
@[sga "3 VIB 4.1" "(ii)"]
private lemma isLocallyConstructible_setOf_fiberDimension_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : FinitePresentation f) (d : ℕ) :
    IsLocallyConstructible {y : Y | f.fiberDimension y ≤ (d : WithBot ℕ∞)} := by
  classical
  let L : Finset (WithBot ℕ∞) :=
    insert ⊥ ((Finset.range (d + 1)).image fun k ↦ ((k : ℕ) : WithBot ℕ∞))
  have hmem : ∀ v : WithBot ℕ∞, v ≤ (d : WithBot ℕ∞) ↔ v ∈ L := by
    refine fun v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
    · cases v with
      | bot => exact Finset.mem_insert_self _ _
      | coe a =>
        cases a with
        | top =>
          exact absurd (top_le_iff.mp (WithBot.coe_le_coe.mp hv)) (ENat.natCast_ne_top d)
        | coe m =>
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, ?_, ?_⟩)
          · exact Finset.mem_range.mpr (by exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast hv))
          · norm_cast
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact bot_le
      · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have heq : {y : Y | f.fiberDimension y ≤ (d : WithBot ℕ∞)} =
      ⋃ v ∈ (L : Set (WithBot ℕ∞)), {y : Y | f.fiberDimension y = v} := by
    ext y
    simpa using hmem (f.fiberDimension y)
  rw [heq]
  exact IsLocallyConstructible.biUnion L.finite_toSet
    fun v _ ↦ isLocallyConstructible_fiberDimension_eq f hf v

/-- The diagram of the finite-type subalgebras of a ring containing a fixed finitely generated
subring. -/
private def finiteTypeBaseDiagram {R : Type u} [CommRing R] (R₀ : Subring R) :
    Algebra.FiniteTypeSystem.Index R₀ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (Algebra.FiniteTypeSystem.Base R₀ i)
  map {i j} h := CommRingCat.ofHom (Algebra.FiniteTypeSystem.baseMap R₀ (leOfHom h)).toRingHom
  map_id i := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The cocone on the finite-type subalgebras given by their inclusions into the ring. -/
private def finiteTypeBaseCocone {R : Type u} [CommRing R] (R₀ : Subring R) :
    Cocone (finiteTypeBaseDiagram R₀) where
  pt := CommRingCat.of R
  ι :=
    { app := fun i ↦ (CommRingCat.ofHom (Algebra.FiniteTypeSystem.baseToRing R₀ i).toRingHom :
        CommRingCat.of (Algebra.FiniteTypeSystem.Base R₀ i) ⟶ CommRingCat.of R)
      naturality := by intro i j h; ext x; rfl }

/-- A ring is the filtered colimit of its finite-type subalgebras containing a fixed finitely
generated subring. -/
private noncomputable def finiteTypeBaseCoconeIsColimit {R : Type u} [CommRing R]
    (R₀ : Subring R) [Algebra.FiniteType ℤ R₀] : IsColimit (finiteTypeBaseCocone R₀) := by
  classical
  let := reflectsColimit_of_reflectsIsomorphisms (finiteTypeBaseDiagram R₀) (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := Algebra.FiniteTypeSystem.base_jointly_surjective R₀ x
    exact ⟨i, y, hy.symm⟩
  · exact fun i x y h ↦ ⟨i, 𝟙 i, Subtype.ext h⟩

/-- The spectrum of a finite-type subalgebra of a ring maps to the spectrum of the fixed subring
`R₀` through the spectrum of the ring itself. -/
private lemma finiteTypeBaseCone_π_comp {R : Type u} [CommRing R] (R₀ : Subring R)
    (i : Algebra.FiniteTypeSystem.Index R₀) :
    (Scheme.Spec.mapCone (finiteTypeBaseCocone R₀).op).π.app (op i) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i))) =
      Spec.map (CommRingCat.ofHom R₀.subtype) := by
  show Scheme.Spec.map _ ≫ Scheme.Spec.map _ = Scheme.Spec.map _
  rw [← Scheme.Spec.map_comp]
  congr 1

/-- The spectra of the finite-type subalgebras of a ring map compatibly to the spectrum of the
fixed subring `R₀`. -/
private lemma finiteTypeBaseDiagram_map_comp {R : Type u} [CommRing R] (R₀ : Subring R)
    {i j : Algebra.FiniteTypeSystem.Index R₀} (h : i ≤ j) :
    Spec.map (CommRingCat.ofHom (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ j))) =
      ((finiteTypeBaseDiagram R₀).op ⋙ Scheme.Spec).map (homOfLE h).op ≫
        Spec.map (CommRingCat.ofHom (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i))) := by
  show Scheme.Spec.map (CommRingCat.ofHom
      (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ j))).op =
    Scheme.Spec.map (CommRingCat.ofHom (Algebra.FiniteTypeSystem.baseMap R₀ h).toRingHom).op ≫
      Scheme.Spec.map (CommRingCat.ofHom
        (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i))).op
  rw [← Scheme.Spec.map_comp]
  congr 1

/-- A locally constructible subset of `Spec R₀` containing the image of `Spec R` already contains
the image of the spectrum of some finite-type subalgebra of `R` containing `R₀`. -/
private lemma exists_range_subset_of_isLocallyConstructible {R : Type u} [CommRing R]
    (R₀ : Subring R) [Algebra.FiniteType ℤ R₀] {E : Set (Spec (.of R₀))}
    (hE : IsLocallyConstructible E)
    (hR : Set.range (Spec.map (CommRingCat.ofHom R₀.subtype)).base ⊆ E) :
    ∃ i : Algebra.FiniteTypeSystem.Index R₀, Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i)))).base ⊆
        E := by
  classical
  let I := Algebra.FiniteTypeSystem.Index R₀
  let F : Iᵒᵖ ⥤ Scheme.{u} := (finiteTypeBaseDiagram R₀).op ⋙ Scheme.Spec
  let iBase : I := Classical.choice inferInstance
  let D : DescentSituation.{u, u} I :=
    { system := F
      transition_affine := by intro i j h; dsimp [F]; infer_instance
      quasiCompact := by intro i; dsimp [F]; infer_instance
      quasiSeparated := by intro i; dsimp [F]; infer_instance
      limitCone := Scheme.Spec.mapCone (finiteTypeBaseCocone R₀).op
      isLimit := isLimitOfPreserves _ (finiteTypeBaseCoconeIsColimit R₀).op
      base := iBase }
  let g : ∀ i : I, Spec (.of (Algebra.FiniteTypeSystem.Base R₀ i)) ⟶ Spec (.of R₀) := fun i ↦
    Spec.map (CommRingCat.ofHom (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i)))
  have hlim : Set.range (D.limitCone.π.app (op iBase)).base ⊆ g iBase ⁻¹' E := by
    rintro _ ⟨x, rfl⟩
    have h := congrArg (fun q : Spec (.of R) ⟶ Spec (.of R₀) ↦ q x)
      (finiteTypeBaseCone_π_comp R₀ iBase)
    change g iBase ((D.limitCone.π.app (op iBase)) x) =
      (Spec.map (CommRingCat.ofHom R₀.subtype)) x at h
    show g iBase ((D.limitCone.π.app (op iBase)) x) ∈ E
    rw [h]
    exact hR ⟨x, rfl⟩
  obtain ⟨i, hBase, hRange⟩ :=
    (eventually_range_transition_subset_of_isLocallyConstructible D _
      (isLocallyConstructible_preimage _ hE) hlim).exists
  refine ⟨i, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hgi : g i = D.system.map (homOfLE hBase).op ≫ g iBase :=
    finiteTypeBaseDiagram_map_comp R₀ hBase
  have hpoint : g i z = g iBase (D.system.map (homOfLE hBase).op z) := by
    rw [hgi]
    exact Scheme.Hom.comp_apply _ _ z
  show g i z ∈ E
  rw [hpoint]
  exact hRange ⟨z, rfl⟩

/-- The spectrum of the structure map of a finite-type algebra is locally of finite type. -/
private lemma locallyOfFiniteType_spec_algebraMap {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (h : Algebra.FiniteType R A) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr h)

/-- A pushout of rings onto `f.appTop` exhibits a morphism of affine schemes `f` as the base
change of the corresponding morphism of spectra. -/
private lemma isPullback_isoSpec_hom_comp_of_isPushout_appTop {X S : Scheme.{u}} [IsAffine X]
    [IsAffine S] (f : X ⟶ S) {R R' : CommRingCat.{u}} {φ : R ⟶ R'} {ψ : R ⟶ Γ(S, ⊤)}
    {χ : R' ⟶ Γ(X, ⊤)} (h : IsPushout φ ψ χ f.appTop) :
    IsPullback (X.isoSpec.hom ≫ Spec.map χ) f (Spec.map φ) (S.isoSpec.hom ≫ Spec.map ψ) :=
  (isPullback_SpecMap_of_isPushout φ ψ χ f.appTop h).of_iso X.isoSpec.symm (Iso.refl _)
    S.isoSpec.symm (Iso.refl _) (by simp) (Scheme.isoSpec_inv_naturality f) (by simp) (by simp)

/-- Base changing `Spec B₀ ⟶ Spec R₀` to the spectrum of a finite-type subalgebra `R_λ` of
`Γ(S, ⊤)` containing `R₀` gives an affine finite-type model of `f` as soon as the square of rings
is a pushout onto `f.appTop`, and its fibres are those of `Spec B₀ ⟶ Spec R₀` over `Spec R_λ`. -/
private lemma exists_finiteTypeAffineModel_forall_fiberDimension_of_isPushout {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) {R₀ : Subring Γ(S, ⊤)} {B₀ : Type u} [CommRing B₀]
    [Algebra R₀ B₀] [Algebra.FiniteType R₀ B₀] (P : WithBot ℕ∞ → Prop)
    {i : Algebra.FiniteTypeSystem.Index R₀}
    (hRange : Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i)))).base ⊆
        {y | P ((Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀))).fiberDimension y)})
    {χ : CommRingCat.of (Algebra.FiniteTypeSystem.Ring R₀ B₀ i) ⟶ Γ(X, ⊤)}
    (h : IsPushout (CommRingCat.ofHom (algebraMap (Algebra.FiniteTypeSystem.Base R₀ i)
      (Algebra.FiniteTypeSystem.Ring R₀ B₀ i)))
      (CommRingCat.ofHom (Algebra.FiniteTypeSystem.baseToRing R₀ i).toRingHom) χ f.appTop) :
    ∃ m : FiniteTypeAffineModel ⊤ f, ∀ s₀ : m.S₀, P (m.f₀.fiberDimension s₀) := by
  let Si : Scheme.{u} := Spec (.of (Algebra.FiniteTypeSystem.Base R₀ i))
  let fi : Spec (.of (Algebra.FiniteTypeSystem.Ring R₀ B₀ i)) ⟶ Si := Spec.map
    (CommRingCat.ofHom (algebraMap (Algebra.FiniteTypeSystem.Base R₀ i)
      (Algebra.FiniteTypeSystem.Ring R₀ B₀ i)))
  -- Base change the model to the stage `i`.
  have := locallyOfFiniteType_spec_algebraMap (R := R₀) (A := B₀) inferInstance
  have hStagePB : IsPullback
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))
      fi (Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀))) (Spec.map (CommRingCat.ofHom
        (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i)))) := by
    simpa only [fi] using isPullback_SpecMap_of_isPushout
      (CommRingCat.ofHom (algebraMap R₀ B₀))
      (CommRingCat.ofHom (algebraMap R₀ (Algebra.FiniteTypeSystem.Base R₀ i)))
      (CommRingCat.ofHom (S := Algebra.FiniteTypeSystem.Ring R₀ B₀ i)
        Algebra.TensorProduct.includeRight.toRingHom)
      (CommRingCat.ofHom (S := Algebra.FiniteTypeSystem.Ring R₀ B₀ i)
        Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.isPushout_tensorProduct R₀ (Algebra.FiniteTypeSystem.Base R₀ i) B₀).flip
  have hfiDim : ∀ z : Si, P (fi.fiberDimension z) := fun z ↦ by
    rw [congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hStagePB) z, Function.comp_apply]
    exact hRange ⟨z, rfl⟩
  -- Assemble the model.
  exact ⟨{ X₀ := _, S₀ := Si, f₀ := fi, toSource := X.isoSpec.hom ≫ Spec.map χ
           toBase := S.isoSpec.hom ≫ Spec.map
             (CommRingCat.ofHom (Algebra.FiniteTypeSystem.baseToRing R₀ i).toRingHom)
           isPullback := isPullback_isoSpec_hom_comp_of_isPushout_appTop f h
           source_affine := inferInstance, base_affine := inferInstance
           base_locallyOfFiniteType := finiteType_spec_terminal _
           base_quasiCompact := inferInstance
           locallyOfFiniteType := locallyOfFiniteType_spec_algebraMap inferInstance
           quasiCompact := inferInstance
           property := trivial }, hfiDim⟩

/-- The common argument behind the two approximation statements: a predicate on the dimension of
the fibres whose locus is locally constructible for every morphism of finite presentation passes
from a morphism of affine schemes of finite presentation to an affine finite-type model of it. -/
@[ega "IV 8.9.1" "(i), special case"]
private theorem exists_finiteTypeAffineModel_forall_fiberDimension {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) (hf : FinitePresentation f) (P : WithBot ℕ∞ → Prop)
    (hP : ∀ {X' Y' : Scheme.{u}} (g : X' ⟶ Y'), FinitePresentation g →
      IsLocallyConstructible {y : Y' | P (g.fiberDimension y)})
    (hd : ∀ s : S, P (f.fiberDimension s)) :
    ∃ m : FiniteTypeAffineModel ⊤ f, ∀ s₀ : m.S₀, P (m.f₀.fiberDimension s₀) := by
  classical
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  let : Algebra A B := f.appTop.hom.toAlgebra
  have : Algebra.FinitePresentation A B := f.finitePresentation_appTop
  obtain ⟨A₀, B₀, M₀, _, _, _, _, _, _, _, _, φ, hA₀, hB₀, _, hpush, _⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := A) (S := B) B
  let S₀ : Scheme.{u} := Spec (.of A₀)
  let f₀ : Spec (.of B₀) ⟶ S₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))
  let toBase₀ : S ⟶ S₀ := S.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom A₀.subtype)
  have : LocallyOfFiniteType f₀ := locallyOfFiniteType_spec_algebraMap hB₀
  have hp₀ : IsPullback
      (X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B₀ B))) f f₀ toBase₀ := by
    have hsring' : IsPushout (CommRingCat.ofHom (algebraMap A₀ B₀))
        (CommRingCat.ofHom A₀.subtype) (CommRingCat.ofHom (algebraMap B₀ B)) f.appTop := by
      convert CommRingCat.isPushout_iff_isPushout.mpr hpush.symm using 1 <;> ext <;> rfl
    exact isPullback_isoSpec_hom_comp_of_isPushout_appTop f hsring'
  have hdim₀ : ∀ y : S, f.fiberDimension y = f₀.fiberDimension (toBase₀ y) :=
    congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hp₀)
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  -- The directed system of the finite-type subalgebras of `A` over `A₀`.
  obtain ⟨i, hRange⟩ := exists_range_subset_of_isLocallyConstructible A₀
    (E := {y | P (f₀.fiberDimension y)}) (hP f₀ (finitePresentation_of_finiteType f₀)) (by
      rintro _ ⟨x, rfl⟩
      have hcancel : S.isoSpec.hom (S.isoSpec.inv x) = x :=
        (Scheme.homeoOfIso S.isoSpec).apply_symm_apply x
      have hx : Spec.map (CommRingCat.ofHom A₀.subtype) x = toBase₀ (S.isoSpec.inv x) := by
        show _ = (S.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom A₀.subtype)) (S.isoSpec.inv x)
        rw [Scheme.Hom.comp_apply, hcancel]
      show P (f₀.fiberDimension (Spec.map (CommRingCat.ofHom A₀.subtype) x))
      rw [hx, ← hdim₀]
      exact hd _)
  have : Algebra.IsPushout A₀ A B₀ B := hpush
  have hpushi : Algebra.IsPushout (Algebra.FiniteTypeSystem.Base A₀ i) A
      (Algebra.FiniteTypeSystem.Ring A₀ B₀ i) B :=
    Algebra.FiniteTypeSystem.ringToRing_isPushout A₀ B₀ i
  have hsring : IsPushout
      (CommRingCat.ofHom (algebraMap (Algebra.FiniteTypeSystem.Base A₀ i)
        (Algebra.FiniteTypeSystem.Ring A₀ B₀ i)))
      (CommRingCat.ofHom (Algebra.FiniteTypeSystem.baseToRing A₀ i).toRingHom)
      (CommRingCat.ofHom
        (Algebra.FiniteTypeSystem.ringToRing A₀ B₀ (S := B) i).toRingHom) f.appTop := by
    convert CommRingCat.isPushout_iff_isPushout.mpr hpushi.symm using 1 <;> ext <;> rfl
  exact exists_finiteTypeAffineModel_forall_fiberDimension_of_isPushout f P hRange hsring

/-- **Stacks Project, Tag 05FJ.** An affine morphism of finite presentation all of whose fibres
have dimension `d` admits an affine finite-type model all of whose fibres have dimension `d`. -/
@[stacks 05FJ]
public theorem exists_finiteTypeAffineModel_fiberDimension_eq {X S : Scheme.{u}} [IsAffine X]
    [IsAffine S] (f : X ⟶ S) (hf : FinitePresentation f) (d : ℕ)
    (hd : ∀ s : S, f.fiberDimension s = (d : WithBot ℕ∞)) :
    ∃ m : FiniteTypeAffineModel ⊤ f,
      ∀ s₀ : m.S₀, m.f₀.fiberDimension s₀ = (d : WithBot ℕ∞) :=
  exists_finiteTypeAffineModel_forall_fiberDimension f hf (· = (d : WithBot ℕ∞))
    (fun g hg ↦ isLocallyConstructible_fiberDimension_eq g hg (d : WithBot ℕ∞)) hd

/-- An affine morphism of finite presentation all of whose fibres have dimension at most `d`
admits an affine finite-type model with the same bound. Unlike
`AlgebraicGeometry.exists_finiteTypeAffineModel_fiberDimension_eq` this covers morphisms with
empty fibres, whose dimension is `⊥`. -/
public theorem exists_finiteTypeAffineModel_fiberDimension_le {X S : Scheme.{u}} [IsAffine X]
    [IsAffine S] (f : X ⟶ S) (hf : FinitePresentation f) (d : ℕ)
    (hd : ∀ s : S, f.fiberDimension s ≤ (d : WithBot ℕ∞)) :
    ∃ m : FiniteTypeAffineModel ⊤ f,
      ∀ s₀ : m.S₀, m.f₀.fiberDimension s₀ ≤ (d : WithBot ℕ∞) :=
  exists_finiteTypeAffineModel_forall_fiberDimension f hf (· ≤ (d : WithBot ℕ∞))
    (fun g hg ↦ isLocallyConstructible_setOf_fiberDimension_le g hg d) hd

end AlgebraicGeometry

end
