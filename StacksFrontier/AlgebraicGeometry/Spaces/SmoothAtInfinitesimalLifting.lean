module

public import Mathlib.RingTheory.Artinian.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint

/-!
# Smoothness at a point of an algebraic space by infinitesimal lifting

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, and let `x` be a point of `X`. Then `f` is smooth at `x`
exactly when every solid square

  `Spec B ⟶ X`, `Spec B' ⟶ Y`, over a surjection `B' ⟶ B` of local rings with square-zero
  kernel whose upper map sends the closed point of `Spec B` to `x`,

admits a dotted arrow `Spec B' ⟶ X`, and exactly when the same holds for the small extensions
of Stacks 02HS.

## Main definitions

* `AlgebraicGeometry.Space.LiftsAt` is the pointwise lifting property against a class of ring
  maps.
* `AlgebraicGeometry.Space.FormallySmoothEtaleDescent` is the descent of formal smoothness
  along a surjective étale chart, the one ingredient of Stacks 04AM which this library does
  not carry.

## Main results

* `AlgebraicGeometry.Space.LiftsAt.mono` is the implication from the square-zero condition to
  the small-extension condition.
* `AlgebraicGeometry.Space.isSmoothAt_of_liftsAt_isSmallExtension` is the implication from the
  small-extension condition to smoothness at the point.
* `AlgebraicGeometry.Space.formallySmooth_of_isSmooth` is step (II) of Stacks 04AM, that a
  smooth morphism of algebraic spaces is formally smooth, from
  `AlgebraicGeometry.Space.FormallySmoothEtaleDescent`.
* The equivalence of the three conditions, **Stacks 0APN**, is
  `AlgebraicGeometry.Space.tfae_isSmoothAt_liftsAt` in
  `StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtLiftingCriterion`.

## Implementation notes

The spectra of the two test rings are presented as objects of the big fppf site together with
isomorphisms of their underlying schemes with those spectra, since the site contains only
schemes below its cutoff; a lifting problem is then a pair of sections of `X` and `Y` over
those objects. "The closed point goes to `x`" is recorded by a field-valued representative of a
point of the source test object whose underlying scheme point is the closed point, mapping to
`x` under `AlgebraicGeometry.Space.pointsMap`. Local Noetherianness of the target is the
étale-local scheme property of Stacks 03E6, `AlgebraicGeometry.Space.HasEtaleLocalProperty`.

Two of the three implications are unconditional. From the small-extension condition, a pointed
étale chart `h : U ⟶ V` at `x` whose target chart is Noetherian receives every lifting problem
for `h` along a residually trivial small extension: the problem is pushed into `X` along the
chart, solved there, and pulled back to `U` because the chart is formally étale (Stacks 0616 by
way of Tag 04AL), the pullback being compatible with the chart of `Y` because that chart is
formally étale too. Stacks 02HX then makes `h` smooth at the chart point, which is smoothness
of `f` at `x` by Stacks 04NC. The test spectra arising this way do lie in the site: the rings
are Artinian local with residue field the residue field of `U` at the chart point, so their
cardinality is bounded by `Stacks.Scheme.size_Spec_lt_of_mk_le_max`.

The implication from smoothness at `x` is where Stacks 04AM enters, through the formal
smoothness of a smooth morphism. Only one half of Tag 04AM is in this library,
`AlgebraicGeometry.Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth`; its
step (II) is reduced here to the single statement
`AlgebraicGeometry.Space.FormallySmoothEtaleDescent`, the smooth analogue of
`AlgebraicGeometry.Space.formallyEtale_of_comp`. That reduction is all of
`AlgebraicGeometry.Space.formallySmooth_of_isSmooth`: on a surjective étale chart the induced
morphism of schemes is smooth, hence formally smooth by
`Stacks.Smooth.formallySmoothScheme_of_smooth`, hence the chart of `X` composed with `f` is
formally smooth, the chart of `Y` being formally étale; only the descent along the chart
remains. The descent itself is not proved. Lifts over an affine étale neighbourhood of a point
are `AlgebraicGeometry.Space.exists_etale_affine_local_lift`, so what is missing is only the
glueing, and unlike the formally étale case there is no uniqueness to glue with: the Stacks
Project trivializes the pseudo-torsor of local lifts instead, and the action of
`AlgebraicGeometry.Space.liftActionSheaf` on `AlgebraicGeometry.Space.liftsSubfunctor` which
would make it one is not constructed in this library.

## References

* [Stacks Project, Tag 02HS](https://stacks.math.columbia.edu/tag/02HS)
* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616)
* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Spectra of Artinian local rings in the site -/

/-- A module of finite length over a local ring has cardinality at most the maximum of `ℵ₀`
and the cardinality of the residue field. -/
private theorem cardinalMk_le_max_residueField_of_isFiniteLength
    {R M : Type u} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) :
    Cardinal.mk M ≤ max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R)) := by
  let c : Cardinal := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R))
  induction h with
  | @of_subsingleton M _ _ hsub =>
      let : Subsingleton M := hsub
      have hinj : Function.Injective (fun _ : M => (ULift.up PUnit.unit : ULift.{u} PUnit)) :=
        fun _ _ _ => Subsingleton.elim _ _
      exact (Cardinal.mk_le_of_injective hinj).trans (by
        change Cardinal.mk (ULift.{u} PUnit) ≤ c
        exact le_trans (by simp) (le_max_left _ _))
  | @of_simple_quotient M _ _ N hsimple hN ih =>
      have hfactor : Cardinal.mk (M ⧸ N) ≤ c := by
        obtain ⟨I, hI, ⟨e⟩⟩ :=
          isSimpleModule_iff_quot_maximal.mp
            (show IsSimpleModule R (M ⧸ N) from inferInstance)
        have hIeq : I = IsLocalRing.maximalIdeal R :=
          (IsLocalRing.isMaximal_iff (R := R)).mp hI
        rw [hIeq] at e
        calc
          Cardinal.mk (M ⧸ N) = Cardinal.mk (R ⧸ IsLocalRing.maximalIdeal R) :=
            Cardinal.mk_congr e.toEquiv
          _ = Cardinal.mk (IsLocalRing.ResidueField R) := rfl
          _ ≤ c := le_max_right _ _
      have hNcard : Cardinal.mk N ≤ c := by simpa [c] using ih
      let rep : M ⧸ N → M := fun q => Classical.choose (Submodule.Quotient.mk_surjective N q)
      have hrep (q : M ⧸ N) : Submodule.Quotient.mk (rep q) = q :=
        Classical.choose_spec (Submodule.Quotient.mk_surjective N q)
      let g : (M ⧸ N) × N → M := fun z => rep z.1 + z.2
      have hg : Function.Surjective g := by
        intro m
        let q : M ⧸ N := Submodule.Quotient.mk m
        have hmN : m - rep q ∈ N := by
          apply (Submodule.Quotient.eq N).mp
          simpa [q] using (hrep q).symm
        refine ⟨(q, ⟨m - rep q, hmN⟩), ?_⟩
        simp [g]
      have hprod : Cardinal.mk ((M ⧸ N) × N) ≤ c := by
        calc
          Cardinal.mk ((M ⧸ N) × N) = Cardinal.mk (M ⧸ N) * Cardinal.mk N :=
            (by simpa only [Cardinal.lift_id] using Cardinal.mk_prod (M ⧸ N) N)
          _ ≤ max (max (Cardinal.mk (M ⧸ N)) (Cardinal.mk N)) Cardinal.aleph0 :=
            Cardinal.mul_le_max _ _
          _ ≤ c := by
            apply max_le
            · exact max_le hfactor hNcard
            · exact le_max_left _ _
      exact (Cardinal.mk_le_of_surjective hg).trans hprod

/-- The spectrum of an Artinian local ring lies in the chosen big fppf site as soon as the
spectrum of a field isomorphic to its residue field does: an Artinian ring has finite length
over itself, so its cardinality is bounded by that of its residue field. -/
private theorem contains_spec_of_isArtinianRing_of_residueFieldEquiv
    (B : BigFppfSite.{u}) {R K : Type u}
    [CommRing R] [IsLocalRing R] [IsArtinianRing R] [CommRing K]
    (hK : (Spec (.of K)).size < B.cutoff)
    (e : IsLocalRing.ResidueField R ≃+* K) :
    B.Contains (Spec (.of R)) := by
  have hR := cardinalMk_le_max_residueField_of_isFiniteLength
    ((isArtinianRing_iff_isFiniteLength R).mp inferInstance)
  rw [Cardinal.mk_congr e.toEquiv] at hR
  exact Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hK hR

/-- A surjection of local rings induces an isomorphism of residue fields. -/
private noncomputable def residueFieldEquivOfSurjective
    {R' R : CommRingCat.{u}} [IsLocalRing R'] [IsLocalRing R] (φ : R' ⟶ R)
    (hsurj : Function.Surjective φ.hom) :
    IsLocalRing.ResidueField R' ≃+* IsLocalRing.ResidueField R := by
  let : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hsurj
  let ψ := IsLocalRing.ResidueField.map φ.hom
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨b', rfl⟩ := hsurj b
    exact ⟨IsLocalRing.residue R' b', by
      simp [ψ, IsLocalRing.ResidueField.map_residue]⟩
  exact RingEquiv.ofBijective ψ ⟨RingHom.injective ψ, hψsurj⟩

/-! ### Square-zero closed immersions of site objects -/

/-- A ring surjection with square-zero kernel has square-zero kernel on global sections of the
induced morphism of spectra. -/
theorem specMap_ker_sq_eq_bot {R' R : CommRingCat.{u}}
    (φ : R' ⟶ R) (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ := by
  let : IsAffine (Spec R') := inferInstance
  have hkerApp :
      RingHom.ker (Spec.map φ).appTop.hom =
        (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R').hom.hom := by
    calc
      _ = RingHom.ker ((Scheme.ΓSpecIso R).hom.hom.comp
          (Spec.map φ).appTop.hom) :=
        (RingHom.ker_comp_of_injective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1).symm
      _ = RingHom.ker (φ.hom.comp (Scheme.ΓSpecIso R').hom.hom) := by
        rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
          Scheme.ΓSpecIso_naturality]
      _ = _ := (RingHom.comap_ker _ _).symm
  rw [hkerApp]
  apply eq_bot_iff.mpr
  have hbot : RingHom.ker (Scheme.ΓSpecIso R').hom.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').hom).1
  simpa [hker, ← RingHom.ker_eq_comap_bot, hbot] using
    (Ideal.le_comap_pow (K := RingHom.ker φ.hom)
      (f := (Scheme.ΓSpecIso R').hom.hom) 2)

/-- A morphism of the big fppf site over `S` whose underlying morphism of schemes is, up to
isomorphisms of its source and target, the map of spectra induced by a surjection of rings with
square-zero kernel, is a square-zero closed immersion. -/
theorem isSquareZeroClosedImmersion_of_specMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R' R : CommRingCat.{u}} (φ : R' ⟶ R)
    (hsurj : Function.Surjective φ.hom)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (T T' : BigFppfOver B S hS) (i : T ⟶ T')
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R')
    (hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv) :
    IsSquareZeroClosedImmersion B S hS i := by
  let Tₛ := (BigFppfOver.toScheme B S hS).obj T
  let T'ₛ := (BigFppfOver.toScheme B S hS).obj T'
  let : IsAffine Tₛ := IsAffine.of_isIso e.hom
  let : IsAffine T'ₛ := IsAffine.of_isIso e'.hom
  let : IsAffine (Spec R) := inferInstance
  let : IsAffine (Spec R') := inferInstance
  let : IsIso e.hom := e.isIso_hom
  let : IsIso e'.inv := e'.isIso_inv
  let : IsIso e.hom.appTop := by
    change IsIso (e.hom.app ⊤)
    infer_instance
  let : IsIso e'.inv.appTop := by
    change IsIso (e'.inv.app ⊤)
    infer_instance
  let _ : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ hsurj
  refine ⟨?_, ?_⟩
  · rw [hi]
    infer_instance
  · have hSpecSqTop : RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ :=
      specMap_ker_sq_eq_bot φ hker
    have hmap :
        ((BigFppfOver.toScheme B S hS).map i).appTop.hom =
          e.hom.appTop.hom.comp
            ((Spec.map φ).appTop.hom.comp e'.inv.appTop.hom) := by
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
        congrArg (fun g : Tₛ ⟶ T'ₛ => g.appTop.hom) hi
    have heInjective : Function.Injective e.hom.appTop.hom :=
      (ConcreteCategory.bijective_of_isIso e.hom.appTop).1
    have hkerComp :
        RingHom.ker (e.hom.appTop.hom.comp
          ((Spec.map φ).appTop.hom.comp e'.inv.appTop.hom)) =
            (RingHom.ker (Spec.map φ).appTop.hom).comap e'.inv.appTop.hom := by
      rw [RingHom.ker_comp_of_injective _ heInjective, RingHom.comap_ker]
    have hkerSq :
        RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom ^ 2 = ⊥ := by
      let ρ := (asIso e'.inv.appTop).commRingCatIsoToRingEquiv
      have hρ : e'.inv.appTop.hom = (ρ : _ →+* _) := rfl
      have hcomap :
          (RingHom.ker (Spec.map φ).appTop.hom).comap e'.inv.appTop.hom =
            (RingHom.ker (Spec.map φ).appTop.hom).map ρ.symm := by
        rw [hρ]
        exact (Ideal.map_symm ρ).symm
      rw [hmap, hkerComp]
      calc
        _ = (RingHom.ker (Spec.map φ).appTop.hom).map ρ.symm ^ 2 := by rw [hcomap]
        _ = (RingHom.ker (Spec.map φ).appTop.hom ^ 2).map ρ.symm := by rw [Ideal.map_pow]
        _ = ⊥ := by rw [hSpecSqTop]; simp
    apply Scheme.IdealSheafData.ext_of_isAffine
    change (((BigFppfOver.toScheme B S hS).map i).ker.ideal
      ⟨⊤, isAffineOpen_top T'ₛ⟩) ^ 2 = ⊥
    rw [AlgebraicGeometry.Scheme.ker_of_isAffine]
    simpa [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_bot,
      Scheme.IdealSheafData.ofIdealTop] using hkerSq

/-! ### The pointwise lifting condition -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The infinitesimal lifting property of a morphism of algebraic spaces at a point of its
source, against a class of ring maps.

A lifting problem consists of an extension `φ : R' ⟶ R` in the class with `R` local, a
presentation of `Spec R` and `Spec R'` by objects `T`, `T'` of the site, a field-valued
representative of the closed point of `Spec R`, and sections `α` of `X` over `T` and `β` of `Y`
over `T'` forming a commutative square and sending that representative to `x`. -/
abbrev LiftsAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X)
    (extension : ∀ ⦃R' R : CommRingCat.{u}⦄, (R' ⟶ R) → Prop) : Prop :=
  ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R), extension φ →
    ∀ (T T' : BigFppfOver B S hS) (i : T ⟶ T')
      (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
      (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R'),
      (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv →
      ∀ [IsLocalRing R] (p : FieldValuedPoint B S hS (yoneda.obj T)),
        schemePoint B S hS T p = e.inv (IsLocalRing.closedPoint R) →
        ∀ (α : yoneda.obj T ⟶ X) (β : yoneda.obj T' ⟶ Y),
          pointsMap B S hS (yoneda.obj T) α (p.class B S hS (yoneda.obj T)) = x →
          α ≫ f = yoneda.map i ≫ β →
      ∃ γ : yoneda.obj T' ⟶ X, yoneda.map i ≫ γ = α ∧ γ ≫ f = β

/-- **Stacks 0APN, (2) implies (3).** The lifting property at a point against a class of
extensions implies the lifting property against any subclass. -/
@[stacks 0APN "condition (2) implies condition (3)"]
theorem LiftsAt.mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {x : points B S hS X}
    {extension extension' : ∀ ⦃R' R : CommRingCat.{u}⦄, (R' ⟶ R) → Prop}
    (hsub : ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R), extension' φ → extension φ)
    (h : LiftsAt B S hS f x extension) :
    LiftsAt B S hS f x extension' := by
  intro R' R φ hφ T T' i e e' hi hRloc p hp α β hpx hcomm
  have := hRloc
  exact h φ (hsub φ hφ) T T' i e e' hi p hp α β hpx hcomm

/-! ### From formal smoothness to the lifting condition -/

/-- A commutative square of Yoneda sections is the same as the equation of the corresponding
elements. -/
private theorem app_yonedaEquiv_eq_map_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T') (α : yoneda.obj T ⟶ F) (β : yoneda.obj T' ⟶ G) :
    a.app (op T) (yonedaEquiv α) = G.map i.op (yonedaEquiv β) ↔ α ≫ a = yoneda.map i ≫ β := by
  rw [← yonedaEquiv_comp, yonedaEquiv_naturality, EmbeddingLike.apply_eq_iff_eq]

/-- A lift of a commutative square of Yoneda sections is the same as a section making both
triangles commute. -/
private theorem isLift_yonedaEquiv_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T') (α : yoneda.obj T ⟶ F) (β : yoneda.obj T' ⟶ G)
    (γ : yoneda.obj T' ⟶ F) :
    IsLift a i (yonedaEquiv α) (yonedaEquiv β) (yonedaEquiv γ) ↔
      yoneda.map i ≫ γ = α ∧ γ ≫ a = β := by
  rw [IsLift, yonedaEquiv_naturality, ← yonedaEquiv_comp, EmbeddingLike.apply_eq_iff_eq,
    EmbeddingLike.apply_eq_iff_eq]

/-- A formally smooth morphism of algebraic spaces has the lifting property at every point of
its source, against every class of square-zero surjections of local rings. -/
@[sga "3 XI 1.8" "smoothness clause"]
private theorem liftsAt_of_formallySmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X)
    (hformal : FormallySmooth f)
    (extension : ∀ ⦃R' R : CommRingCat.{u}⦄, (R' ⟶ R) → Prop)
    (hextension : ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R),
      extension φ → InfinitesimalLifting.IsSquareZeroSurjection φ) :
    LiftsAt B S hS f x extension := by
  intro R' R φ hφ T T' i e e' hi hRloc _p _ α β _ hcomm
  have := hRloc
  have hsq : InfinitesimalLifting.IsSquareZeroSurjection φ := hextension φ hφ
  have hsite : IsSquareZeroClosedImmersion B S hS i :=
    isSquareZeroClosedImmersion_of_specMap B S hS φ hsq.2.2.1 hsq.2.2.2 T T' i e e' hi
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.hom
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := IsAffine.of_isIso e'.hom
  obtain ⟨z, hz⟩ := hformal T T' ‹_› ‹_› i hsite (yonedaEquiv α) (yonedaEquiv β)
    ((app_yonedaEquiv_eq_map_iff B S hS f i α β).mpr hcomm)
  obtain ⟨γ, rfl⟩ := yonedaEquiv.surjective z
  exact ⟨γ, (isLift_yonedaEquiv_iff B S hS f i α β γ).mp hz⟩

/-- A section of an algebraic space over the spectrum of a local ring whose closed point lies
in an open subspace factors through that open subspace: the closed point is a specialization of
every point, so the whole spectrum lands in the open set of points. -/
private theorem factorsThrough_of_spec_isLocalRing
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (T : BigFppfOver B S hS) (R : CommRingCat.{u}) [IsLocalRing R]
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (α : yoneda.obj T ⟶ X) (p : FieldValuedPoint B S hS (yoneda.obj T))
    (hp : schemePoint B S hS T p = e.inv (IsLocalRing.closedPoint R))
    (x : points B S hS X)
    (hpx : pointsMap B S hS (yoneda.obj T) α (p.class B S hS (yoneda.obj T)) = x)
    (hx : x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    ∃ α' : yoneda.obj T ⟶ U.toFunctor, α' ≫ U.ι = α := by
  let W : Set (points B S hS X) := Set.range (pointsMap B S hS U.toFunctor U.ι)
  have hW : IsOpen W := by
    have h := (openSubspacesOrderIso B S hS X hX ⟨U, hU⟩).2
    rwa [openSubspacesOrderIso_apply B S hS X hX ⟨U, hU⟩] at h
  let D : Set (points B S hS (yoneda.obj T)) := pointsMap B S hS (yoneda.obj T) α ⁻¹' W
  have hD : IsOpen D := (continuous_pointsMap B S hS α).isOpen_preimage W hW
  obtain ⟨V, hV, hVspec⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS T D).mp hD
  have hclosed : schemePoint B S hS T p ∈ V := by
    refine (hVspec p).mp ?_
    change pointsMap B S hS (yoneda.obj T) α (p.class B S hS (yoneda.obj T)) ∈ W
    rw [hpx]
    exact hx
  have hspec : ∀ z : (BigFppfOver.toScheme B S hS).obj T,
      z ⤳ schemePoint B S hS T p := by
    intro z
    have h₀ := IsLocalRing.specializes_closedPoint (e.hom.base z)
    have h₁ := h₀.map (f := e.inv.base) e.inv.continuous
    have hz : e.inv.base (e.hom.base z) = z := by simp
    simpa [hz, hp] using h₁
  have hVall : ∀ z : (BigFppfOver.toScheme B S hS).obj T, z ∈ V :=
    fun z => (hspec z).mem_open hV hclosed
  refine (factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS T) U hU α).2 ?_
  intro y hy
  rcases hy with ⟨y₀, rfl⟩
  induction y₀ using Quot.inductionOn with
  | h q => exact (hVspec q).mpr (hVall (schemePoint B S hS T q))

/-! ### Step (II) of Stacks 04AM -/

/-- **The descent of formal smoothness along a surjective étale chart.** If `a` is a
representable, surjective, étale transformation and `a ≫ b` is formally smooth, with `b`'s
source and target sheaves for the étale topology, then `b` is formally smooth.

This is the smooth analogue of `AlgebraicGeometry.Space.formallyEtale_of_comp` and the only
ingredient of step (II) of [Stacks Project, Tag 04AM] that this library does not carry. Lifts
do exist over an affine étale neighbourhood of every point, by
`AlgebraicGeometry.Space.exists_etale_affine_local_lift`; what is missing is the glueing. The
formally étale case glues by uniqueness, which formal smoothness does not supply, and the
Stacks Project instead trivializes the pseudo-torsor of local lifts. Its sheaf of lifts is
`AlgebraicGeometry.Space.liftsSubfunctor` and the acting sheaf of module homomorphisms is
`AlgebraicGeometry.Space.liftActionSheaf`, but the action of the second on the first is not
constructed, for want of the twisting of the structure map of a morphism by a derivation. -/
def FormallySmoothEtaleDescent : Prop :=
  ∀ s : RepresentableSurjectiveEtaleSituation.{u},
    Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G →
    Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.H →
    FormallySmooth (s.a ≫ s.b) → FormallySmooth s.b

/-- **Stacks 04AM, step (II).** A smooth morphism of algebraic spaces over `S` is formally
smooth, granted that formal smoothness descends along a surjective étale chart.

On a surjective étale chart of the morphism the induced morphism of schemes is smooth, hence
formally smooth by `Stacks.Smooth.formallySmoothScheme_of_smooth`, hence its Yoneda image is
formally smooth; the chart of the target is formally étale by Tag 04AL, so the chart of the
source composed with the morphism is formally smooth. Only the descent along the chart
remains. -/
theorem formallySmooth_of_isSmooth (hdescent : FormallySmoothEtaleDescent.{u})
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsSmooth B S hS f) :
    FormallySmooth f := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  have hψ : Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
    hf U V a b ψ haEtale hbEtale hdiag.symm
  have hψF : FormallySmooth (yoneda.map ψ) :=
    formallySmooth_yoneda_map_of_formallySmoothScheme
      (Stacks.Smooth.formallySmoothScheme_of_smooth _)
  have hbF : FormallySmooth b := fun T T' hT hT' i hi z w hzw =>
    let ⟨v, hv⟩ := formallyEtale_of_etale B S hS b hbEtale T T' hT hT' i hi z w hzw
    ⟨v, hv.1⟩
  have hcomp : FormallySmooth (a ≫ f) := by
    rw [hdiag]
    exact FormallySmooth.comp _ _ hψF hbF
  exact hdescent
    { B := B, S := S, hS := hS, F := yoneda.obj U, G := X, H := Y, a := a, b := f
      representable_a := haEtale.1, surjective_a := haSurj, etale_a := haEtale }
    (isSheaf_etaleTopology_over_of_isAlgebraicSpace B S hS hX)
    (isSheaf_etaleTopology_over_of_isAlgebraicSpace B S hS hY) hcomp

/-- **Stacks 0APN, (1) implies (2) and (3).** A morphism of algebraic spaces over `S` which is
smooth at a point of its source has the lifting property at that point against every class of
square-zero surjections of local rings, granted step (II) of Stacks 04AM.

Smoothness at the point gives an open subspace of the source containing it on which the
morphism is smooth, hence formally smooth; the spectrum of a local ring whose closed point
lies over the given point factors through that open subspace, so the lifting problem is a
lifting problem for the restricted morphism. -/
theorem liftsAt_of_isSmoothAt (hdescent : FormallySmoothEtaleDescent.{u})
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X)
    (hsm : IsSmoothAt B S hS f x)
    (extension : ∀ ⦃R' R : CommRingCat.{u}⦄, (R' ⟶ R) → Prop)
    (hextension : ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R),
      extension φ → InfinitesimalLifting.IsSquareZeroSurjection φ) :
    LiftsAt B S hS f x extension := by
  obtain ⟨U, hU, x', hx', hsmU⟩ := hsm
  have hformal : FormallySmooth (U.ι ≫ f) :=
    formallySmooth_of_isSmooth B S hS hdescent hU.1 hY (U.ι ≫ f) hsmU
  intro R' R φ hφ T T' i e e' hi hRloc p hp α β hpx hcomm
  have := hRloc
  obtain ⟨αU, hαU⟩ := factorsThrough_of_spec_isLocalRing B S hS hX U hU T R e α p hp x hpx
    ⟨x', hx'⟩
  obtain ⟨γU, hγU⟩ := liftsAt_of_formallySmooth B S hS (U.ι ≫ f)
    (pointsMap B S hS (yoneda.obj T) αU (p.class B S hS (yoneda.obj T))) hformal
    extension hextension φ hφ T T' i e e' hi p hp αU β rfl
    (by rw [← Category.assoc, hαU]; exact hcomm)
  refine ⟨γU ≫ U.ι, ?_, ?_⟩
  · calc
      (yoneda.map i ≫ γU) ≫ U.ι = αU ≫ U.ι := by rw [hγU.1]
      _ = α := hαU
  · simpa only [Category.assoc] using hγU.2

/-! ### From the lifting condition to smoothness -/

/-- The lifting property at a point transports to a commuting square of étale charts over the
morphism: a lifting problem for the morphism of charts is pushed into the source space along
its chart, solved there, and pulled back to the source chart, which is formally étale; the
pullback agrees with the given section of the target chart because that chart is formally
étale too. -/
private theorem liftsAt_chartMap
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X)
    (extension : ∀ ⦃R' R : CommRingCat.{u}⦄, (R' ⟶ R) → Prop)
    (H : LiftsAt B S hS f x extension)
    {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    {R' R : CommRingCat.{u}} (φ : R' ⟶ R) (hφ : extension φ)
    (hsq : InfinitesimalLifting.IsSquareZeroSurjection φ)
    (T T' : BigFppfOver B S hS) (i : T ⟶ T')
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R')
    (hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv)
    [IsLocalRing R] (pT : FieldValuedPoint B S hS (yoneda.obj T))
    (hpT : schemePoint B S hS T pT = e.inv (IsLocalRing.closedPoint R))
    (α : yoneda.obj T ⟶ yoneda.obj U) (β : yoneda.obj T' ⟶ yoneda.obj V)
    (hcenter : pointsMap B S hS (yoneda.obj T) (α ≫ a)
      (pT.class B S hS (yoneda.obj T)) = x)
    (hαβ : α ≫ yoneda.map h = yoneda.map i ≫ β) :
    ∃ γ : yoneda.obj T' ⟶ yoneda.obj U,
      yoneda.map i ≫ γ = α ∧ γ ≫ yoneda.map h = β := by
  have hsite : IsSquareZeroClosedImmersion B S hS i :=
    isSquareZeroClosedImmersion_of_specMap B S hS φ hsq.2.2.1 hsq.2.2.2 T T' i e e' hi
  have hsolid : (α ≫ a) ≫ f = yoneda.map i ≫ (β ≫ b) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc, hαβ, Category.assoc]
  obtain ⟨γX, hγX⟩ := H φ hφ T T' i e e' hi pT hpT (α ≫ a) (β ≫ b) hcenter hsolid
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.hom
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := IsAffine.of_isIso e'.hom
  have haFormal : FormallyEtale a := formallyEtale_of_etale B S hS a ha
  have hbFormal : FormallyEtale b := formallyEtale_of_etale B S hS b hb
  obtain ⟨z, hz, -⟩ := haFormal T T' ‹_› ‹_› i hsite (yonedaEquiv α) (yonedaEquiv γX)
    ((app_yonedaEquiv_eq_map_iff B S hS a i α γX).mpr hγX.1.symm)
  obtain ⟨γ, rfl⟩ := yonedaEquiv.surjective z
  obtain ⟨hγα, hγa⟩ := (isLift_yonedaEquiv_iff B S hS a i α γX γ).mp hz
  obtain ⟨zb, -, huniq⟩ := hbFormal T T' ‹_› ‹_› i hsite
    (yonedaEquiv (α ≫ yoneda.map h)) (yonedaEquiv (β ≫ b))
    ((app_yonedaEquiv_eq_map_iff B S hS b i (α ≫ yoneda.map h) (β ≫ b)).mpr
      (by rw [hαβ, Category.assoc]))
  have hcandidate := (isLift_yonedaEquiv_iff B S hS b i (α ≫ yoneda.map h) (β ≫ b)
    (γ ≫ yoneda.map h)).mpr
    ⟨by rw [← Category.assoc, hγα], by
      rw [Category.assoc, hcomm, ← Category.assoc, hγa]; exact hγX.2⟩
  have hβlift := (isLift_yonedaEquiv_iff B S hS b i (α ≫ yoneda.map h) (β ≫ b) β).mpr
    ⟨hαβ.symm, rfl⟩
  exact ⟨γ, hγα, yonedaEquiv.injective ((huniq _ hcandidate).trans (huniq _ hβlift).symm)⟩

/-- A morphism of algebraic spaces over `S` which is locally of finite type and whose target
has an étale-local Noetherian atlas admits, at every point of its source, a pointed étale
chart whose target chart is locally Noetherian and whose morphism of charts is locally of
finite type. -/
private theorem exists_etaleChartAtPoint_isLocallyNoetherian
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hFiniteType : IsLocallyOfFiniteType B S hS f) :
    ∃ c : EtaleChartAtPoint B S hS f x,
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj c.V) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) := by
  obtain ⟨V, b, hbSurj, hbEtale, hVnoeth⟩ := hNoeth
  obtain ⟨U, a, h, hcomm, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  obtain ⟨y, hy⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj x
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  refine ⟨{ U := U, V := V, a := a, b := b, h := h
            a_etale := haEtale, b_etale := hbEtale, comm := hcomm.symm
            representative := q, point := IsLocalRing.closedPoint q.carrier
            maps_to := hy }, hVnoeth, ?_⟩
  exact hFiniteType U V a b h haEtale hbEtale hcomm.symm

/-- The lifting property at a point against small extensions makes the morphism of charts of a
pointed étale chart lift against residually trivial small extensions at the chart point.

The two test rings are Artinian local with residue field identified with the residue field of
the source chart at the chart point, so their spectra lie in the site and present a lifting
problem for the chart, which `AlgebraicGeometry.Space.liftsAt_chartMap` solves. -/
private theorem liftsAgainstResiduallyTrivialSmallExtension_chartMap
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X)
    (H : LiftsAt B S hS f x fun ⦃_ _⦄ φ => InfinitesimalLifting.IsSmallExtension φ)
    (c : EtaleChartAtPoint B S hS f x) :
    InfinitesimalLifting.LiftsAgainstResiduallyTrivialSmallExtension
      ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) := by
  let U := c.U
  let u := c.sourcePoint B S hS
  let chartX := (BigFppfOver.toScheme B S hS).obj U
  let k := chartX.residueField u
  intro R' R φ hφ _ α β hcomm hclosed hresIso
  obtain ⟨hR', hR, hArtR', hArtR, hsurj, hlen⟩ := hφ
  let : IsLocalRing R' := hR'
  let : IsLocalRing R := hR
  let : IsArtinianRing R' := hArtR'
  let : IsArtinianRing R := hArtR
  have hsmall : InfinitesimalLifting.IsSmallExtension φ :=
    ⟨hR', hR, hArtR', hArtR, hsurj, hlen⟩
  let cp : Spec R := IsLocalRing.closedPoint R
  have hK : (Spec (.of k)).size < B.cutoff := B.residueField_spec_contains U.left.property u
  let αres : CommRingCat.of k ⟶ CommRingCat.of ((Spec R).residueField cp) :=
    (chartX.residueFieldCongr hclosed.symm).hom ≫ α.residueFieldMap cp
  have hαresIso : IsIso αres := by
    let : IsIso (chartX.residueFieldCongr hclosed.symm).hom :=
      (chartX.residueFieldCongr hclosed.symm).isIso_hom
    let : IsIso (α.residueFieldMap cp) := hresIso
    infer_instance
  let eAlpha : k ≃+* (Spec R).residueField cp := (asIso αres).commRingCatIsoToRingEquiv
  let eR : IsLocalRing.ResidueField R ≃+* k :=
    (AlgebraicGeometry.residueFieldAtClosedPointEquiv (R := R)).symm.trans eAlpha.symm
  have hRsite : B.Contains (Spec R) :=
    contains_spec_of_isArtinianRing_of_residueFieldEquiv B hK eR
  let eR' : IsLocalRing.ResidueField R' ≃+* k :=
    (residueFieldEquivOfSurjective φ hsurj).trans eR
  have hR'site : B.Contains (Spec R') :=
    contains_spec_of_isArtinianRing_of_residueFieldEquiv B hK eR'
  let T₀ : B.Schemes := B.obj hRsite
  let T'₀ : B.Schemes := B.obj hR'site
  let tU : T₀ ⟶ U.left := B.inclusion.preimage α
  let tV : T'₀ ⟶ c.V.left := B.inclusion.preimage β
  let T : BigFppfOver B S hS := Over.mk (tU ≫ U.hom)
  let T' : BigFppfOver B S hS := Over.mk (tV ≫ c.V.hom)
  let i₀ : T₀ ⟶ T'₀ := B.inclusion.preimage (Spec.map φ)
  have hiBase : i₀ ≫ tV ≫ c.V.hom = tU ≫ U.hom := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, i₀, tU, tV, B.inclusion.map_preimage]
    change Spec.map φ ≫ β ≫ B.inclusion.map c.V.hom = α ≫ B.inclusion.map U.hom
    have hcbase : (BigFppfOver.toScheme B S hS).map c.h ≫ B.inclusion.map c.V.hom =
        B.inclusion.map U.hom := by
      change B.inclusion.map c.h.left ≫ B.inclusion.map c.V.hom = B.inclusion.map U.hom
      rw [← B.inclusion.map_comp, c.h.w]
    calc
      Spec.map φ ≫ β ≫ B.inclusion.map c.V.hom =
          α ≫ (BigFppfOver.toScheme B S hS).map c.h ≫ B.inclusion.map c.V.hom := by
            simpa only [Category.assoc] using
              congrArg (fun g => g ≫ B.inclusion.map c.V.hom) hcomm.symm
      _ = α ≫ B.inclusion.map U.hom := congrArg (fun g => α ≫ g) hcbase
  let i : T ⟶ T' := Over.homMk i₀ hiBase
  let aT : T ⟶ U := Over.homMk tU (by simp [T, tU])
  let bT' : T' ⟶ c.V := Over.homMk tV (by simp [T', tV])
  have hsiteSq : aT ≫ c.h = i ≫ bT' := by
    apply Over.OverMorphism.ext
    change tU ≫ c.h.left = i₀ ≫ tV
    apply B.inclusion.map_injective
    change B.inclusion.map tU ≫ B.inclusion.map c.h.left =
      B.inclusion.map i₀ ≫ B.inclusion.map tV
    simp only [tU, tV, i₀, B.inclusion.map_preimage]
    exact hcomm
  have hαβ : yoneda.map aT ≫ yoneda.map c.h = yoneda.map i ≫ yoneda.map bT' := by
    simpa only [Functor.map_comp] using congrArg yoneda.map hsiteSq
  let e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R := Iso.refl _
  let e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R' := Iso.refl _
  have hi' : (BigFppfOver.toScheme B S hS).map i = Spec.map φ := by
    change B.inclusion.map i₀ = Spec.map φ
    exact B.inclusion.map_preimage _
  have hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ Spec.map φ ≫ e'.inv := by
    rw [hi']
    change Spec.map φ = 𝟙 (Spec R) ≫ Spec.map φ ≫ 𝟙 (Spec R')
    simp
  have haT : (BigFppfOver.toScheme B S hS).map aT = α := by
    change B.inclusion.map tU = α
    exact B.inclusion.map_preimage (show B.inclusion.obj T₀ ⟶ B.inclusion.obj U.left from α)
  have hbT' : (BigFppfOver.toScheme B S hS).map bT' = β := by
    change B.inclusion.map tV = β
    exact B.inclusion.map_preimage
      (show B.inclusion.obj T'₀ ⟶ B.inclusion.obj c.V.left from β)
  let j : Spec (.of k) ⟶ Spec R :=
    Spec.map (asIso αres).inv ≫ (Spec R).fromSpecResidueField cp
  let k₀ : B.Schemes := B.obj hK
  let v : k₀ ⟶ T₀ := B.inclusion.preimage j
  let P : BigFppfOver B S hS := Over.mk (v ≫ T.hom)
  let vT : P ⟶ T := Over.homMk v (by simp [P])
  let p : FieldValuedPoint B S hS (yoneda.obj T) :=
    { carrier := k, contained := hK, toBase := B.inclusion.map P.hom, value := vT }
  let : Ring.KrullDimLE 0 R := (isArtinianRing_iff_krullDimLE_zero (R := R)).mp hArtR
  let _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum R
  have hp : schemePoint B S hS T p = e.inv cp := Subsingleton.elim _ _
  have hcenter : pointsMap B S hS (yoneda.obj T) (yoneda.map aT ≫ c.a)
      (p.class B S hS (yoneda.obj T)) = x := by
    have hmapPointAux : schemePoint B S hS U
        (FieldValuedPoint.map B S hS (yoneda.obj T) (yoneda.map aT) p) = u :=
      calc
        _ = (BigFppfOver.toScheme B S hS).map aT (schemePoint B S hS T p) :=
          schemePoint_map_yoneda B S hS aT p
        _ = α cp := by rw [hp]; exact congrArg (fun g => g cp) haT
        _ = u := hclosed
    have hmapPoint : (BigFppfOver.toScheme B S hS).map
        (FieldValuedPoint.map B S hS (yoneda.obj T) (yoneda.map aT) p).value
        (IsLocalRing.closedPoint
          (FieldValuedPoint.map B S hS (yoneda.obj T) (yoneda.map aT) p).carrier) = u :=
      hmapPointAux
    have hclass := schemePointRepresentative_class B S hS U
      (FieldValuedPoint.map B S hS (yoneda.obj T) (yoneda.map aT) p)
    rw [hmapPoint] at hclass
    have hrepclass : (schemePointRepresentative B S hS U u).class B S hS (yoneda.obj U) =
        c.representative.class B S hS (yoneda.obj U) := by
      have hpField : c.point = IsLocalRing.closedPoint c.representative.carrier :=
        Subsingleton.elim _ _
      have hu : u = schemePoint B S hS U c.representative :=
        congrArg (fun z => (BigFppfOver.toScheme B S hS).map c.representative.value z) hpField
      rw [hu]
      exact schemePointRepresentative_class B S hS U c.representative
    rw [pointsMap_comp_apply, pointsMap_class, ← hclass, hrepclass]
    exact c.maps_to
  obtain ⟨γ, hγ₁, hγ₂⟩ := liftsAt_chartMap B S hS f x
    (fun ⦃_ _⦄ φ => InfinitesimalLifting.IsSmallExtension φ) H
    c.a c.b c.h c.a_etale c.b_etale c.comm φ hsmall
    (InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hsmall) T T' i e e' hi p hp
    (yoneda.map aT) (yoneda.map bT') hcenter hαβ
  let γsite : T' ⟶ U := yonedaEquiv γ
  have hγsite : yoneda.map γsite = γ := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map]
  refine ⟨(BigFppfOver.toScheme B S hS).map γsite, ?_, ?_⟩
  · have hs : i ≫ γsite = aT := by
      apply yoneda.map_injective
      rw [Functor.map_comp, hγsite]
      exact hγ₁
    rw [← hi', ← Functor.map_comp, hs, haT]
  · have hs : γsite ≫ c.h = bT' := by
      apply yoneda.map_injective
      rw [Functor.map_comp, hγsite]
      exact hγ₂
    rw [← Functor.map_comp, hs, hbT']

/-- **Stacks 0APN, (3) implies (1).** A morphism of algebraic spaces over `S` which is locally
of finite type, whose target is locally Noetherian, and which has the lifting property at a
point of its source against small extensions, is smooth at that point.

A pointed étale chart at the point with locally Noetherian target chart receives every lifting
problem for its morphism of charts along a residually trivial small extension, so Stacks 02HX
makes that morphism of charts smooth at the chart point; smoothness at a point being an
étale-local property of germs, Stacks 04NC reads that back as smoothness of the morphism at the
point. -/
@[stacks 0APN "condition (3) implies condition (1)"]
theorem isSmoothAt_of_liftsAt_isSmallExtension
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hFiniteType : IsLocallyOfFiniteType B S hS f)
    (hlift : LiftsAt B S hS f x fun ⦃_ _⦄ φ => InfinitesimalLifting.IsSmallExtension φ) :
    IsSmoothAt B S hS f x := by
  obtain ⟨c, hVnoeth, hft⟩ :=
    exists_etaleChartAtPoint_isLocallyNoetherian B S hS hX hY f x hNoeth hFiniteType
  let _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj c.V) := hVnoeth
  let _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) := hft
  have hchart : InfinitesimalLifting.SmoothAt ((BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS) :=
    ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness
      ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)).out 4 1).mp
      (liftsAgainstResiduallyTrivialSmallExtension_chartMap B S hS f x hlift c)
  rw [isSmoothAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX hY f x,
    holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _
      (MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget
        (@Smooth.{u} : MorphismProperty Scheme.{u}) Smooth.isEtaleLocalOnSourceAndTarget) f x c]
  exact (smoothAt_iff_hasRepresentativeWithProperty
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)).mp hchart

/-! ### The criterion -/

end AlgebraicGeometry.Space

end
