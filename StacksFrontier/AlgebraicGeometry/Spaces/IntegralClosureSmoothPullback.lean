module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# The integral closure of the structure sheaf commutes with smooth pullback

Let `f : Y ⟶ X` be a smooth morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras on the small
étale site of `X`, and let `A' ⊆ A` be the integral closure of `𝒪_X` in `A`.  Stacks 082E
asserts that the integral closure of `𝒪_Y` in `f^*A` is `f^*A'`.

This file proves that, as an isomorphism `f^*A' ≅ (f^*A)'` of algebra sheaves on `Y` compatible
with the two inclusions into `f^*A`.  The pullback is the extension of scalars
`AlgebraicGeometry.Space.algebraPullback`, the integral closure is
`AlgebraicGeometry.Space.AlgebraSheaf.integralClosureSheaf` (Stacks 0821), and the argument is
the source's: the assertion is local on `Y`, the affine chart diagrams over `f` are cover-dense,
and over such a diagram it is the affine statement that integral closure commutes with smooth
base change, Stacks 03GG.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineTensorPresentation` is the assertion that over every diagram
  of affine étale charts over `f` the sections of an algebra pullback are the base change of the
  sections of the algebra, naturally in a morphism of algebra sheaves.  It is the one input the
  library does not supply; see the implementation notes.

## Main results

* `Stacks.injective_and_range_eq_integralClosure_of_tensor`: Stacks 03GG read through two tensor
  presentations — a map agreeing with the base change of an inclusion whose image is an integral
  closure is injective with image the integral closure.
* `AlgebraicGeometry.Space.AlgebraSheaf.exists_iso_of_locally_range_eq`: two subalgebras of an
  algebra sheaf whose sections agree locally on the small étale site are isomorphic over it.
* `AlgebraicGeometry.Space.algebraPullback_integralClosure_affine_range`: over a diagram of
  affine étale charts over a smooth `f`, the sections of `f^*A'` are the integral closure of the
  chart ring of `Y` in the sections of `f^*A`.

## Implementation notes

**The shape of the conclusion.**  The source says the two subalgebras of `f^*A` are *equal*.
`f^*A'` is not literally a subobject of `f^*A` — it is a pushout of sheaves of rings, and that
the canonical map `f^*A' ⟶ f^*A` is a monomorphism is part of what has to be proved — so the
equality is stated as an isomorphism `f^*A' ≅ (f^*A)'` whose composite with the inclusion of
`(f^*A)'` is the pullback of the inclusion of `A'`.  Two subobjects of `f^*A` are equal exactly
when such an isomorphism exists, so nothing is weakened; the monomorphy of `f^*A' ⟶ f^*A` is a
consequence and is recorded along the way.

**What is assumed, and why.**  Two hypotheses beyond quasi-coherence of `A` are carried
explicitly, and both are the single missing input Stacks 03GA for *algebras*: the library proves
03GA for modules, and only in the special cases of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackQuasicoherence.lean`.

* `HasAffineTensorPresentation`, the identification `(f^*A)(U) = 𝒪_Y(U) ⊗_{𝒪_X(V)} A(V)` over a
  diagram of affine étale charts.  This is Descent, Proposition 03DX(2) read across `f`, the
  algebra counterpart of `AlgebraicGeometry.Space.IsCartesianOnAffineChartDiagrams`, which
  `StacksFrontier/AlgebraicGeometry/Spaces/FittingIdealPullback.lean` carries as a hypothesis for
  exactly the same reason.  It is asked for naturally in a morphism `A' ⟶ A`, because the
  assertion compares the inclusions and not only the two algebras.
* quasi-coherence of `f^*A`, which is what lets Stacks 0820 identify the sections of `(f^*A)'`
  over an affine chart of `Y`.

Everything else is available.  The affine statement is Stacks 03GG, reached through
`Stacks.isIntegral_iff_mem_range_lTensor`: the elements of `𝒪_Y(U) ⊗_{𝒪_X(V)} A(V)` integral
over `𝒪_Y(U)` are the base change of the elements of `A(V)` integral over `𝒪_X(V)`.  The
sections of `A'` and of `(f^*A)'` over an affine chart are Stacks 0820,
`AlgebraicGeometry.Space.AlgebraSheaf.range_integralClosureInclusion_app_eq_integralClosure'`;
and the cover-density of the affine chart diagrams is
`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`.

**Gluing the local statement.**  A morphism of sheaves of commutative rings which is injective
on the sections over the members of a covering of every object is a monomorphism, by
`CategoryTheory.Sheaf.mono_of_isLocallyInjective`; and if two monomorphisms into a common sheaf
have the same image on the members of a covering of every object, the first projection of their
fibre product is locally bijective, hence invertible.  That is
`Stacks.Sites.isIso_pullback_fst_of_locally_range_subset`, and it is what turns the chartwise
computation into the isomorphism of algebra sheaves.

## References

* [Stacks Project, Tag 082E](https://stacks.math.columbia.edu/tag/082E)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 03GG](https://stacks.math.columbia.edu/tag/03GG)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace Stacks.Sites

/-- A monomorphism of sheaves of commutative rings is injective on the sections over every
object: it is a monomorphism of presheaves, hence objectwise, and a monomorphism of commutative
rings is injective. -/
theorem injective_app_of_mono {C : Type*} [Category C] (J : GrothendieckTopology C)
    {F G : Sheaf J CommRingCat.{u}} (φ : F ⟶ G) [Mono φ] (U : Cᵒᵖ) :
    Function.Injective (φ.hom.app U).hom := by
  have : Mono φ.hom := (sheafToPresheaf J CommRingCat.{u}).map_mono φ
  have : Mono (φ.hom.app U) := (NatTrans.mono_iff_mono_app _).mp inferInstance U
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (φ.hom.app U)

/-- A morphism of sheaves of commutative rings which is injective on the sections over the
members of a covering of every object is a monomorphism: it is locally injective, and a locally
injective morphism of sheaves is a monomorphism. -/
theorem mono_of_locallyInjective_app {C : Type*} [Category C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget CommRingCat.{u})] {F G : Sheaf J CommRingCat.{u}} (i : F ⟶ G)
    (hi : ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f → Function.Injective (i.hom.app (op V)).hom) :
    Mono i := by
  have hlocal : Sheaf.IsLocallyInjective i := by
    constructor
    intro U x y hxy
    obtain ⟨R, hR, hi⟩ := hi U.unop
    apply J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hR
    intro V f hf
    apply hi V f hf
    have hx := ConcreteCategory.congr_hom (i.hom.naturality f.op) x
    have hy := ConcreteCategory.congr_hom (i.hom.naturality f.op) y
    exact hx.trans ((congrArg (G.obj.map f.op) hxy).trans hy.symm)
  exact Sheaf.mono_of_isLocallyInjective i

/-- If the image of `i` is contained in the image of a monomorphism `j` on the sections over the
members of a covering of every object, then the first projection of the fibre product of `i` and
`j` is an isomorphism.

It is injective because it is a monomorphism, and locally surjective because a section of `F`
which locally lifts along `j` locally lifts to the fibre product; a locally bijective morphism of
sheaves is an isomorphism. -/
theorem isIso_pullback_fst_of_locally_range_subset {C : Type*} [Category C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{u})]
    {F G H : Sheaf J CommRingCat.{u}} (i : F ⟶ H) (j : G ⟶ H) [Mono j]
    (hr : ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f →
        Set.range (i.hom.app (op V)).hom ⊆ Set.range (j.hom.app (op V)).hom) :
    IsIso (pullback.fst i j) := by
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  refine ⟨Presheaf.isLocallyInjective_of_injective J _
    (injective_app_of_mono J (pullback.fst i j)), ?_⟩
  constructor
  intro U x
  obtain ⟨R, hR, hr⟩ := hr U
  apply J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hR
  intro V f hf
  have hp := (IsPullback.of_hasPullback i j).map (sheafToPresheaf J CommRingCat.{u})
  have he := hp.map ((CategoryTheory.evaluation Cᵒᵖ CommRingCat.{u}).obj (op V))
  have h := (Types.isPullback_iff _ _ _ _).mp (he.map (forget CommRingCat.{u}))
  obtain ⟨y, hy⟩ := hr V f hf (Set.mem_range_self (F.obj.map f.op x))
  obtain ⟨z, hz, _⟩ := h.2.2 (F.obj.map f.op x) y hy.symm
  exact ⟨z, hz⟩

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Smoothness of the chart rings of an affine chart diagram -/

/-- **The chart ring of the source of an affine chart diagram over a smooth morphism is a smooth
algebra over the chart ring of its target.**  The vertical scheme morphism of a chart diagram
over `f` is smooth when `f` is, and a smooth morphism of affine schemes is a smooth ring map on
global sections. -/
theorem smooth_chartDiagramRestrict (f : Y ⟶ X) (hf : IsSmooth B S hS f.hom)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    (chartDiagramRestrict B S hS f d).Smooth := by
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y.1).obj d.U)) := hU
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X.1).obj d.V)) := hV
  have hg : Smooth ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf _ _ _ _ d.g d.U.property d.V.property d.comm.symm
  exact HasRingHomProperty.appTop (P := @Smooth) ((BigFppfOver.toScheme B S hS).map d.g) hg

/-- The chart ring of the source of an affine chart diagram over a smooth morphism, as a smooth
algebra over the chart ring of its target. -/
theorem smooth_chartDiagramAlgebra (f : Y ⟶ X) (hf : IsSmooth B S hS f.hom)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    Algebra.Smooth (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U) :=
  (smooth_chartDiagramRestrict B S hS f hf d hU hV).toAlgebra

/-! ### Integral closure under a smooth base change, through two presentations -/

end AlgebraicGeometry.Space

namespace Stacks

/-- **Integral closure under a smooth base change, read through two presentations.**  Let `T` be
a smooth `R`-algebra, let `i : A' ⟶ A` be an injective `R`-algebra map whose image is the integral
closure of `R` in `A`, and present `T ⊗[R] A'` and `T ⊗[R] A` as `C'` and `C`.  A `T`-algebra map
`j : C' ⟶ C` agreeing with the base change of `i` on the elements `1 ⊗ a'` is injective with
image the integral closure of `T` in `C`.

This is Stacks 03GG in the form the chartwise computation needs: `A'` and `C'` are the sections
of the integral closure over a chart, and `j` is the restriction of the pullback of the
inclusion. -/
theorem injective_and_range_eq_integralClosure_of_tensor {R T A A' C C' : Type*}
    [CommRing R] [CommRing T] [CommRing A] [CommRing A'] [CommRing C] [CommRing C']
    [Algebra R T] [Algebra R A] [Algebra R A'] [Algebra T C] [Algebra T C']
    [Algebra.Smooth R T] (i : A' →ₐ[R] A) (hi : Function.Injective i)
    (hr : Set.range i = (integralClosure R A : Set A))
    (eA' : TensorProduct R T A' ≃ₐ[T] C') (eA : TensorProduct R T A ≃ₐ[T] C)
    (j : C' →ₐ[T] C) (hj : ∀ a' : A', j (eA' (1 ⊗ₜ[R] a')) = eA (1 ⊗ₜ[R] i a')) :
    Function.Injective j ∧ Set.range j = (integralClosure T C : Set C) := by
  have hι : ∀ x : A, IsIntegral R x ↔ x ∈ LinearMap.range i.toLinearMap := by
    intro x
    refine ⟨fun h => ?_, fun ⟨y, hy⟩ => ?_⟩
    · have hx : x ∈ Set.range i := by
        rw [hr]
        exact (mem_integralClosure_iff R A).2 h
      exact ⟨hx.choose, hx.choose_spec⟩
    · have hx : x ∈ (integralClosure R A : Set A) := by
        rw [← hr]
        exact ⟨y, hy⟩
      exact (mem_integralClosure_iff R A).1 hx
  have hcomp : ∀ z : TensorProduct R T A',
      j (eA' z) = eA (LinearMap.lTensor T i.toLinearMap z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul t a' =>
      rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, tmul_eq_smul_one_tmul t,
        tmul_eq_smul_one_tmul t]
      simp only [map_smul, hj a']
  have hlt : Function.Injective (LinearMap.lTensor T i.toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap i.toLinearMap hi
  refine ⟨fun x y hxy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := eA'.surjective x
    obtain ⟨y, rfl⟩ := eA'.surjective y
    exact congrArg eA' (hlt (eA.injective ((hcomp x).symm.trans (hxy.trans (hcomp y)))))
  · refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro c ⟨c', rfl⟩
      obtain ⟨w, rfl⟩ := eA'.surjective c'
      rw [SetLike.mem_coe, mem_integralClosure_iff, hcomp w]
      simpa using
        ((isIntegral_iff_mem_range_lTensor i.toLinearMap hι _).2 ⟨w, rfl⟩).map eA.toAlgHom
    · intro c hc
      obtain ⟨z, rfl⟩ := eA.surjective c
      have hz : IsIntegral T z := by
        simpa using ((mem_integralClosure_iff T C).1 hc).map eA.symm.toAlgHom
      obtain ⟨w, hw⟩ := (isIntegral_iff_mem_range_lTensor i.toLinearMap hι z).1 hz
      exact ⟨eA' w, (hcomp w).trans (congrArg eA hw)⟩

end Stacks

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B S hS}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### Comparing two subalgebras of an algebra sheaf -/

/-- An isomorphism of the underlying sheaves of rings commuting with two morphisms into a common
algebra sheaf, the second a monomorphism, is an isomorphism of algebra sheaves over it.

The structure-algebra maps are carried along because the monomorphism is injective on the
sections over each chart and both triangles commute. -/
theorem exists_iso_of_right_iso {A C H : AlgebraSheaf.{u, u} B S hS F hF}
    (i : A ⟶ H) (j : C ⟶ H) [Mono j.right] (e : A.right ≅ C.right)
    (he : e.hom ≫ j.right = i.right) : ∃ e' : A ≅ C, e'.hom ≫ j = i := by
  have hj (U : (SmallEtale B S hS F)ᵒᵖ) :
      Function.Injective ((j.right.hom.app U).hom) :=
    Stacks.Sites.injective_app_of_mono _ j.right _
  have ecomm (U : (SmallEtale B S hS F)ᵒᵖ)
      (r : (structureSheaf B S hS F hF).obj.obj U) :
      (e.hom.hom.app U).hom (A.algebraMap U r) = C.algebraMap U r := by
    refine hj U ?_
    have hcomp := congrArg
      (fun q : A.right ⟶ H.right => (q.hom.app U).hom (A.algebraMap U r)) he
    have hcomp' : (j.right.hom.app U).hom ((e.hom.hom.app U).hom (A.algebraMap U r)) =
        H.algebraMap U r := by simpa using hcomp.trans (i.comm U r)
    exact hcomp'.trans (j.comm U r).symm
  have einvcomm (U : (SmallEtale B S hS F)ᵒᵖ)
      (r : (structureSheaf B S hS F hF).obj.obj U) :
      (e.inv.hom.app U).hom (C.algebraMap U r) = A.algebraMap U r := by
    have hbij : Function.Bijective ((e.hom.hom.app U).hom) :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    refine hbij.1 ?_
    have hleft : (e.hom.hom.app U).hom ((e.inv.hom.app U).hom (C.algebraMap U r)) =
        C.algebraMap U r :=
      congrArg (fun q : C.right ⟶ C.right => (q.hom.app U).hom (C.algebraMap U r))
        e.inv_hom_id
    exact hleft.trans (ecomm U r).symm
  refine ⟨⟨⟨e.hom, ecomm⟩, ⟨e.inv, einvcomm⟩, Hom.ext e.hom_inv_id, Hom.ext e.inv_hom_id⟩, ?_⟩
  exact Hom.ext he

/-- **Two subalgebras of an algebra sheaf with the same sections locally are isomorphic over
it.**  If `i` and `j` are monomorphisms of the underlying sheaves of rings with the same image
on the sections over the members of a covering of every chart, then their sources are isomorphic
as algebra sheaves over the common target.

Both projections of the fibre product of `i` and `j` are isomorphisms, by
`Stacks.Sites.isIso_pullback_fst_of_locally_range_subset` applied in both directions, so the
composite of one with the inverse of the other is the required isomorphism. -/
theorem exists_iso_of_locally_range_eq {A C H : AlgebraSheaf.{u, u} B S hS F hF}
    (i : A ⟶ H) (j : C ⟶ H) [Mono i.right] [Mono j.right]
    (hr : ∀ U : SmallEtale B S hS F, ∃ R : Presieve U,
      Sieve.generate R ∈ SmallEtale.topology B S hS F U ∧
        ∀ (V : SmallEtale B S hS F) (g : V ⟶ U), R g →
          Set.range ((i.right.hom.app (op V)).hom) =
            Set.range ((j.right.hom.app (op V)).hom)) :
    ∃ e : A ≅ C, e.hom ≫ j = i := by
  choose R hR hrange using hr
  have hfst : IsIso (pullback.fst i.right j.right) :=
    Stacks.Sites.isIso_pullback_fst_of_locally_range_subset _ i.right j.right fun U =>
      ⟨R U, hR U, fun V g hg => (hrange U V g hg).le⟩
  have hsnd : IsIso (pullback.snd i.right j.right) := by
    have := Stacks.Sites.isIso_pullback_fst_of_locally_range_subset
      (SmallEtale.topology B S hS F) j.right i.right fun U =>
        ⟨R U, hR U, fun V g hg => (hrange U V g hg).symm.le⟩
    rw [← pullbackSymmetry_hom_comp_fst]
    infer_instance
  refine exists_iso_of_right_iso i j
    ((asIso (pullback.fst i.right j.right)).symm ≪≫ asIso (pullback.snd i.right j.right)) ?_
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/-- The map on sections over a chart induced by a morphism of algebra sheaves, as a morphism of
algebras over the chart ring. -/
private noncomputable def sectionsAlgHom {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C)
    (U : SmallEtale B S hS F) :
    letI := chartSectionsAlgebra A U
    letI := chartSectionsAlgebra C U
    A.right.obj.obj (op U) →ₐ[chartRing B S hS F hF U] C.right.obj.obj (op U) :=
  letI := chartSectionsAlgebra A U
  letI := chartSectionsAlgebra C U
  { __ := (φ.right.hom.app (op U)).hom
    commutes' := φ.comm (op U) }

end AlgebraSheaf

/-! ### The affine-chart tensor presentation of an algebra pullback -/

variable (B S hS) {X Y : AlgebraicSpaces B S hS}

/-- **The affine-chart tensor presentation of the algebra pullback along `f`.**  Over every
diagram of affine étale charts over `f`, the sections of `f^*A` over the chart of `Y` are the
base change `𝒪_Y(U) ⊗_{𝒪_X(V)} A(V)` of the sections of `A` over the chart of `X`, compatibly
with a morphism of algebra sheaves on `X`.

This is Descent, Proposition 03DX(2) read across `f`, the algebra counterpart of
`AlgebraicGeometry.Space.IsCartesianOnAffineChartDiagrams`; it is Stacks 03GA for algebras, which
this library does not prove, and it is therefore carried as a hypothesis. -/
def HasAffineTensorPresentation (f : Y ⟶ X) : Prop :=
  ∀ {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A ⟶ C)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom),
    IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
    IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      letI := chartDiagramAlgebra B S hS f d
      letI := chartSectionsAlgebra A d.V
      letI := chartSectionsAlgebra C d.V
      letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
      letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj C) d.U
      ∃ (eA : TensorProduct (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
                (A.right.obj.obj (op d.V)) ≃ₐ[chartRing B S hS Y.1 Y.2 d.U]
              ((algebraPullback B S hS f).obj A).right.obj.obj (op d.U))
        (eC : TensorProduct (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
                (C.right.obj.obj (op d.V)) ≃ₐ[chartRing B S hS Y.1 Y.2 d.U]
              ((algebraPullback B S hS f).obj C).right.obj.obj (op d.U)),
        ∀ a, (((algebraPullback B S hS f).map φ).right.hom.app (op d.U)).hom (eA (1 ⊗ₜ a)) =
          eC (1 ⊗ₜ ((φ.right.hom.app (op d.V)).hom a))

/-! ### The sections of the pulled-back integral closure over an affine chart diagram -/

/-- **Over a diagram of affine étale charts over a smooth morphism, the pullback of the
integral-closure inclusion is injective with image the integral closure.**  The chart ring of
`Y` is a smooth algebra over the chart ring of `X`, the sections of `A'` over the chart of `X`
are the integral closure there by Stacks 0820, and the two tensor presentations turn Stacks 03GG
into the assertion over the chart of `Y`. -/
theorem algebraPullback_integralClosure_affine_range (f : Y ⟶ X)
    (hf : IsSmooth B S hS f.hom) (hpres : HasAffineTensorPresentation B S hS f)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    Function.Injective ((((algebraPullback B S hS f).map
          (AlgebraSheaf.integralClosureInclusion A)).right.hom.app (op d.U)).hom) ∧
      Set.range ((((algebraPullback B S hS f).map
          (AlgebraSheaf.integralClosureInclusion A)).right.hom.app (op d.U)).hom) =
        (integralClosure (chartRing B S hS Y.1 Y.2 d.U)
          (((algebraPullback B S hS f).obj A).right.obj.obj (op d.U)) : Set _) := by
  let _ := chartDiagramAlgebra B S hS f d
  let _ := chartSectionsAlgebra A d.V
  let _ := chartSectionsAlgebra (AlgebraSheaf.integralClosureSheaf A) d.V
  let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  let _ := chartSectionsAlgebra
    ((algebraPullback B S hS f).obj (AlgebraSheaf.integralClosureSheaf A)) d.U
  have _ := smooth_chartDiagramAlgebra B S hS f hf d hU hV
  obtain ⟨eD, eA, he⟩ := hpres (AlgebraSheaf.integralClosureInclusion A) d hU hV
  have _ := AlgebraSheaf.mono_integralClosureInclusion_right A
  have hr : Set.range (AlgebraSheaf.sectionsAlgHom (AlgebraSheaf.integralClosureInclusion A) d.V) =
      (integralClosure (chartRing B S hS X.1 X.2 d.V) (A.right.obj.obj (op d.V)) : Set _) :=
    AlgebraSheaf.range_integralClosureInclusion_app_eq_integralClosure' A hA d.V hV
  exact Stacks.injective_and_range_eq_integralClosure_of_tensor
    (AlgebraSheaf.sectionsAlgHom (AlgebraSheaf.integralClosureInclusion A) d.V)
    (Stacks.Sites.injective_app_of_mono _ (AlgebraSheaf.integralClosureInclusion A).right _)
    hr eD eA (AlgebraSheaf.sectionsAlgHom
      ((algebraPullback B S hS f).map (AlgebraSheaf.integralClosureInclusion A)) d.U) he

end AlgebraicGeometry.Space
