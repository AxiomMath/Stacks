module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealOrderIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# The defining ideal sheaf of a closed subspace is cartesian on affine charts

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `Z` be a
closed subspace of `X`.  Stacks 03MB asserts that `Z ↦ 𝓘_Z` is an inclusion-reversing bijection
between the closed subspaces of `X` and the **quasi-coherent** sheaves of ideals of `𝒪_X` on the
small étale site of `X`.  `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealOrderIso.lean` assembles that statement
from two hypotheses, `hq` (the defining ideal sheaf is quasi-coherent) and `hr` (every
quasi-coherent sheaf of ideals is a defining ideal sheaf).

**This file discharges `hq` outright**, in the following sense.  What is proved here is that
`𝓘_Z` is *cartesian on affine charts* — the base change criterion
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, Stacks 03DX(2) read as a condition — with no
hypothesis at all, and the implication from that criterion to quasi-coherence on the small étale
site is the unconditional
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.  Composing the two
gives `hq` unconditionally; that composite is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf` of
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent`, which is where the
assembly of Stacks 03MB now lives, because it is that file and not this one which imports the
implication.  No separate statement about the direct image `i_*𝒪_Z` is needed, and in particular
the 03MB sibling clause "`i_*𝒪_Z` is quasi-coherent" is *not* used.

The reason the cartesian condition is reachable unconditionally is that the defining ideal is
computed, by `AlgebraicGeometry.Space.definingIdealAt_eq_ker`, as the kernel of an
honest map of rings of global sections of *schemes*,

`Γ(U) ⟶ Γ(Z ×_X U)`,

and over affine charts the whole comparison becomes commutative algebra:

* `Z ×_X U` is affine, because `Z ×_X U ⟶ U` is a closed immersion and `U` is affine;
* `Γ(Z ×_X V)` is `Γ(V) ⊗_{Γ(U)} Γ(Z ×_X U)`, because `Z ×_X V` is the fibre product of
  `Z ×_X U ⟶ U` and `V ⟶ U` and `Γ` turns a fibre product of affine schemes into a tensor
  product (Mathlib's `AlgebraicGeometry.isPushout_appTop_of_isPullback`);
* `Γ(U) ⟶ Γ(V)` is flat, which is
  `AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine`.

With those three `AlgebraicGeometry.Space.bijective_baseChange_of_exact` carries the
base change comparison from `𝒪_X` and `Γ(Z ×_X -)` to their kernel, which is `𝓘_Z`.

## Main definitions

* `AlgebraicGeometry.Space.subspaceInclusion` is the inclusion of a closed subspace, read as a
  morphism of algebraic spaces.  It is an abbreviation for the term `ObjectProperty.homMk Z.1.ι`
  that the statements of Stacks 03MB write out by hand.

## Main results

* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_unit`: **the structure sheaf is cartesian on
  affine charts**, with no hypothesis — indeed the base change comparison for `𝒪_X` is bijective
  over *every* morphism of étale charts, which is
  `AlgebraicGeometry.Space.bijective_sectionsBaseChange_unit`.
* `AlgebraicGeometry.Space.representablePullback_isPullback` and
  `AlgebraicGeometry.Space.isPushout_appTop_representablePullback`: the base change of a chart
  along a representable morphism of algebraic spaces is a fibre product of schemes, and between
  affine charts its ring of global functions is the pushout.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_kerSubmodule_of_isPushout`: the base
  change comparison of a sheaf submodule of `𝒪_X` which is chartwise the kernel of a map of
  rings is bijective, given flatness and the pushout square for those rings.
* `AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`: **the defining ideal
  sheaf of a closed subspace is cartesian on affine charts.**  Unconditional.  This is the last
  declaration of the file and the one everything above it serves.

## Implementation notes

No `@[stacks 03MB]` attribute is claimed: cartesianity on affine charts is one input to the tag
and not a clause of it, and the assembly of the tag is elsewhere.  This is the convention of the
sibling files `AlgebraicGeometry.Spaces.ChartSectionsKernel` and
`AlgebraicGeometry.Spaces.ShortExactQuasicoherent`.

Two declarations that used to close this file have been removed, both superseded by
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent`, which imports this one.
`definingIdealSheaf_isQuasicoherentOnSite` carried the two-way bridge `h03DX` of Descent 03DX(2)
as a hypothesis and used only its direction "cartesian ⟹ quasi-coherent", which is now the proved
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`; its hypothesis-free
form is `AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`.
`closedSubspaceIdealOrderIso_of_isCartesian` carried that bridge together with a surjectivity
hypothesis `hsurj`; both are now discharged except for the forward implication of
Descent 03DX(2), and the assembly asking only for that is
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_h03DX`.

The module universe is the universe `u` of the schemes and is not free; the reason is the one
recorded in `AlgebraicGeometry.Spaces.ShortExactQuasicoherent`, that
`SheafOfModules.unit` of a `RingCat.{u}`-valued sheaf of rings has its sections in `Type u`.

`AlgebraicGeometry.Space.bijective_sectionsBaseChange_kerSubmodule_of_isPushout` takes the two
rings `P`, `Q` and the three ring maps between them as *data*, rather than reading them off the
geometry, so that the elaborator never has to unify the large scheme-level terms inside the
proof; the geometric instantiation is
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_definingIdealSheaf`, which supplies them
and discharges the pushout hypothesis from
`AlgebraicGeometry.Space.isPushout_appTop_representablePullback`.

`AlgebraicGeometry.Space.representablePullback_isPullback` is stated for the explicit lift
`hf.lift (hf.fst V.1.hom) (hf.snd V.1.hom ≫ k.hom.left) _` rather than for
`(AlgebraicGeometry.Space.smallBaseChange B S hS f hf).map k`, which is that lift: the field
`((smallBaseChange B S hS f hf).obj V).1.left` of the latter does not reduce to
`hf.pullback V.1.hom` at instance transparency, and the pullback square cannot be stated at all
through it.

The `Algebra` and `IsScalarTower` structures of the four rings depend on the chart morphism and
so cannot be instances; they are introduced by `let`/`have` inside the proofs, as in
`AlgebraicGeometry.Spaces.ChartSections`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two base change comparisons of commutative algebra -/

/-- `LinearMap.liftBaseChange` is bijective once it agrees on pure tensors with a bijective
additive equivalence. -/
private theorem bijective_liftBaseChange_of_addEquiv {R A P Q : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q] [Module A Q]
    [IsScalarTower R A Q] (φ : P →ₗ[R] Q) (e : TensorProduct R A P ≃+ Q)
    (he : ∀ a x, e (a ⊗ₜ x) = a • φ x) : Function.Bijective (LinearMap.liftBaseChange A φ) := by
  have hfun : (⇑(LinearMap.liftBaseChange A φ) : TensorProduct R A P → Q) = ⇑e := by
    refine funext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | tmul a x => rw [LinearMap.liftBaseChange_tmul, he]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  rw [hfun]
  exact e.bijective

/-- The base change comparison `A ⊗_R R ⟶ A` of the free module of rank one is bijective: it is
the canonical isomorphism `CategoryTheory.TensorProduct.rid`, because a linear map `R ⟶ A` which
is the structure map sends `r` to `r · 1`. -/
theorem bijective_liftBaseChange_of_eq_algebraMap {R : Type*} [CommRing R] {A : Type*}
    [CommRing A] [Algebra R A] (φ : R →ₗ[R] A) (hφ : ∀ r, φ r = algebraMap R A r) :
    Function.Bijective (LinearMap.liftBaseChange A φ) := by
  refine bijective_liftBaseChange_of_addEquiv φ (TensorProduct.rid R A).toAddEquiv fun a r => ?_
  change TensorProduct.rid R A (a ⊗ₜ r) = _
  rw [TensorProduct.rid_tmul, hφ, Algebra.smul_def, mul_comm, smul_eq_mul]

/-- **A pushout square of commutative rings is a base change.** If the square of structure maps
of `R ⟶ A`, `R ⟶ P`, `A ⟶ Q`, `P ⟶ Q` is a pushout in `CommRingCat`, then the base change
comparison `A ⊗_R P ⟶ Q` is bijective.

This is `CommRingCat.isPushout_iff_isPushout` read through `Algebra.IsPushout.equiv`; the linear
map is given as data with its identification with the structure map, because the comparison the
application needs is a `LinearMap.liftBaseChange`. -/
theorem bijective_liftBaseChange_of_isPushout {R A P Q : Type u} [CommRing R] [CommRing A]
    [CommRing P] [CommRing Q] [Algebra R A] [Algebra R P] [Algebra A Q] [Algebra P Q]
    [Algebra R Q] [IsScalarTower R A Q] [IsScalarTower R P Q]
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R P)) (CommRingCat.ofHom (algebraMap A Q))
      (CommRingCat.ofHom (algebraMap P Q)))
    (ψ : P →ₗ[R] Q) (hψ : ∀ x, ψ x = algebraMap P Q x) :
    Function.Bijective (LinearMap.liftBaseChange A ψ) := by
  have hpo : Algebra.IsPushout R A P Q := CommRingCat.isPushout_iff_isPushout.1 H
  refine bijective_liftBaseChange_of_addEquiv ψ (Algebra.IsPushout.equiv R A P Q).toAddEquiv
    fun b x => ?_
  change Algebra.IsPushout.equiv R A P Q (b ⊗ₜ x) = _
  rw [Algebra.IsPushout.equiv_tmul, hψ, Algebra.smul_def]

/-! ### The structure sheaf is cartesian on affine charts -/

variable {B S hS}

/-- **The base change comparison of the structure sheaf is bijective over every morphism of étale
charts**, affine or not: the sections of `𝒪_F` over a chart are the free module of rank one on the
regular functions there, and `𝒪_F(V) ⊗_{𝒪_F(U)} 𝒪_F(U) = 𝒪_F(V)`. -/
theorem bijective_sectionsBaseChange_unit {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    Function.Bijective (sectionsBaseChange (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) f) := by
  let _ := chartAlgebra (hF := hF) f
  exact bijective_liftBaseChange_of_eq_algebraMap
    (R := chartRing B S hS F hF U) (A := chartRing B S hS F hF V) _ (fun _ => rfl)

/-- **The structure sheaf of an algebraic space is cartesian on affine charts.**  This is the
base case of the criterion of Stacks 03DX(2), and it is unconditional. -/
theorem isCartesianOnAffineCharts_unit {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} :
    IsCartesianOnAffineCharts (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) :=
  fun _ _ _ _ f => bijective_sectionsBaseChange_unit f

variable (B S hS)

/-! ### Base change of an étale chart along a representable morphism -/

/-- The inclusion of a closed subspace of an algebraic space, as a morphism of algebraic
spaces. -/
noncomputable abbrev subspaceInclusion (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X :=
  ObjectProperty.homMk Z.1.ι

/-- **Stacks 03G2, part (4), as a fibre product over the chart.** For a representable morphism
`f : X ⟶ Y` of algebraic spaces and a morphism `k : V ⟶ W` of étale charts of `Y`, the square
formed by the base-changed charts `X ×_Y V ⟶ X ×_Y W` and the cartesian projections is a fibre
product.

The square is obtained from the two representability squares of `W` and of `V` by cancelling the
one for `W` on the right; the comparison morphism is the lift which
`AlgebraicGeometry.Space.smallBaseChange` uses on morphisms. -/
theorem representablePullback_isPullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    IsPullback
      (yoneda.map (hf.lift (hf.fst V.1.hom) (hf.snd V.1.hom ≫ k.hom.left)
        (representablePullback_lift_cond B S hS f hf k)))
      (yoneda.map (hf.snd V.1.hom)) (yoneda.map (hf.snd W.1.hom)) (yoneda.map k.hom.left) := by
  refine IsPullback.of_right (h₁₂ := hf.fst W.1.hom) (h₂₂ := W.1.hom) ?_ ?_
    (hf.isPullback W.1.hom)
  · rw [hf.lift_fst, CostructuredArrow.w k.hom]
    exact hf.isPullback V.1.hom
  · rw [← yoneda.map_comp, ← yoneda.map_comp]
    exact congrArg yoneda.map (hf.lift_snd _ _ _)

/-- **Global functions on the base change of an affine chart are the tensor product.** For a
representable `f : X ⟶ Y` and a morphism `k : V ⟶ W` of étale charts of `Y` with `V`, `W` and
`X ×_Y W` affine, the square of rings of global functions of the fibre product square of
`AlgebraicGeometry.Space.representablePullback_isPullback` is a pushout in `CommRingCat`.

This is Mathlib's `AlgebraicGeometry.isPushout_appTop_of_isPullback`, the statement that `Γ`
turns a fibre product of affine schemes into a tensor product of rings, applied to the fibre
product square after passage to schemes. -/
theorem isPushout_appTop_representablePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W)
    (hXW : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback W.1.hom)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left)) :
    IsPushout ((BigFppfOver.toScheme B S hS).map (hf.snd W.1.hom)).appTop
      ((BigFppfOver.toScheme B S hS).map k.hom.left).appTop
      ((BigFppfOver.toScheme B S hS).map (hf.lift (hf.fst V.1.hom)
        (hf.snd V.1.hom ≫ k.hom.left) (representablePullback_lift_cond B S hS f hf k))).appTop
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop :=
  isPushout_appTop_of_isPullback
    ((IsPullback.of_map_of_faithful yoneda
      (representablePullback_isPullback B S hS f hf k)).map (BigFppfOver.toScheme B S hS))

/-- The base change of a closed subspace to an affine étale chart is an affine scheme: its
projection to the chart is a closed immersion. -/
theorem isAffine_representablePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (W : SmallEtale B S hS Y.1)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.snd W.1.hom)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback W.1.hom)) :=
  isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hf.snd W.1.hom))

/-! ### A chartwise kernel ideal sheaf is cartesian where the rings form a pushout -/

variable {B S hS}

/-- **The base change comparison of a chartwise kernel is bijective.** Let `N` be a sheaf
submodule of `𝒪_F` whose sections over the étale charts `U` and `V` are the kernels of ring maps
`p_U : 𝒪_F(U) ⟶ P` and `p_V : 𝒪_F(V) ⟶ Q`, compatibly with a ring map `q : P ⟶ Q` over
restriction `𝒪_F(U) ⟶ 𝒪_F(V)`.  If that restriction is flat and the four rings form a pushout
square, then the base change comparison for `N` over `f : V ⟶ U` is bijective.

The proof is `AlgebraicGeometry.Space.bijective_baseChange_of_exact` applied to the
two exact sequences `0 ⟶ N(U) ⟶ 𝒪_F(U) ⟶ P` and `0 ⟶ N(V) ⟶ 𝒪_F(V) ⟶ Q`, whose comparison maps
at the middle terms are bijective by
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_unit` and at the right-hand terms by
`AlgebraicGeometry.Space.bijective_liftBaseChange_of_isPushout`. -/
theorem bijective_sectionsBaseChange_kerSubmodule_of_isPushout
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (N : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) {P Q : Type u} [CommRing P] [CommRing Q]
    (pU : chartRing B S hS F hF U →+* P) (pV : chartRing B S hS F hF V →+* Q) (q : P →+* Q)
    (hsq : q.comp pU = pV.comp (chartRestrict (hF := hF) f))
    (hNU : ∀ a : chartRing B S hS F hF U, a ∈ N.obj (op U) ↔ pU a = 0)
    (hNV : ∀ a : chartRing B S hS F hF V, a ∈ N.obj (op V) ↔ pV a = 0)
    (hflat : RingHom.Flat (chartRestrict (hF := hF) f))
    (hpo : IsPushout (CommRingCat.ofHom (chartRestrict (hF := hF) f))
      (CommRingCat.ofHom pU) (CommRingCat.ofHom pV) (CommRingCat.ofHom q)) :
    Function.Bijective (sectionsBaseChange N.toSheafOfModules f) := by
  let _algA : Algebra (chartRing B S hS F hF U) (chartRing B S hS F hF V) :=
    chartAlgebra (hF := hF) f
  let _algP : Algebra (chartRing B S hS F hF U) P := pU.toAlgebra
  let _algQ : Algebra (chartRing B S hS F hF V) Q := pV.toAlgebra
  let _algPQ : Algebra P Q := q.toAlgebra
  let _algRQ : Algebra (chartRing B S hS F hF U) Q :=
    (pV.comp (chartRestrict (hF := hF) f)).toAlgebra
  have _tower₁ : IsScalarTower (chartRing B S hS F hF U) (chartRing B S hS F hF V) Q :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _tower₂ : IsScalarTower (chartRing B S hS F hF U) P Q :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hsq r).symm
  have _flat : Module.Flat (chartRing B S hS F hF U) (chartRing B S hS F hF V) := hflat
  have hcG' := bijective_liftBaseChange_of_isPushout (R := chartRing B S hS F hF U)
    (A := chartRing B S hS F hF V) (P := P) (Q := Q) hpo
    (IsScalarTower.toAlgHom (chartRing B S hS F hF U) P Q).toLinearMap (fun _ => rfl)
  let φU := Algebra.linearMap (chartRing B S hS F hF U) P
  let φV := Algebra.linearMap (chartRing B S hS F hF V) Q
  let cG := sectionsBaseChange (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) f
  have hex : ∀ (W : SmallEtale B S hS F) (T : Type u) [CommRing T]
      [Algebra (chartRing B S hS F hF W) T],
      (∀ a : chartRing B S hS F hF W, a ∈ N.obj (op W) ↔ algebraMap _ T a = 0) →
      Function.Exact ((N.ι.val.app (op W)).hom) (Algebra.linearMap (chartRing B S hS F hF W) T) :=
    fun W T _ _ hN b =>
      ⟨fun hb => ⟨⟨b, (hN b).2 hb⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact (hN _).1 a.2⟩
  have hsqG : ∀ z : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (chartRing B S hS F hF U), φV (cG z) =
        LinearMap.liftBaseChange (chartRing B S hS F hF V)
          (IsScalarTower.toAlgHom (chartRing B S hS F hF U) P Q).toLinearMap
          (LinearMap.lTensor (chartRing B S hS F hF V) φU z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
        have hx : q (pU x) = pV (chartRestrict (hF := hF) f x) := RingHom.congr_fun hsq x
        rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, Algebra.smul_def]
        change pV (b * chartRestrict (hF := hF) f x) = pV b * q (pU x)
        rw [hx]
        exact map_mul pV b _
    | add z w hz hw =>
        rw [map_add, map_add]
        exact (congrArg φV (map_add cG z w)).trans
          ((map_add φV _ _).trans (congrArg₂ (· + ·) hz hw))
  exact bijective_baseChange_of_exact (ιU := (N.ι.val.app (op U)).hom) (φU := φU)
    (ιV := (N.ι.val.app (op V)).hom) (φV := φV)
    (cK := sectionsBaseChange N.toSheafOfModules f) (cG := cG)
    (fun _ _ h => Subtype.ext h) (hex U P hNU) (fun _ _ h => Subtype.ext h) (hex V Q hNV)
    (app_sectionsBaseChange N.ι f) hsqG
    (bijective_sectionsBaseChange_unit f) hcG'

variable (B S hS)

/-! ### The defining ideal sheaf of a closed subspace -/

/-- **The base change comparison of the defining ideal sheaf of a closed subspace is bijective
over a morphism of affine étale charts.**

The defining ideal of `Z` at a chart `U` is the kernel of `Γ(U) ⟶ Γ(Z ×_X U)`, by
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`; over affine charts the base changes of `Z` are
affine and their rings of global functions form a pushout square, so
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_kerSubmodule_of_isPushout` applies. -/
theorem bijective_sectionsBaseChange_definingIdealSheaf (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    Function.Bijective (sectionsBaseChange
      (definingIdealSheaf B S hS X Z).toSheafOfModules f) := by
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hV
  have hZUaff : IsAffine
      ((BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback U.1.hom)) :=
    isAffine_representablePullback B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep U
      (Z.2.2.property_snd U.1.hom) hUaff
  have hmem : ∀ (W : SmallEtale B S hS X.1) (a : chartRing B S hS X.1 X.2 W), a ∈
      (definingIdealSheaf B S hS X Z).obj (op W) ↔ _ := fun W a =>
    (Iff.of_eq (congrArg (fun I => a ∈ I) (definingIdealAt_eq_ker B S hS X Z W))).trans
      RingHom.mem_ker
  refine bijective_sectionsBaseChange_kerSubmodule_of_isPushout _ f
    (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).appTop.hom)
    (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).appTop.hom)
    (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.lift (Z.2.2.rep.fst V.1.hom)
      (Z.2.2.rep.snd V.1.hom ≫ f.hom.left)
      (representablePullback_lift_cond B S hS
        (subspaceInclusion B S hS X Z) Z.2.2.rep f))).appTop.hom)
    ?_ ?_ ?_ (flat_chartRestrict_of_isAffine f hU hV) ?_
  · have hcomm : ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).appTop ≫
          ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.lift (Z.2.2.rep.fst V.1.hom)
            (Z.2.2.rep.snd V.1.hom ≫ f.hom.left)
            (representablePullback_lift_cond B S hS
              (subspaceInclusion B S hS X Z) Z.2.2.rep f))).appTop =
        ((BigFppfOver.toScheme B S hS).map f.hom.left).appTop ≫
          ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).appTop := by
      have h := congrArg (fun m : Z.2.2.rep.pullback V.1.hom ⟶ U.1.left =>
          ((BigFppfOver.toScheme B S hS).map m).appTop) (Z.2.2.rep.lift_snd _ _
        (representablePullback_lift_cond B S hS
          (subspaceInclusion B S hS X Z) Z.2.2.rep f))
      simpa only [Functor.map_comp, Scheme.Hom.comp_appTop] using h
    exact RingHom.ext fun x => ConcreteCategory.congr_hom hcomm x
  · exact hmem U
  · exact hmem V
  · exact (isPushout_appTop_representablePullback B S hS
      (subspaceInclusion B S hS X Z) Z.2.2.rep f hZUaff hVaff hUaff).flip

/-- **The defining ideal sheaf of a closed subspace is cartesian on affine charts.**  This is the
base change criterion of Stacks 03DX(2) for `𝓘_Z`, and it is unconditional: it needs no
comparison between quasi-coherence on the small étale site and quasi-coherence on a chart, only
the computation of `𝓘_Z` as a kernel of global functions, flatness of the restriction maps
between affine charts, and the fibre product of affine schemes. -/
theorem definingIdealSheaf_isCartesianOnAffineCharts (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    IsCartesianOnAffineCharts (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  fun _ _ hU hV f => bijective_sectionsBaseChange_definingIdealSheaf B S hS X Z f hU hV

end AlgebraicGeometry.Space

end
