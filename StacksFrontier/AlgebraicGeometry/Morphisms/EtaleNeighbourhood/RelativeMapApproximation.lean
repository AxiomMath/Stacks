module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FiberMaximalIdeal
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteTypeBaseApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksFrontier.RingTheory.GRing.Criteria
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.EssFiniteType
import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
import StacksFrontier.AlgebraicGeometry.SpecLimitOfIndSmooth
import StacksFrontier.RingTheory.Smoothing.ApproximationGRingEtale
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tags 0GDX and 0CB1: approximating an isomorphism of completed local rings by a morphism

Tag 0GDX approximates an isomorphism `φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y_σ, y_σ}` of `𝒪_{S, s}`-algebras,
where `Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` is the base change of `Y ⟶ T` along the morphism
attached to a local homomorphism `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`, by a diagram of elementary étale
neighbourhoods: an elementary étale neighbourhood `(V, v)` of `(S, s)` with a morphism
`τ : V ⟶ T` carrying `v` to `t`, and an elementary étale neighbourhood `(W, w)` of `(X, x)`
which is simultaneously one of `(Y ×_{T, τ} V, y_τ)`.

The proof runs as follows. Flatness of the completion makes `𝒪^∧_{X_σ, x_σ}` the completion of
`𝒪^∧_{X, x}` for the point `x_σ` of `X ×_S Spec 𝒪^∧_{S, s}` above `x` and the closed point, so
`φ` becomes an isomorphism of completed local rings of two schemes locally of finite type over
`Spec 𝒪^∧_{S, s}`; Tag 0CAV turns it into a single pointed scheme `(U, u)` which is an
elementary étale neighbourhood of both. Popescu's theorem presents `Spec 𝒪^∧_{S, s}` as a
cofiltered inverse limit of affine schemes smooth over an affine open of `S`; an affine open of
`U` and its two étale morphisms descend to a finite stage `D` of that presentation by Tags 01ZM
and 07RP. Finally the first stage of Tag 0CAW replaces `D` by an elementary étale neighbourhood
`(V, v)` of `(S, s)` over it, and `(W, w)` is the base change of the stage along `V ⟶ D`.

The source cuts the stage down to a closed subscheme étale over `S` using the étale slice of Tag
057G. That is not needed: étaleness is stable under base change, so all the construction asks of
`V` is a morphism `V ⟶ D` over `S` through the image of the closed point which is an isomorphism
on residue fields there, and the first stage of Tag 0CAW supplies one — together with the
congruence modulo `𝔪_v ^ N` which the slice does not. Dropping the slice costs one lemma: the
source identifies a point of a fibre product by injectivity of a base change of an immersion,
and with `V ⟶ D` no longer an immersion that step is instead
`AlgebraicGeometry.Scheme.Pullback.point_eq_of_isIso_residueFieldMap`, the uniqueness
counterpart of `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

## Main definitions

* `StacksDraft.ArtinApproximation.specCompletedStalk`, `specCompletedStalkPoint` and
  `specCompletedStalkTo`: the scheme `Spec 𝒪^∧_{S, s}`, its closed point, and its canonical
  morphism to `S`.
* `StacksDraft.ArtinApproximation.relativeBaseChangeMorphism`: the morphism
  `Spec 𝒪^∧_{S, s} ⟶ T` attached to `σ`, whose base change of `Y ⟶ T` is `Y_σ`.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.point_eq_of_isIso_residueFieldMap`: a point of `X ×_S Y`
  over `y` is determined by its image in `X` when `g` is an isomorphism on residue fields
  at `y`.
* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_over_stage`: the first
  stage of Tag 0CAW over a morphism `m : Spec 𝒪^∧_{S, s} ⟶ W` over `S`, giving an elementary
  étale neighbourhood `(V, v)` of `(S, s)` with a morphism `ι : V ⟶ W` over `S` carrying `v` to
  the image of the closed point, an isomorphism on residue fields there, and the congruence
  modulo `𝔪_v ^ N`.
* `StacksDraft.ArtinApproximation.exists_point_and_closedFiberIso_over_stage`: the closed-fibre
  identification `(Y_σ)_s ≅ (Y ×_T V)_v` of Tag 0GDX and the point `y_τ` of `Y ×_T V`
  corresponding to `y_σ` under it.
* `StacksDraft.ArtinApproximation.exists_common_elementaryEtaleNeighborhood_absoluteApproximation`:
  Tag 0GDX.
* `StacksDraft.ArtinApproximation.exists_etale_relativeIsomorphismApproximation`: the diagram
  of Tag 0CB1 for an isomorphism of completions `𝒪^∧_{X, x} ≅ 𝒪^∧_{Y_σ, y_σ}`, the
  same construction run in the setting of Tag 0CAW — where `T` comes with a morphism to `S`
  locally of finite type and `σ` is a map of `𝒪_{S, s}`-algebras — and packaged as the diagram
  of Tag 0CAW with `f : W ⟶ X ×_S V` étale.

## Implementation notes

*Which hypotheses are carried.* None. Theorem 07QZ, which the library's Tag 0CAU behind both Tag
0CAV and the first stage of Tag 0CAW states as the named hypothesis
`StacksDraft.ArtinApproximation.LocalApproximationProperty`, is discharged here with
`StacksDraft.ArtinApproximation.localApproximationProperty`. The source's "`T` of finite type
over `Spec ℤ`" is weakened to "locally of finite type", which is all the construction uses.

*One construction, two bases.* The only place where "`T` is of finite type over `Spec ℤ`"
enters is the factorisation of the morphism `Spec 𝒪^∧_{S, s} ⟶ T` attached to `σ` through a
finite stage of the presentation of `Spec 𝒪^∧_{S, s}`. All that step asks is a scheme `B`
receiving both `S` and `T`, with `T ⟶ B` locally of finite presentation and the morphism
attached to `σ` compatible over `B` with the completion map `Spec 𝒪^∧_{S, s} ⟶ S`. So the
construction is carried out once, in
`StacksDraft.ArtinApproximation.exists_common_elementaryEtaleNeighborhood_over_base`, and the
two tags are the two choices of `B`: terminal for Tag 0GDX, where the compatibility is
automatic, and `B = S` for Tag 0CB1, where it says exactly that `σ` is a map of
`𝒪_{S, s}`-algebras (`relativeBaseChangeMorphism_comp`). The factorisation over `B` also
returns `τ ≫ (T ⟶ B) = (V ⟶ S) ≫ (S ⟶ B)`, which for `B = S` is the statement that the
morphism `τ : V ⟶ T` of Tag 0CAW is a morphism over `S`.

*No isomorphism of completed local rings over the stage.* Clause (5) of Tag 0CAW identifies only
the `𝔪 ^ N`-truncations of `𝒪^∧_{Y_σ, y_σ}` and `𝒪^∧_{Y ×_{T, τ} V, y_τ}`, never the
completions, and no isomorphism of the completions exists in general; the counterexample is
recorded in the module docstring of
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/FiniteTypeBaseApproximation.lean`.
So the coupling of `(V, τ)` to `Y` and `y_σ` is made at finite order: at order one through the
closed fibres, and at order `N` through the isomorphism of `𝔪 ^ N`-truncations which clause (5)
uses.

*How clause (5) is obtained.* The local ring of a fibre product is a localization of the tensor
product of the local rings, so a map out of it is a compatible pair of maps out of the two
factors (`exists_ringHom_stalk_pullback`). Applied to the two base changes of the object `A`
over a smooth stage `D` — one along `m : Spec 𝒪^∧_{S, s} ⟶ D`, the other along `ι : V ⟶ D` —
this turns the congruence of clause (3) over `D` into a map
`𝒪_{A ×_D Spec 𝒪^∧_{S, s}, a_σ} → 𝒪_{A ×_D V, w}/𝔪_w ^ N` compatible with the maps from
`𝒪_{A, a}`: the order-`N` comparison `exists_ringHom_stalk_pullback_comparison`. The congruence
of Tag 0CAV, taken at the order `N` of clause (5) rather than at order one, lives in the
completed local ring of the étale neighbourhood `U` produced upstairs; `U` is that first base
change near its point, which the descent now records, so the congruence transports to
`𝒪_{A ×_D Spec 𝒪^∧_{S, s}, a_σ}` and the comparison carries it to `𝒪_{W, w}/𝔪_w ^ N`.

*The closed-fibre identification.* It is an isomorphism of the scheme-theoretic fibres
`AlgebraicGeometry.Scheme.Hom.fiber`, compatible with the two maps to `Y` and with the two maps
to the residue fields of the bases. It is built from `CategoryTheory.IsPullback.isoIsPullback`
after exhibiting both fibres as pullbacks of `q` along the two maps `Spec κ ⟶ T`, which the
residue field isomorphism identifies; this is why no comparison of `pullback.lift`s appears.

*The shape of the descent.* The comparison of a base change along `β : Z ⟶ T` with one along a
morphism `τ` through which `β` factors is `baseChangeCompare`, whose two projections are the
projections of `pullbackTransitionIso`; working with it rather than with nested `pullback.lift`s
is what keeps the descent computations to rewriting by `Over.pullback_map_left` and
`pullback.lift_fst`.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0CB1](https://stacks.math.columbia.edu/tag/0CB1)
* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
* [Stacks Project, Tag 0CAV](https://stacks.math.columbia.edu/tag/0CAV)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 057G](https://stacks.math.columbia.edu/tag/057G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.Scheme.Pullback

/-- If the residue field of `Y` at `y` is the residue field of `S` below it, then the tensor
product `κ(x) ⊗_{κ(s)} κ(y)` attached to a point of `X ×_S Y` over `y` has a one-point
spectrum. -/
private lemma subsingleton_spec_tensor_ofPoint
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y)
    (hy : IsIso (g.residueFieldMap y))
    (z : (pullback f g : Scheme.{u})) (hz : pullback.snd f g z = y) :
    ∀ p p' : ↥(Spec (Triplet.ofPoint z).tensor), p = p' := by
  set T := Triplet.ofPoint z with hT
  have hTy : T.y = y := hz
  have : IsIso (g.residueFieldMap T.y) := by rwa [hTy]
  have hcongr : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) :=
    IsIso.comp_isIso' (S.residueFieldCongr T.hy).isIso_inv inferInstance
  have hpush : IsPushout
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
      T.tensorInl T.tensorInr := IsPushout.of_hasPushout _ _
  have : IsIso T.tensorInl := hpush.isIso_inl_of_isIso hcongr
  have : IsIso (Spec.map T.tensorInl) := inferInstance
  intro p p'
  exact (Spec.map T.tensorInl).isOpenEmbedding.injective
    (Subsingleton.elim (α := PrimeSpectrum _) _ _)

/-- **Uniqueness of a point of a fibre product above a prescribed pair of points.** If
`g : Y ⟶ S` induces an isomorphism on residue fields at `y`, then a point of `X ×_S Y` lying
over `y` is determined by its image in `X`.

This is the uniqueness counterpart of
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`: in general the points of
`X ×_S Y` above a pair `(x, y)` are the points of `Spec (κ(x) ⊗_{κ(s)} κ(y))`, and the
hypothesis forces that spectrum to be a single point. -/
theorem point_eq_of_isIso_residueFieldMap
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y)
    (hy : IsIso (g.residueFieldMap y))
    (z₁ z₂ : (pullback f g : Scheme.{u}))
    (hfst : pullback.fst f g z₁ = pullback.fst f g z₂)
    (hsnd₁ : pullback.snd f g z₁ = y) (hsnd₂ : pullback.snd f g z₂ = y) :
    z₁ = z₂ := by
  apply carrierEquiv.injective
  apply carrierEquiv_eq_iff.mpr
  refine ⟨Triplet.ext hfst (hsnd₁.trans hsnd₂.symm), ?_⟩
  exact subsingleton_spec_tensor_ofPoint f g y hy z₂ hsnd₂ _ _

end AlgebraicGeometry.Scheme.Pullback

namespace StacksDraft.ArtinApproximation

/-! ### Residue fields along a composite -/

/-- If a composite induces an isomorphism on residue fields, so does its first factor. -/
private lemma isIso_residueFieldMap_of_comp_left
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsIso ((f ≫ g).residueFieldMap x)] :
    IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, fun b => ?_⟩
  have hsurj : Function.Surjective
      ((g.residueFieldMap (f x) ≫ f.residueFieldMap x).hom) := by
    rw [← Scheme.residueFieldMap_comp]
    exact ((ConcreteCategory.isIso_iff_bijective
      ((f ≫ g).residueFieldMap x)).mp inferInstance).surjective
  obtain ⟨a, ha⟩ := hsurj b
  exact ⟨g.residueFieldMap (f x) a, by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using ha⟩

/-- If a composite induces an isomorphism on residue fields, so does its second factor. -/
private lemma isIso_residueFieldMap_of_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsIso ((f ≫ g).residueFieldMap x)] :
    IsIso (g.residueFieldMap (f x)) := by
  have := isIso_residueFieldMap_of_comp_left f g x
  have : IsIso (g.residueFieldMap (f x) ≫ f.residueFieldMap x) := by
    rw [← Scheme.residueFieldMap_comp]
    exact inferInstanceAs (IsIso ((f ≫ g).residueFieldMap x))
  exact IsIso.of_isIso_comp_right _ (f.residueFieldMap x)

/-- Two morphisms into a common target which hit the same point and induce isomorphisms on
residue fields there identify the residue fields of their sources. -/
private lemma exists_residueFieldIso_of_common_point
    {Z V D : Scheme.{u}} (a : Z ⟶ D) (i : V ⟶ D)
    (z : Z) (v : V) (hpoint : a z = i v)
    [IsIso (a.residueFieldMap z)] [IsIso (i.residueFieldMap v)] :
    ∃ e : Z.residueField z ≅ V.residueField v,
      Spec.map e.inv ≫ V.fromSpecResidueField v ≫ i =
        Z.fromSpecResidueField z ≫ a := by
  refine ⟨(asIso (a.residueFieldMap z)).symm ≪≫
    D.residueFieldCongr hpoint ≪≫ asIso (i.residueFieldMap v), ?_⟩
  rw [← i.SpecMap_residueFieldMap_fromSpecResidueField v]
  rw [← a.SpecMap_residueFieldMap_fromSpecResidueField z]
  simp only [Iso.trans_inv, asIso_inv, Scheme.residueFieldCongr_inv, Iso.symm_inv, asIso_hom,
    Category.assoc, ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
  rw [Spec.map_comp, Category.assoc,
    D.residueFieldCongr_fromSpecResidueField hpoint.symm]

/-! ### Comparing the closed fibres of two base changes -/

/-- An isomorphism of residue fields which is compatible with two morphisms out of their
spectra induces an isomorphism of the fibres of the two base changes of a fixed morphism. -/
private lemma exists_fiberIso_of_residueFieldIso
    {Y T B C : Scheme.{u}} (q : Y ⟶ T) (f : B ⟶ T) (g : C ⟶ T)
    (b : B) (c : C) (e : B.residueField b ≅ C.residueField c)
    (h : Spec.map e.inv ≫ C.fromSpecResidueField c ≫ g =
      B.fromSpecResidueField b ≫ f) :
    ∃ E : (pullback.snd q f).fiber b ≅ (pullback.snd q g).fiber c,
      E.hom ≫ (pullback.snd q g).fiberι c ≫ pullback.fst q g =
        (pullback.snd q f).fiberι b ≫ pullback.fst q f ∧
      E.hom ≫ (pullback.snd q g).fiberToSpecResidueField c =
        (pullback.snd q f).fiberToSpecResidueField b ≫ Spec.map e.inv := by
  have h' : Spec.map e.hom ≫ B.fromSpecResidueField b ≫ f =
      C.fromSpecResidueField c ≫ g := by
    rw [← h]
    simp [← Spec.map_comp_assoc]
  -- The fibre of `Y ×_T B ⟶ B` at `b` is the pullback of `q` along `Spec κ(b) ⟶ B ⟶ T`.
  have hA : IsPullback ((pullback.snd q f).fiberι b ≫ pullback.fst q f)
      ((pullback.snd q f).fiberToSpecResidueField b) q
      (B.fromSpecResidueField b ≫ f) :=
    (IsPullback.of_hasPullback (pullback.snd q f) (B.fromSpecResidueField b)).paste_horiz
      (IsPullback.of_hasPullback q f)
  have hB₀ : IsPullback ((pullback.snd q g).fiberι c ≫ pullback.fst q g)
      ((pullback.snd q g).fiberToSpecResidueField c) q
      (C.fromSpecResidueField c ≫ g) :=
    (IsPullback.of_hasPullback (pullback.snd q g) (C.fromSpecResidueField c)).paste_horiz
      (IsPullback.of_hasPullback q g)
  -- The residue field isomorphism makes `Spec κ(c) ⟶ T` and `Spec κ(b) ⟶ T` the same cospan
  -- leg, so the two fibres are pullbacks of one and the same cospan.
  have : IsIso (Spec.map e.hom) := inferInstance
  have hiso : IsPullback (C.fromSpecResidueField c ≫ g) (Spec.map e.hom) (𝟙 T)
      (B.fromSpecResidueField b ≫ f) :=
    (IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using h'⟩).flip
  have hB : IsPullback ((pullback.snd q g).fiberι c ≫ pullback.fst q g)
      ((pullback.snd q g).fiberToSpecResidueField c ≫ Spec.map e.hom) q
      (B.fromSpecResidueField b ≫ f) := by
    simpa only [Category.comp_id] using hB₀.paste_vert hiso
  refine ⟨hA.isoIsPullback _ _ hB, ?_, ?_⟩
  · simpa only [Category.assoc] using hA.isoIsPullback_hom_fst _ _ hB
  · have hsnd := hA.isoIsPullback_hom_snd _ _ hB
    have hinv : Spec.map e.hom ≫ Spec.map e.inv = 𝟙 (Spec (C.residueField c)) := by
      rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id]
    have hres := congrArg (fun m => m ≫ Spec.map e.inv) hsnd
    simp only [Category.assoc, hinv, Category.comp_id] at hres
    exact hres

/-- The isomorphism of fibres of `exists_fiberIso_of_residueFieldIso`, together with the point
of the second base change which corresponds to a given point of the first. -/
private lemma exists_fiberIso_point_of_residueFieldIso
    {Y T B C : Scheme.{u}} (q : Y ⟶ T) (f : B ⟶ T) (g : C ⟶ T)
    (b : B) (c : C) (e : B.residueField b ≅ C.residueField c)
    (h : Spec.map e.inv ≫ C.fromSpecResidueField c ≫ g =
      B.fromSpecResidueField b ≫ f)
    (y : Y) (yB : (pullback q f : Scheme.{u}))
    (hyB : pullback.fst q f yB = y) (hb : pullback.snd q f yB = b) :
    ∃ (yC : (pullback q g : Scheme.{u})), pullback.fst q g yC = y ∧
      ∃ (hc : pullback.snd q g yC = c)
      (E : (pullback.snd q f).fiber b ≅ (pullback.snd q g).fiber c),
      E.hom ≫ (pullback.snd q g).fiberι c ≫ pullback.fst q g =
        (pullback.snd q f).fiberι b ≫ pullback.fst q f ∧
      E.hom ≫ (pullback.snd q g).fiberToSpecResidueField c =
        (pullback.snd q f).fiberToSpecResidueField b ≫ Spec.map e.inv ∧
      E.hom (((pullback.snd q f).fiberHomeo b).symm ⟨yB, hb⟩) =
        ((pullback.snd q g).fiberHomeo c).symm ⟨yC, hc⟩ := by
  obtain ⟨E, hY, hBase⟩ := exists_fiberIso_of_residueFieldIso q f g b c e h
  have hyC : pullback.fst q g ((pullback.snd q g).fiberι c
      (E.hom (((pullback.snd q f).fiberHomeo b).symm ⟨yB, hb⟩))) = y := by
    have heq := congrArg (fun k : (pullback.snd q f).fiber b ⟶ Y => k
      (((pullback.snd q f).fiberHomeo b).symm ⟨yB, hb⟩)) hY
    simpa [Scheme.Hom.comp_apply, hyB] using heq
  have hc : pullback.snd q g ((pullback.snd q g).fiberι c
      (E.hom (((pullback.snd q f).fiberHomeo b).symm ⟨yB, hb⟩))) = c :=
    ((pullback.snd q g).fiberHomeo c _).2
  refine ⟨_, hyC, hc, E, hY, hBase, ?_⟩
  apply ((pullback.snd q g).fiberι c).isEmbedding.injective
  simp only [Scheme.Hom.fiberι_fiberHomeo_symm]

/-! ### The spectrum of the completed local ring -/

/-- `Spec 𝒪^∧_{S, s}`, the spectrum of the completed local ring of `S` at `s`. -/
abbrev specCompletedStalk (S : Scheme.{u}) (s : S) : Scheme.{u} :=
  Spec (CommRingCat.of
    (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))

/-- The closed point of `Spec 𝒪^∧_{S, s}`. -/
abbrev specCompletedStalkPoint (S : Scheme.{u}) [IsLocallyNoetherian S] (s : S) :
    specCompletedStalk S s :=
  closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))

/-- The completion map `𝒪_{S, s} → 𝒪^∧_{S, s}` read as a morphism `Spec 𝒪^∧_{S, s} ⟶ S`. -/
abbrev specCompletedStalkTo (S : Scheme.{u}) (s : S) : specCompletedStalk S s ⟶ S :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
    S.fromSpecStalk s

/-- A local homomorphism out of `𝒪_{X, x}` which is bijective on residue fields stays so when
read as the local homomorphism attached to the associated morphism of schemes. -/
private lemma residueFieldMap_bijective_of_specMap
    {X : Scheme.{u}} (x : X) (R : Type u) [CommRing R] [IsLocalRing R]
    (f : X.presheaf.stalk x →+* R) [IsLocalHom f]
    (hf : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    Function.Bijective (IsLocalRing.ResidueField.map
      (Scheme.stalkClosedPointTo
        (Spec.map (CommRingCat.ofHom f) ≫ X.fromSpecStalk x)).hom) := by
  have h := (SpecToEquivOfLocalRing X (CommRingCat.of R)).right_inv
    ⟨x, ⟨CommRingCat.ofHom f, inferInstance⟩⟩
  have hP := congrArg (fun z : Σ y,
      {g : CommRingCat.of (X.presheaf.stalk y) ⟶ CommRingCat.of R // IsLocalHom g.hom} =>
    let : IsLocalHom z.2.1.hom := z.2.2
    Function.Bijective (IsLocalRing.ResidueField.map z.2.1.hom)) h
  exact hP.mpr hf

/-- The completion map `𝒪_{S, s} → 𝒪^∧_{S, s}` is an isomorphism on residue fields, read as
the morphism `Spec 𝒪^∧_{S, s} ⟶ S`. -/
private lemma isIso_residueFieldMap_specCompletedStalkTo (S : Scheme.{u})
    [IsLocallyNoetherian S] (s : S) :
    IsIso ((specCompletedStalkTo S s).residueFieldMap (specCompletedStalkPoint S s)) := by
  have hbij : Function.Bijective (IsLocalRing.ResidueField.map
      (Scheme.stalkClosedPointTo (specCompletedStalkTo S s)).hom) := by
    simpa using residueFieldMap_bijective_of_specMap s
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
      (AdicCompletion.residueField_map_bijective (S.presheaf.stalk s))
  let eStalk := (stalkClosedPointIso (CommRingCat.of
    (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s)))).commRingCatIsoToRingEquiv
  have : IsLocalRing
      ((specCompletedStalk S s).presheaf.stalk (specCompletedStalkPoint S s)) :=
    eStalk.symm.isLocalRing
  have : IsLocalHom eStalk.toRingHom := ⟨(isLocalHom_equiv eStalk).map_nonunit⟩
  have hResidueMapComp :
      (IsLocalRing.ResidueField.mapEquiv eStalk).toRingHom.comp
        ((specCompletedStalkTo S s).residueFieldMap (specCompletedStalkPoint S s)).hom =
      IsLocalRing.ResidueField.map
        (Scheme.stalkClosedPointTo (specCompletedStalkTo S s)).hom := by
    ext a
    change IsLocalRing.ResidueField.map eStalk.toRingHom
      (IsLocalRing.ResidueField.map
        ((specCompletedStalkTo S s).stalkMap (specCompletedStalkPoint S s)).hom a) = _
    refine (DFunLike.congr_fun (IsLocalRing.ResidueField.map_comp
      ((specCompletedStalkTo S s).stalkMap (specCompletedStalkPoint S s)).hom
      eStalk.toRingHom).symm a).trans ?_
    rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  have hcomp : Function.Bijective (fun a => (IsLocalRing.ResidueField.mapEquiv eStalk)
      (((specCompletedStalkTo S s).residueFieldMap (specCompletedStalkPoint S s)) a)) := by
    change Function.Bijective ((IsLocalRing.ResidueField.mapEquiv eStalk).toRingHom.comp
      ((specCompletedStalkTo S s).residueFieldMap (specCompletedStalkPoint S s)).hom)
    rw [hResidueMapComp]
    exact hbij
  refine ⟨Function.Injective.of_comp hcomp.1, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hcomp.2 (IsLocalRing.ResidueField.mapEquiv eStalk b)
  exact ⟨a, (IsLocalRing.ResidueField.mapEquiv eStalk).injective ha⟩

/-- The morphism `Spec R ⟶ X` attached to a local homomorphism out of `𝒪_{X, x}` carries the
closed point to `x`. -/
private lemma fromSpecStalk_specMap_closedPoint {X : Scheme.{u}} {x : X} {R : Type u}
    [CommRing R] [IsLocalRing R] (σ : X.presheaf.stalk x →+* R) [IsLocalHom σ] :
    (Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecStalk x) (closedPoint R) = x := by
  have : IsLocalHom (CommRingCat.ofHom σ).hom := inferInstanceAs (IsLocalHom σ)
  change (X.fromSpecStalk x) (Spec.map (CommRingCat.ofHom σ) (closedPoint R)) = x
  rw [Spec_closedPoint]
  exact Scheme.fromSpecStalk_closedPoint

/-- A morphism out of `Spec 𝒪^∧_{S, s}` over `S` is an isomorphism on residue fields at the
closed point. -/
private lemma isIso_residueFieldMap_of_comp_specCompletedStalkTo
    {S D : Scheme.{u}} [IsLocallyNoetherian S] {s : S} (ρ : D ⟶ S)
    (m : specCompletedStalk S s ⟶ D) (hm : m ≫ ρ = specCompletedStalkTo S s) :
    IsIso (m.residueFieldMap (specCompletedStalkPoint S s)) := by
  have := isIso_residueFieldMap_specCompletedStalkTo S s
  have : IsIso ((m ≫ ρ).residueFieldMap (specCompletedStalkPoint S s)) := by
    rw [hm]; infer_instance
  exact isIso_residueFieldMap_of_comp_left m ρ _

/-- **The maximal ideal of the local ring of an étale neighbourhood is generated by that of the
base.** The fibres of an étale morphism are disjoint unions of spectra of finite separable field
extensions, so their local rings have vanishing maximal ideal; this is
`AlgebraicGeometry.map_maximalIdeal_eq_of_etale_fibers`, read through the transport along
`AlgebraicGeometry.EtaleNeighborhood.map_point` which `stalkHom` performs. -/
@[ega "IV 18.8.6" "m_μ = m_λ A_μ for λ ≤ μ", sga "1 IX 1.2" "partial", sga "3 XI 1.3" "(ii)"]
private lemma map_maximalIdeal_stalkHom {S : Scheme.{u}} {s : S}
    (V : EtaleNeighborhood S s) :
    Ideal.map V.stalkHom (maximalIdeal (S.presheaf.stalk s)) =
      maximalIdeal (V.scheme.presheaf.stalk V.point) := by
  have hdef : V.stalkHom = (V.toBase.stalkMap V.point).hom.comp
      ((S.presheaf.stalkCongr (.of_eq V.map_point.symm)).hom).hom :=
    CommRingCat.hom_comp _ _
  rw [hdef, ← Ideal.map_map,
    show Ideal.map ((S.presheaf.stalkCongr (.of_eq V.map_point.symm)).hom).hom
        (maximalIdeal (S.presheaf.stalk s)) =
      maximalIdeal (S.presheaf.stalk (V.toBase V.point)) from
      map_maximalIdeal_eq_ringEquiv
        (S.presheaf.stalkCongr (.of_eq V.map_point.symm)).commRingCatIsoToRingEquiv]
  exact map_maximalIdeal_eq_of_etale_fibers V.toBase
    (fun z => by
      change Etale (pullback.snd V.toBase (S.fromSpecResidueField z))
      infer_instance) V.point

/-! ### Replacing a stage of the presentation by an elementary étale neighbourhood -/

/-- **The first stage of Tag 0CAW over a morphism out of `Spec 𝒪^∧_{S, s}`.** Let `S` be
locally Noetherian, let `𝒪_{S, s}` be a G-ring, let `ρ : W ⟶ S` be locally of finite type and
let `m : Spec 𝒪^∧_{S, s} ⟶ W` be a morphism over `S`. Then for every `N ≥ 1` there are an
elementary étale neighbourhood `(V, v)` of `(S, s)` and a morphism `ι : V ⟶ W` over `S`
carrying `v` to the image `w` of the closed point, such that `ι` is an isomorphism on residue
fields at `v` and the square relating the local homomorphism `𝒪_{W, w} → 𝒪^∧_{S, s}` attached
to `m` to `ι^♯_v` commutes modulo `𝔪_v ^ N`.

Applied to a stage `W` of the presentation of `Spec 𝒪^∧_{S, s}` as a limit of schemes smooth
over `S`, this replaces the étale slice of [Stacks Project, Tag 057G] used in the source's
proof of Tag 0GDX: the slice gives a `V` which is a closed subscheme of `W`, whereas this gives
one which is merely a scheme over `W` — enough for the base change which follows, and carrying
in addition the congruence of [Stacks Project, Tag 0CAW]. -/
theorem exists_elementaryEtaleNeighborhood_over_stage
    {S W : Scheme.{u}} [IsLocallyNoetherian S] {s : S}
    (ρ : W ⟶ S) [LocallyOfFiniteType ρ] (m : specCompletedStalk S s ⟶ W)
    (hm : m ≫ ρ = specCompletedStalkTo S s)
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (V : EtaleNeighborhood S s) (ι : V.scheme ⟶ W)
      (hι : ι V.point = m (specCompletedStalkPoint S s)),
      V.IsElementary ∧ ι ≫ ρ = V.toBase ∧
        IsIso (ι.residueFieldMap V.point) ∧
        ∀ a : W.presheaf.stalk (m (specCompletedStalkPoint S s)),
          V.completionMap ((Scheme.stalkClosedPointTo m).hom a) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (ι.stalkHomAt hι a) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N) := by
  have : IsLocalHom (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
  -- The image of the closed point lies over `s`.
  have hpoint : ρ (m (specCompletedStalkPoint S s)) = s := by
    change (m ≫ ρ) (specCompletedStalkPoint S s) = s
    rw [hm]
    exact fromSpecStalk_specMap_closedPoint _
  -- The local homomorphism attached to `m` is an `𝒪_{S, s}`-algebra map for `ρ`.
  have hσbase : (Scheme.stalkClosedPointTo m).hom.comp (ρ.stalkHomAt hpoint) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) :=
    stalkClosedPointTo_comp_stalkHomAt m ρ
      (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) hm hpoint
  obtain ⟨V, hVel, ι, hι, hover, hcong⟩ :=
    exists_elementaryEtaleNeighborhood_baseApproximation ρ
      (m (specCompletedStalkPoint S s)) s hpoint hG N hN
      (Scheme.stalkClosedPointTo m).hom (Scheme.isLocalHom_stalkClosedPointTo m) hσbase
  refine ⟨V, ι, hι, hVel, hover, ?_, hcong⟩
  -- `ι` is an isomorphism on residue fields because `V ⟶ S` is, and `V ⟶ S` factors as
  -- `ι ≫ ρ`.
  have hVres : IsIso (V.toBase.residueFieldMap V.point) := by
    have : IsIso ((S.residueFieldCongr V.map_point).inv ≫
      V.toBase.residueFieldMap V.point) := hVel
    exact IsIso.of_isIso_comp_left (S.residueFieldCongr V.map_point).inv _
  have : IsIso ((ι ≫ ρ).residueFieldMap V.point) := by
    rwa [hover]
  exact isIso_residueFieldMap_of_comp_left ι ρ V.point

/-- **The closed-fibre identification of Tag 0GDX.** Let `ρ : W ⟶ S` and `τ_W : W ⟶ T`, let
`m : Spec 𝒪^∧_{S, s} ⟶ W` be a morphism over `S`, and let `(V, v)` with `ι : V ⟶ W` over `S`
be as produced by `exists_elementaryEtaleNeighborhood_over_stage`. Write `σ = m ≫ τ_W` and
`τ = ι ≫ τ_W`. Then a point `y_σ` of `Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` lying over `y` and
over the closed point determines a point `y_τ` of `Y ×_{T, τ} V` lying over `y` and over `v`,
together with an isomorphism `κ(z) ≅ κ(v)` of the residue fields of the two bases compatible
with their maps to `S` and to `T`, and an isomorphism `(Y_σ)_z ≅ (Y ×_T V)_v` of the closed
fibres compatible with the maps to `Y` and to those residue fields, which carries `y_σ`
to `y_τ`.

This is the source's sentence "let `y_τ ∈ Y ×_T V` correspond to `y_σ` via the identification
`(Y_σ)_s = (Y ×_T V)_v`", and it is what couples the elementary étale neighbourhood of the base
to `Y` and `y_σ`. -/
theorem exists_point_and_closedFiberIso_over_stage
    {S W Y T : Scheme.{u}} [IsLocallyNoetherian S] {s : S}
    (ρ : W ⟶ S) (τW : W ⟶ T) (q : Y ⟶ T)
    (m : specCompletedStalk S s ⟶ W) (hm : m ≫ ρ = specCompletedStalkTo S s)
    (V : EtaleNeighborhood S s) (ι : V.scheme ⟶ W)
    (hι : ι V.point = m (specCompletedStalkPoint S s))
    (hιρ : ι ≫ ρ = V.toBase) (hιres : IsIso (ι.residueFieldMap V.point))
    (y : Y) (yσ : (pullback q (m ≫ τW) : Scheme.{u}))
    (hyσY : pullback.fst q (m ≫ τW) yσ = y)
    (hyσZ : pullback.snd q (m ≫ τW) yσ = specCompletedStalkPoint S s) :
    ∃ (yτ : (pullback q (ι ≫ τW) : Scheme.{u})),
      pullback.fst q (ι ≫ τW) yτ = y ∧
      ∃ (hyτV : pullback.snd q (ι ≫ τW) yτ = V.point)
      (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
        V.scheme.residueField V.point)
      (eFiber : (pullback.snd q (m ≫ τW)).fiber (specCompletedStalkPoint S s) ≅
        (pullback.snd q (ι ≫ τW)).fiber V.point),
      (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
        (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
          specCompletedStalkTo S s) ∧
      (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ (ι ≫ τW) =
        (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
          (m ≫ τW)) ∧
      (eFiber.hom ≫ (pullback.snd q (ι ≫ τW)).fiberι V.point ≫
          pullback.fst q (ι ≫ τW) =
        (pullback.snd q (m ≫ τW)).fiberι (specCompletedStalkPoint S s) ≫
          pullback.fst q (m ≫ τW)) ∧
      (eFiber.hom ≫ (pullback.snd q (ι ≫ τW)).fiberToSpecResidueField V.point =
        (pullback.snd q (m ≫ τW)).fiberToSpecResidueField (specCompletedStalkPoint S s) ≫
          Spec.map eBase.inv) ∧
      (eFiber.hom (((pullback.snd q (m ≫ τW)).fiberHomeo
          (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩) =
        ((pullback.snd q (ι ≫ τW)).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  have := hιres
  have : IsIso (m.residueFieldMap (specCompletedStalkPoint S s)) :=
    isIso_residueFieldMap_of_comp_specCompletedStalkTo ρ m hm
  -- The two bases have the same residue field, compatibly with their maps to `W`.
  obtain ⟨eBase, heBase⟩ := exists_residueFieldIso_of_common_point m ι
    (specCompletedStalkPoint S s) V.point hι.symm
  have heBaseS : Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
      (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
        specCompletedStalkTo S s := by
    rw [← hιρ, ← hm]
    exact (reassoc_of% heBase) ρ
  have heBaseT : Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ (ι ≫ τW) =
      (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
        (m ≫ τW) := (reassoc_of% heBase) τW
  obtain ⟨yτ, hyτY, hyτV, eFiber, h₁, h₂, h₃⟩ :=
    exists_fiberIso_point_of_residueFieldIso q (m ≫ τW) (ι ≫ τW)
      (specCompletedStalkPoint S s) V.point eBase heBaseT y yσ hyσY hyσZ
  exact ⟨yτ, hyτY, hyτV, eBase, eFiber, heBaseS, heBaseT, h₁, h₂, h₃⟩

/-! ### The maximal ideal of the local ring of a base change -/

/-- Let `A` be a local `R`-algebra by a local homomorphism, let `B` be an `R`-algebra in which
every element agrees with one coming from `R` modulo `𝔪_R`, and let `C` be a local localization
of `A ⊗[R] B` whose structure map is local on the left factor. Then the maximal ideal of `C` is
generated by that of `A`. -/
private lemma maximalIdeal_map_of_tensor_localization
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing C]
    [Algebra R A] [Algebra R B] [IsLocalHom (algebraMap R A)]
    (φ : A ⊗[R] B →+* C)
    [IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom)]
    (hB : ∀ b : B, ∃ r : R,
      b - algebraMap R B r ∈ (maximalIdeal R).map (algebraMap R B))
    (M : Submonoid (A ⊗[R] B))
    (hLoc : letI := φ.toAlgebra; IsLocalization M C) :
    (maximalIdeal A).map (φ.comp Algebra.TensorProduct.includeLeftRingHom) =
      maximalIdeal C := by
  let f := φ.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)
  let J := (maximalIdeal A).map f
  have hJ : J ≤ maximalIdeal C := map_maximalIdeal_le f
  let π := Ideal.Quotient.mk J
  let e : ResidueField A →+* C ⧸ J :=
    Ideal.Quotient.lift (maximalIdeal A) (π.comp f)
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f ha)
  have he (a : A) : e (residue A a) = π (f a) := rfl
  have hR (r : R) : φ (1 ⊗ₜ[R] algebraMap R B r) = f (algebraMap R A r) := by
    change φ (Algebra.TensorProduct.includeRight (algebraMap R B r)) = _
    simp [f, RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom]
  have hRB : (maximalIdeal R).map
      (((π.comp φ).comp Algebra.TensorProduct.includeRight.toRingHom).comp
        (algebraMap R B)) = ⊥ := by
    rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro r hr
    change π (φ (1 ⊗ₜ[R] algebraMap R B r)) = 0
    rw [hR]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem f ((map_maximalIdeal_le (algebraMap R A))
        (Ideal.mem_map_of_mem (algebraMap R A) hr)))
  have hright (b : B) : ∃ a : A, π (φ (1 ⊗ₜ[R] b)) = π (f a) := by
    obtain ⟨r, hr⟩ := hB b
    refine ⟨algebraMap R A r, ?_⟩
    have hm := Ideal.mem_map_of_mem ((π.comp φ).comp
      Algebra.TensorProduct.includeRight.toRingHom) hr
    rw [Ideal.map_map, hRB] at hm
    change π (φ (1 ⊗ₜ[R] (b - algebraMap R B r))) = 0 at hm
    simpa [map_sub, sub_eq_zero, TensorProduct.tmul_sub, hR] using hm
  have htensor (t : A ⊗[R] B) : ∃ a : A, π (φ t) = π (f a) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      obtain ⟨a', ha'⟩ := hright b
      refine ⟨a * a', ?_⟩
      have ht : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * (1 ⊗ₜ[R] b) := by simp
      rw [ht, map_mul, map_mul, ha']
      change π (f a) * π (f a') = π (f (a * a'))
      simp only [map_mul]
    | add t t' ht ht' =>
      obtain ⟨a, ha⟩ := ht
      obtain ⟨a', ha'⟩ := ht'
      exact ⟨a + a', by simp [ha, ha']⟩
  let := φ.toAlgebra
  have : IsLocalization M C := hLoc
  have : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (ne_of_lt
    (lt_of_le_of_lt hJ (maximalIdeal.isMaximal C).lt_top))
  have hesurj : Function.Surjective e := by
    intro c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨⟨t, m⟩, htm⟩ := IsLocalization.surj M c
    obtain ⟨a, ha⟩ := htensor t
    obtain ⟨b, hb⟩ := htensor m
    have hbunit : IsUnit (e (residue A b)) := by
      rw [he, ← hb]
      exact (IsLocalization.map_units C m).map π
    have hb0 : residue A b ≠ 0 := fun hb0 => by simpa [hb0] using hbunit.ne_zero
    refine ⟨residue A a / residue A b, ?_⟩
    apply hbunit.mul_left_inj.mp
    rw [← map_mul, div_mul_cancel₀ _ hb0, he, ← ha, he, ← hb, ← map_mul]
    exact congrArg π htm.symm
  have hfield : IsField (C ⧸ J) := by
    refine ⟨exists_pair_ne (C ⧸ J), mul_comm, ?_⟩
    intro c hc
    obtain ⟨a, rfl⟩ := hesurj c
    have ha : a ≠ 0 := fun ha => hc (by simp [ha])
    exact ⟨e a⁻¹, by rw [← map_mul, mul_inv_cancel₀ ha, map_one]⟩
  exact ((Ideal.Quotient.maximal_ideal_iff_isField_quotient J).2 hfield).eq_of_le
    (maximalIdeal.isMaximal C).ne_top hJ

/-- The ideal of `A ⊗[R] B` generated by `𝔪_A` contains the one generated by `𝔪_R` through the
right factor, because `1 ⊗ r` and `r ⊗ 1` are the same element. -/
private lemma map_maximalIdeal_includeRight_le_map_includeLeft
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A]
    [Algebra R A] [Algebra R B] [IsLocalHom (algebraMap R A)] :
    ((maximalIdeal R).map (algebraMap R B)).map
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B) ≤
      (maximalIdeal A).map
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) := by
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro r hr
  have hswap : (1 : A) ⊗ₜ[R] algebraMap R B r = (algebraMap R A r) ⊗ₜ[R] (1 : B) := by
    rw [Algebra.algebraMap_eq_smul_one r (A := B), Algebra.algebraMap_eq_smul_one r (A := A),
      TensorProduct.smul_tmul]
  change (1 : A) ⊗ₜ[R] algebraMap R B r ∈
    (maximalIdeal A).map (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)
  rw [hswap]
  exact Ideal.mem_map_of_mem _ ((map_maximalIdeal_le (algebraMap R A))
    (Ideal.mem_map_of_mem (algebraMap R A) hr))

/-- **Density of the left factor in a tensor product.** If every element of `B` agrees with one
coming from `R` modulo `𝔪_R`, then every element of `A ⊗[R] B` agrees with one coming from `A`
modulo the ideal generated by `𝔪_A`. -/
private lemma exists_sub_includeLeft_mem_map_maximalIdeal
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A]
    [Algebra R A] [Algebra R B] [IsLocalHom (algebraMap R A)]
    (hB : ∀ b : B, ∃ r : R,
      b - algebraMap R B r ∈ (maximalIdeal R).map (algebraMap R B))
    (t : A ⊗[R] B) :
    ∃ a : A, t - Algebra.TensorProduct.includeLeftRingHom a ∈
      (maximalIdeal A).map
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) := by
  set J := (maximalIdeal A).map
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) with hJdef
  have hright : ((maximalIdeal R).map (algebraMap R B)).map
      (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B) ≤ J :=
    map_maximalIdeal_includeRight_le_map_includeLeft
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨r, hr⟩ := hB b
    refine ⟨a * algebraMap R A r, ?_⟩
    have hmem : (1 : A) ⊗ₜ[R] (b - algebraMap R B r) ∈ J :=
      hright (Ideal.mem_map_of_mem _ hr)
    have hprod : a ⊗ₜ[R] b - (a * algebraMap R A r) ⊗ₜ[R] (1 : B) =
        (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] (b - algebraMap R B r)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sub, mul_one]
      congr 1
      rw [Algebra.algebraMap_eq_smul_one r (A := B), TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.smul_def, mul_comm a (algebraMap R A r)]
    change a ⊗ₜ[R] b - Algebra.TensorProduct.includeLeftRingHom (a * algebraMap R A r) ∈ J
    change a ⊗ₜ[R] b - (a * algebraMap R A r) ⊗ₜ[R] (1 : B) ∈ J
    rw [hprod]
    exact Ideal.mul_mem_left _ _ hmem
  | add t t' ht ht' =>
    obtain ⟨a, ha⟩ := ht
    obtain ⟨a', ha'⟩ := ht'
    refine ⟨a + a', ?_⟩
    have h : t + t' - Algebra.TensorProduct.includeLeftRingHom (a + a') =
        (t - Algebra.TensorProduct.includeLeftRingHom a) +
          (t' - Algebra.TensorProduct.includeLeftRingHom a') := by
      rw [map_add]; ring
    rw [h]
    exact Ideal.add_mem _ ha ha'

/-- In a local ring, an element agreeing with a unit modulo the maximal ideal is a unit. -/
private lemma isUnit_of_sub_mem_maximalIdeal {C : Type*} [CommRing C] [IsLocalRing C]
    {x y : C} (hx : IsUnit x) (h : x - y ∈ maximalIdeal C) : IsUnit y := by
  by_contra hy
  have hy' : y ∈ maximalIdeal C := (mem_maximalIdeal y).mpr hy
  have hx' : x ∈ maximalIdeal C := by
    have hsum := Ideal.add_mem (maximalIdeal C) h hy'
    simpa only [sub_add_cancel] using hsum
  exact (mem_maximalIdeal x).mp hx' hx

/-- **A map out of a local localization of `A ⊗[R] B` is determined by the two factors.** -/
private lemma ringHom_ext_of_tensor_localization
    {R A B C' C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C'] [CommRing C]
    [Algebra R A] [Algebra R B]
    (φ : A ⊗[R] B →+* C') (M : Submonoid (A ⊗[R] B))
    (hLoc : letI := φ.toAlgebra; IsLocalization M C')
    (Λ₁ Λ₂ : C' →+* C)
    (hl : Λ₁.comp (φ.comp Algebra.TensorProduct.includeLeftRingHom) =
      Λ₂.comp (φ.comp Algebra.TensorProduct.includeLeftRingHom))
    (hr : Λ₁.comp (φ.comp Algebra.TensorProduct.includeRight.toRingHom) =
      Λ₂.comp (φ.comp Algebra.TensorProduct.includeRight.toRingHom)) :
    Λ₁ = Λ₂ := by
  let := φ.toAlgebra
  have : IsLocalization M C' := hLoc
  refine IsLocalization.ringHom_ext M ?_
  have halg : (algebraMap (A ⊗[R] B) C') = φ := rfl
  rw [halg]
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have ht : a ⊗ₜ[R] b =
        (Algebra.TensorProduct.includeLeftRingHom a : A ⊗[R] B) *
          (Algebra.TensorProduct.includeRight.toRingHom b : A ⊗[R] B) := by
      change a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change Λ₁ (φ (a ⊗ₜ[R] b)) = Λ₂ (φ (a ⊗ₜ[R] b))
    rw [ht, map_mul, map_mul, map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun hl a) (RingHom.congr_fun hr b)
  | add t t' ht ht' =>
    change Λ₁ (φ (t + t')) = Λ₂ (φ (t + t'))
    simp only [map_add]
    exact congrArg₂ (· + ·) ht ht'

/-- **A map out of a local localization of `A ⊗[R] B` from maps on the two factors.** Let `C'`
be a local localization of `A ⊗[R] B` whose structure map is local on the left factor, with `A`
local over the local ring `R` and every element of `B` congruent to one from `R` modulo `𝔪_R`.
Then any pair of ring maps `u : A → C`, `v : B → C` into a local ring `C` which agree on `R`,
with `u` local, extends uniquely to a local ring map `C' → C`.

Geometrically `C'` is the local ring of a fibre product `X ×_S Y` at a point, and this says
that a map out of it is the same thing as a compatible pair of maps out of the local rings of
`X` and of `Y`. -/
private lemma exists_ringHom_of_tensor_localization
    {R A B C' C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C'] [CommRing C]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing C'] [IsLocalRing C]
    [Algebra R A] [Algebra R B] [IsLocalHom (algebraMap R A)]
    (φ : A ⊗[R] B →+* C')
    [IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom)]
    (hB : ∀ b : B, ∃ r : R,
      b - algebraMap R B r ∈ (maximalIdeal R).map (algebraMap R B))
    (M : Submonoid (A ⊗[R] B))
    (hLoc : letI := φ.toAlgebra; IsLocalization M C')
    (u : A →+* C) (v : B →+* C) (hu : IsLocalHom u)
    (huv : u.comp (algebraMap R A) = v.comp (algebraMap R B)) :
    ∃ Λ : C' →+* C, IsLocalHom Λ ∧
      Λ.comp (φ.comp Algebra.TensorProduct.includeLeftRingHom) = u ∧
      Λ.comp (φ.comp Algebra.TensorProduct.includeRight.toRingHom) = v := by
  let := φ.toAlgebra
  have : IsLocalization M C' := hLoc
  have := hu
  let : Algebra R C := (u.comp (algebraMap R A)).toAlgebra
  have halgC : ∀ r : R, algebraMap R C r = u (algebraMap R A r) := fun _ => rfl
  let uA : A →ₐ[R] C := AlgHom.mk' u (by
    intro r a
    show u (r • a) = r • u a
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halgC])
  let vA : B →ₐ[R] C := AlgHom.mk' v (by
    intro r b
    show v (r • b) = r • v b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halgC]
    exact congrArg (· * v b) (RingHom.congr_fun huv r).symm)
  obtain ⟨ψ, hψl, hψr⟩ : ∃ ψ : A ⊗[R] B →+* C,
      ψ.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) = u ∧
      ψ.comp (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B) = v := by
    refine ⟨(Algebra.TensorProduct.lift uA vA
      (fun x y => mul_comm (uA x) (vA y))).toRingHom, RingHom.ext fun a => ?_,
      RingHom.ext fun b => ?_⟩
    · change u a * v 1 = u a
      rw [map_one, mul_one]
    · change u 1 * v b = v b
      rw [map_one, one_mul]
  have hψla : ∀ a : A, ψ (Algebra.TensorProduct.includeLeftRingHom a) = u a :=
    fun a => RingHom.congr_fun hψl a
  set J := (maximalIdeal A).map
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) with hJdef
  have hJψ : ∀ t ∈ J, ψ t ∈ maximalIdeal C := by
    have hle : J.map ψ ≤ maximalIdeal C := by
      rw [hJdef, Ideal.map_map, hψl]
      exact map_maximalIdeal_le u
    exact fun t ht => hle (Ideal.mem_map_of_mem _ ht)
  have hJφ : ∀ t ∈ J, φ t ∈ maximalIdeal C' := by
    have hle : J.map φ ≤ maximalIdeal C' := by
      rw [hJdef, Ideal.map_map]
      exact map_maximalIdeal_le _
    exact fun t ht => hle (Ideal.mem_map_of_mem _ ht)
  -- an element of `A ⊗[R] B` whose image in `C'` is a unit has unit image in `C` as well
  have hkey : ∀ t : A ⊗[R] B, IsUnit (φ t) → IsUnit (ψ t) := by
    intro t ht
    obtain ⟨a, ha⟩ := exists_sub_includeLeft_mem_map_maximalIdeal hB t
    have h2 : φ t - φ (Algebra.TensorProduct.includeLeftRingHom a) ∈ maximalIdeal C' := by
      rw [← map_sub]
      exact hJφ _ ha
    have h4 : IsUnit a :=
      (isUnit_map_iff (φ.comp Algebra.TensorProduct.includeLeftRingHom) a).mp
        (isUnit_of_sub_mem_maximalIdeal ht h2)
    refine isUnit_of_sub_mem_maximalIdeal (h4.map u) ?_
    have hneg : u a - ψ t =
        -(ψ (t - Algebra.TensorProduct.includeLeftRingHom a)) := by
      rw [map_sub, hψla a]; ring
    rw [hneg]
    exact neg_mem (hJψ _ ha)
  -- conversely, an element with non-unit image in `C'` has non-unit image in `C`
  have hkey' : ∀ t : A ⊗[R] B, φ t ∈ maximalIdeal C' → ψ t ∈ maximalIdeal C := by
    intro t ht
    obtain ⟨a, ha⟩ := exists_sub_includeLeft_mem_map_maximalIdeal hB t
    have ha' : φ (Algebra.TensorProduct.includeLeftRingHom a) ∈ maximalIdeal C' := by
      have hd : φ t - φ (Algebra.TensorProduct.includeLeftRingHom a) ∈ maximalIdeal C' := by
        rw [← map_sub]
        exact hJφ _ ha
      have hsub := Ideal.sub_mem (maximalIdeal C') ht hd
      simpa only [sub_sub_cancel] using hsub
    have hamem : a ∈ maximalIdeal A :=
      (mem_maximalIdeal a).mpr fun hua => (mem_maximalIdeal _).mp ha'
        (hua.map (φ.comp Algebra.TensorProduct.includeLeftRingHom))
    have hua : u a ∈ maximalIdeal C := map_maximalIdeal_le u (Ideal.mem_map_of_mem u hamem)
    have hd : ψ t - u a ∈ maximalIdeal C := by
      have heq : ψ t - u a = ψ (t - Algebra.TensorProduct.includeLeftRingHom a) := by
        rw [map_sub, hψla a]
      rw [heq]
      exact hJψ _ ha
    have hsum := Ideal.add_mem (maximalIdeal C) hd hua
    simpa only [sub_add_cancel] using hsum
  have hunit : ∀ m : M, IsUnit (ψ (m : A ⊗[R] B)) := fun m =>
    hkey _ (IsLocalization.map_units C' m)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : C' →+* C, ∀ t : A ⊗[R] B, Λ (φ t) = ψ t :=
    ⟨IsLocalization.lift (S := C') hunit, fun t => IsLocalization.lift_eq hunit t⟩
  refine ⟨Λ, ⟨fun ξ hξ => ?_⟩, RingHom.ext fun a => (hΛ _).trans (RingHom.congr_fun hψl a),
    RingHom.ext fun b => (hΛ _).trans (RingHom.congr_fun hψr b)⟩
  by_contra hns
  have hmem : ξ ∈ maximalIdeal C' := (mem_maximalIdeal ξ).mpr hns
  obtain ⟨⟨t, m⟩, htm⟩ := IsLocalization.surj (S := C') M ξ
  have htm' : ξ * φ (m : A ⊗[R] B) = φ t := htm
  have hφt : φ t ∈ maximalIdeal C' := by
    rw [← htm']
    exact Ideal.mul_mem_right _ _ hmem
  obtain ⟨w, hw⟩ := hunit m
  have hprod : Λ ξ * ψ (m : A ⊗[R] B) ∈ maximalIdeal C := by
    rw [← hΛ (m : A ⊗[R] B), ← map_mul, htm', hΛ t]
    exact hkey' t hφt
  have hcancel : Λ ξ = (Λ ξ * ψ (m : A ⊗[R] B)) * (↑w⁻¹ : C) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  have hfinal : Λ ξ ∈ maximalIdeal C := by
    rw [hcancel]
    exact Ideal.mul_mem_right _ _ hprod
  exact (mem_maximalIdeal _).mp hfinal hξ

/-- If a local homomorphism carries the maximal ideal onto the maximal ideal and is surjective
on residue fields, then every element of the target agrees with one from the source modulo the
image of the maximal ideal. -/
private lemma exists_sub_mem_map_maximalIdeal_of_residueField_surjective
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    (f : R →+* B) [IsLocalHom f]
    (hm : (maximalIdeal R).map f = maximalIdeal B)
    (hf : Function.Surjective (IsLocalRing.ResidueField.map f)) (b : B) :
    ∃ r : R, b - f r ∈ (maximalIdeal R).map f := by
  obtain ⟨r, hr⟩ := hf (residue B b)
  obtain ⟨a, rfl⟩ := residue_surjective r
  refine ⟨a, ?_⟩
  rw [hm, ← Ideal.Quotient.eq_zero_iff_mem]
  change residue B (b - f a) = 0
  simpa [map_sub, sub_eq_zero, ResidueField.map_residue] using hr.symm

/-- The density of the image of `R` modulo `𝔪_R` transports along an isomorphism of the
target. -/
private lemma exists_sub_mem_map_maximalIdeal_of_comp_equiv
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C] [IsLocalRing R]
    (f : R →+* B) (e : B ≃+* C)
    (h : ∀ c : C, ∃ r : R, c - (e.toRingHom.comp f) r ∈
      (maximalIdeal R).map (e.toRingHom.comp f)) (b : B) :
    ∃ r : R, b - f r ∈ (maximalIdeal R).map f := by
  obtain ⟨r, hr⟩ := h (e b)
  refine ⟨r, ?_⟩
  have h' := Ideal.mem_map_of_mem e.symm.toRingHom hr
  have he : e.symm.toRingHom.comp (e.toRingHom.comp f) = f := by ext; simp
  rw [Ideal.map_map] at h'
  change e.symm (e b - e (f r)) ∈
    (maximalIdeal R).map (e.symm.toRingHom.comp (e.toRingHom.comp f)) at h'
  rw [he] at h'
  simpa using h'

/-- The density of the image modulo the maximal ideal passes from a local homomorphism out of
`𝒪_{X, x}` to the map of stalks of the associated morphism of schemes. -/
private lemma exists_sub_mem_map_maximalIdeal_stalkMap_specMap_fromSpecStalk
    {X : Scheme.{u}} (x : X) (B : Type u) [CommRing B] [IsLocalRing B]
    (f : X.presheaf.stalk x →+* B) [IsLocalHom f]
    (hf : ∀ b : B, ∃ a : X.presheaf.stalk x,
      b - f a ∈ (maximalIdeal (X.presheaf.stalk x)).map f) :
    let g := Spec.map (CommRingCat.ofHom f) ≫ X.fromSpecStalk x
    ∀ b : (Spec (.of B)).presheaf.stalk (closedPoint B),
      ∃ a : X.presheaf.stalk (g (closedPoint B)),
        b - (g.stalkMap (closedPoint B)).hom a ∈
          (maximalIdeal (X.presheaf.stalk (g (closedPoint B)))).map
            (g.stalkMap (closedPoint B)).hom := by
  let g := Spec.map (CommRingCat.ofHom f) ≫ X.fromSpecStalk x
  have h := (SpecToEquivOfLocalRing X (CommRingCat.of B)).right_inv
    ⟨x, ⟨CommRingCat.ofHom f, inferInstance⟩⟩
  have hP := congrArg (fun z : Σ y,
      {g : X.presheaf.stalk y ⟶ CommRingCat.of B // IsLocalHom g.hom} =>
    ∀ b : B, ∃ a : X.presheaf.stalk z.1,
      b - z.2.1.hom a ∈ (maximalIdeal (X.presheaf.stalk z.1)).map z.2.1.hom) h
  have hg : ∀ b : B, ∃ a : X.presheaf.stalk (g (closedPoint B)),
      b - (Scheme.stalkClosedPointTo g).hom a ∈
        (maximalIdeal (X.presheaf.stalk (g (closedPoint B)))).map
          (Scheme.stalkClosedPointTo g).hom := hP.mpr hf
  exact exists_sub_mem_map_maximalIdeal_of_comp_equiv (g.stalkMap _).hom
    (stalkClosedPointIso (.of B)).commRingCatIsoToRingEquiv hg

/-- The density of the image modulo the maximal ideal transports along an isomorphism of the
source. -/
private lemma exists_sub_mem_map_maximalIdeal_comp_equiv
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    [IsLocalRing R] [IsLocalRing R'] (e : R ≃+* R') (f : R' →+* B)
    (h : ∀ b : B, ∃ r : R', b - f r ∈ (maximalIdeal R').map f) (b : B) :
    ∃ r : R, b - (f.comp e.toRingHom) r ∈ (maximalIdeal R).map
      (f.comp e.toRingHom) := by
  obtain ⟨r, hr⟩ := h b
  refine ⟨e.symm r, ?_⟩
  rw [← Ideal.map_map, map_maximalIdeal_of_surjective e.toRingHom e.surjective]
  simpa using hr

/-- The density of the image modulo the maximal ideal passes from a composite to its second
factor. If every element of `B` agrees with one from `R` modulo the ideal generated by the image
of `𝔪_R`, and `R → R'` is local, then every element of `B` agrees with one from `R'` modulo the
ideal generated by the image of `𝔪_{R'}`. -/
private lemma exists_sub_mem_map_maximalIdeal_of_comp_left
    {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B]
    [IsLocalRing R] [IsLocalRing R'] (h : R →+* R') [IsLocalHom h] (g : R' →+* B)
    (hRB : ∀ b : B, ∃ r : R, b - (g.comp h) r ∈ (maximalIdeal R).map (g.comp h))
    (b : B) : ∃ r : R', b - g r ∈ (maximalIdeal R').map g := by
  obtain ⟨r, hr⟩ := hRB b
  refine ⟨h r, ?_⟩
  have hle : (maximalIdeal R).map (g.comp h) ≤ (maximalIdeal R').map g := by
    rw [← Ideal.map_map]
    exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le h)
  exact hle hr

/-- **A ring isomorphism of local rings descends to the `𝔪 ^ N`-truncations.** -/
private def quotientPowEquiv {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (N : ℕ) :
    (A ⧸ maximalIdeal A ^ N) ≃+* (B ⧸ maximalIdeal B ^ N) :=
  Ideal.quotientEquiv _ _ e (by
    rw [Ideal.map_pow]
    exact congrArg (· ^ N) (map_maximalIdeal_eq_ringEquiv e).symm)

private lemma quotientPowEquiv_mk {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (N : ℕ) (a : A) :
    quotientPowEquiv e N (Ideal.Quotient.mk (maximalIdeal A ^ N) a) =
      Ideal.Quotient.mk (maximalIdeal B ^ N) (e a) :=
  Ideal.quotientEquiv_mk _ _ _ _ _

/-- **`AlgebraicGeometry.completionQuotientEquiv` is `AdicCompletion.evalₐ`**, on the whole
completion and not only on the image of the ring. -/
private lemma completionQuotientEquiv_quotient_mk (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (N : ℕ) (ζ : AdicCompletion (maximalIdeal R) R) :
    completionQuotientEquiv R N
        (Ideal.Quotient.mk
          (maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ N) ζ) =
      AdicCompletion.evalₐ (maximalIdeal R) N ζ := by
  simp only [completionQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

/-- If every element of `𝒪_{Y, g y}` agrees with one from `𝒪_{S, s}` modulo `𝔪_s`, then the
maximal ideal of the local ring of `X ×_S Y` at a point is generated by that of `X`. -/
private lemma maximalIdeal_map_pullback_fst_of_dense_stalkMap
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : (pullback f g : Scheme.{u}))
    (hB : ∀ b : Y.presheaf.stalk (pullback.snd f g z),
      ∃ r : S.presheaf.stalk (g (pullback.snd f g z)),
        b - (g.stalkMap (pullback.snd f g z)).hom r ∈
          (maximalIdeal (S.presheaf.stalk (g (pullback.snd f g z)))).map
            (g.stalkMap (pullback.snd f g z)).hom) :
    (maximalIdeal (X.presheaf.stalk (pullback.fst f g z))).map
      ((pullback.fst f g).stalkMap z).hom =
        maximalIdeal ((pullback f g).presheaf.stalk z) := by
  have hcond : (pullback.fst f g ≫ f).base z = (pullback.snd f g ≫ g).base z :=
    congrArg (fun k : pullback f g ⟶ S => k.base z) pullback.condition
  let : Algebra ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(X.presheaf.stalk ((pullback.fst f g).base z)) :=
    (f.stalkMap ((pullback.fst f g).base z)).hom.toAlgebra
  let : Algebra ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(Y.presheaf.stalk ((pullback.snd f g).base z)) :=
    ((eqToHom (congrArg S.presheaf.stalk hcond)) ≫
      g.stalkMap ((pullback.snd f g).base z)).hom.toAlgebra
  have : IsLocalHom (algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(X.presheaf.stalk ((pullback.fst f g).base z))) :=
    inferInstanceAs (IsLocalHom (f.stalkMap ((pullback.fst f g).base z)).hom)
  obtain ⟨φ, hleft, hright, M, hM⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g z
  have : IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom) := by
    rw [hleft]
    infer_instance
  have hmod : ∀ b : ↑(Y.presheaf.stalk ((pullback.snd f g).base z)),
      ∃ r : ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z)),
        b - algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
            ↑(Y.presheaf.stalk ((pullback.snd f g).base z)) r ∈
          (maximalIdeal ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))).map
            (algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
              ↑(Y.presheaf.stalk ((pullback.snd f g).base z))) :=
    exists_sub_mem_map_maximalIdeal_comp_equiv
      (eqToIso (congrArg S.presheaf.stalk hcond)).commRingCatIsoToRingEquiv
      (g.stalkMap ((pullback.snd f g).base z)).hom hB
  simpa only [hleft] using maximalIdeal_map_of_tensor_localization φ hmod M hM

/-- The maximal ideal of the local ring of `X ×_S Spec 𝒪^∧_{S, s}` at a point over the closed
point is generated by the maximal ideal of `𝒪_{X, x}`. -/
private lemma maximalIdeal_map_pullback_fst_completion
    {X S : Scheme.{u}} (p : X ⟶ S) (s : S)
    [IsNoetherianRing (S.presheaf.stalk s)]
    (z : (pullback p (Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s) : Scheme.{u}))
    (hz : pullback.snd p _ z = closedPoint
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) :
    (maximalIdeal (X.presheaf.stalk (pullback.fst p _ z))).map
      ((pullback.fst p _).stalkMap z).hom =
        maximalIdeal ((pullback p _).presheaf.stalk z) := by
  apply maximalIdeal_map_pullback_fst_of_dense_stalkMap
  rw [hz]
  apply exists_sub_mem_map_maximalIdeal_stalkMap_specMap_fromSpecStalk
  exact exists_sub_mem_map_maximalIdeal_of_residueField_surjective _
    AdicCompletion.maximalIdeal_eq_map.symm
    (AdicCompletion.residueField_map_bijective (S.presheaf.stalk s)).surjective

/-! ### Maps out of the local ring of a base change -/

/-- The comparison isomorphism of stalks attached to an equality of points is the cast. -/
private lemma stalkCongr_hom_eq_eqToHom {X : Scheme.{u}} {x y : X} (e : x = y) :
    (X.presheaf.stalkCongr (.of_eq e)).hom = eqToHom (congrArg X.presheaf.stalk e) := by
  cases e
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  simp

/-- At the image of the point itself, `stalkHomAt` is the stalk map. -/
private lemma stalkHomAt_rfl {U Y : Scheme.{u}} (q : U ⟶ Y) (p : U) :
    q.stalkHomAt (rfl : q p = q p) = (q.stalkMap p).hom := by
  change ((Y.presheaf.stalkCongr (.of_eq (rfl : q p = q p))).hom ≫ q.stalkMap p).hom = _
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]

/-- The square of local rings attached to a commuting square of morphisms. -/
private lemma stalkHomAt_comp_eq_of_comp_eq {X Y₁ Y₂ Z : Scheme.{u}} {f₁ : X ⟶ Y₁} {g₁ : Y₁ ⟶ Z}
    {f₂ : X ⟶ Y₂} {g₂ : Y₂ ⟶ Z} (h : f₁ ≫ g₁ = f₂ ≫ g₂) {x : X} {y₁ : Y₁} {y₂ : Y₂} {z : Z}
    (hx₁ : f₁ x = y₁) (hy₁ : g₁ y₁ = z) (hx₂ : f₂ x = y₂) (hy₂ : g₂ y₂ = z) :
    (f₁.stalkHomAt hx₁).comp (g₁.stalkHomAt hy₁) =
      (f₂.stalkHomAt hx₂).comp (g₂.stalkHomAt hy₂) := by
  rw [← Scheme.Hom.stalkHomAt_comp, ← Scheme.Hom.stalkHomAt_comp]
  exact stalkHomAt_congr h _ _

/-- **A map out of the local ring of a fibre product is determined by the two projections.** -/
private lemma ringHom_stalk_pullback_ext
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme.{u}))
    {x : X} {y : Y} (hx : pullback.fst f g z = x) (hy : pullback.snd f g z = y)
    {C : Type u} [CommRing C]
    (Λ₁ Λ₂ : (pullback f g : Scheme.{u}).presheaf.stalk z →+* C)
    (hl : Λ₁.comp ((pullback.fst f g).stalkHomAt hx) =
      Λ₂.comp ((pullback.fst f g).stalkHomAt hx))
    (hr : Λ₁.comp ((pullback.snd f g).stalkHomAt hy) =
      Λ₂.comp ((pullback.snd f g).stalkHomAt hy)) :
    Λ₁ = Λ₂ := by
  subst hx
  subst hy
  rw [stalkHomAt_rfl] at hl hr
  have hcond : (pullback.fst f g ≫ f).base z = (pullback.snd f g ≫ g).base z :=
    congrArg (fun k : pullback f g ⟶ S => k.base z) pullback.condition
  let : Algebra ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(X.presheaf.stalk ((pullback.fst f g).base z)) :=
    (f.stalkMap ((pullback.fst f g).base z)).hom.toAlgebra
  let : Algebra ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(Y.presheaf.stalk ((pullback.snd f g).base z)) :=
    ((eqToHom (congrArg S.presheaf.stalk hcond)) ≫
      g.stalkMap ((pullback.snd f g).base z)).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hM⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g z
  exact ringHom_ext_of_tensor_localization φ M hM Λ₁ Λ₂ (by rwa [hleft])
    (by rwa [hright])

/-- **The local ring of a fibre product from the two projections.** Let `f : X ⟶ S` and
`g : Y ⟶ S` be morphisms, let `z` be a point of `X ×_S Y` over `x`, `y` and `s`, and assume
every element of `𝒪_{Y, y}` agrees with one from `𝒪_{S, s}` modulo `𝔪_s` — for instance because
`g` is an isomorphism on residue fields at `y`. Then a local map `u` out of `𝒪_{X, x}` and a map
`v` out of `𝒪_{Y, y}` into a local ring `C` which agree on `𝒪_{S, s}` are induced by a unique
local map out of `𝒪_{X ×_S Y, z}`.

This is what compares the local rings of two base changes of one morphism along two maps which
agree only modulo a power of the maximal ideal: the comparison map is produced from the two
projections, with no identification of the two bases themselves. -/
private lemma exists_ringHom_stalk_pullback
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme.{u}))
    {x : X} {y : Y} {s : S}
    (hx : pullback.fst f g z = x) (hy : pullback.snd f g z = y)
    (hfs : f x = s) (hgs : g y = s)
    {C : Type u} [CommRing C] [IsLocalRing C]
    (hB : ∀ b : Y.presheaf.stalk y, ∃ r : S.presheaf.stalk s,
      b - g.stalkHomAt hgs r ∈
        (maximalIdeal (S.presheaf.stalk s)).map (g.stalkHomAt hgs))
    (u : X.presheaf.stalk x →+* C) (v : Y.presheaf.stalk y →+* C) (hu : IsLocalHom u)
    (huv : u.comp (f.stalkHomAt hfs) = v.comp (g.stalkHomAt hgs)) :
    ∃ Λ : (pullback f g : Scheme.{u}).presheaf.stalk z →+* C, IsLocalHom Λ ∧
      Λ.comp ((pullback.fst f g).stalkHomAt hx) = u ∧
      Λ.comp ((pullback.snd f g).stalkHomAt hy) = v := by
  subst hx
  subst hy
  subst hfs
  rw [stalkHomAt_rfl] at huv
  have hcond : (pullback.fst f g ≫ f).base z = (pullback.snd f g ≫ g).base z :=
    congrArg (fun k : pullback f g ⟶ S => k.base z) pullback.condition
  have hgstalk : g.stalkHomAt hgs =
      ((eqToHom (congrArg S.presheaf.stalk hcond)) ≫
        g.stalkMap ((pullback.snd f g).base z)).hom :=
    congrArg CommRingCat.Hom.hom
      (congrArg (· ≫ g.stalkMap ((pullback.snd f g).base z))
        (stalkCongr_hom_eq_eqToHom hgs.symm))
  let : Algebra ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(X.presheaf.stalk ((pullback.fst f g).base z)) :=
    (f.stalkMap ((pullback.fst f g).base z)).hom.toAlgebra
  let : Algebra ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(Y.presheaf.stalk ((pullback.snd f g).base z)) :=
    ((eqToHom (congrArg S.presheaf.stalk hcond)) ≫
      g.stalkMap ((pullback.snd f g).base z)).hom.toAlgebra
  have : IsLocalHom (algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(X.presheaf.stalk ((pullback.fst f g).base z))) :=
    inferInstanceAs (IsLocalHom (f.stalkMap ((pullback.fst f g).base z)).hom)
  obtain ⟨φ, hleft, hright, M, hM⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g z
  have : IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom) := by
    rw [hleft]; infer_instance
  have halgY : (algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(Y.presheaf.stalk ((pullback.snd f g).base z))) = g.stalkHomAt hgs := hgstalk.symm
  have halgX : (algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
      ↑(X.presheaf.stalk ((pullback.fst f g).base z))) =
      (f.stalkMap ((pullback.fst f g).base z)).hom := rfl
  have hB' : ∀ b : ↑(Y.presheaf.stalk ((pullback.snd f g).base z)),
      ∃ r : ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z)),
        b - algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
            ↑(Y.presheaf.stalk ((pullback.snd f g).base z)) r ∈
          (maximalIdeal ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))).map
            (algebraMap ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
              ↑(Y.presheaf.stalk ((pullback.snd f g).base z))) := by
    rw [halgY]
    exact hB
  have huv' : u.comp (algebraMap
        ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
        ↑(X.presheaf.stalk ((pullback.fst f g).base z))) =
      v.comp (algebraMap
        ↑(S.presheaf.stalk ((pullback.fst f g ≫ f).base z))
        ↑(Y.presheaf.stalk ((pullback.snd f g).base z))) := by
    rw [halgY, halgX]
    exact huv
  obtain ⟨Λ, hΛloc, hΛl, hΛr⟩ :=
    exists_ringHom_of_tensor_localization φ hB' M hM u v hu huv'
  refine ⟨Λ, hΛloc, ?_, ?_⟩
  · rw [stalkHomAt_rfl, ← hleft]
    exact hΛl
  · rw [stalkHomAt_rfl, ← hright]
    exact hΛr

-- "Two equal morphisms through a common point induce the same map of local rings" is
-- `StacksDraft.ArtinApproximation.stalkHomAt_congr`, imported from
-- `StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.StalkHomAtHelpers`; the uses
-- below are of that lemma.

/-! ### The `𝔪 ^ N`-truncation of a local ring

Clause (5) of [Stacks Project, Tag 0CAW] is a commuting square of truncations `𝒪 / 𝔪 ^ N`, and
the identification it uses is an isomorphism of two such truncations. The lemmas here are the
ones that produce and compare them: the truncation of a local ring is again local, a local
homomorphism into a truncation kills the `N`-th power of the maximal ideal, the truncation of a
local ring is the truncation of its completion through `AdicCompletion.evalₐ`, and an
isomorphism of completions therefore induces an isomorphism of truncations. -/

/-- For `N ≥ 1` the `N`-th power of the maximal ideal is a proper ideal. -/
private lemma pow_maximalIdeal_ne_top (A : Type*) [CommRing A] [IsLocalRing A] {N : ℕ}
    (hN : 1 ≤ N) : maximalIdeal A ^ N ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top
    (top_le_iff.mp (h.ge.trans (Ideal.pow_le_self (Nat.one_le_iff_ne_zero.mp hN))))

/-- The `𝔪 ^ N`-truncation of a local ring is a local ring, for `N ≥ 1`. -/
private lemma isLocalRing_quotient_pow_maximalIdeal (A : Type*) [CommRing A] [IsLocalRing A]
    {N : ℕ} (hN : 1 ≤ N) : IsLocalRing (A ⧸ maximalIdeal A ^ N) :=
  have : Nontrivial (A ⧸ maximalIdeal A ^ N) :=
    Ideal.Quotient.nontrivial_iff.mpr (pow_maximalIdeal_ne_top A hN)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The `N`-th power of the maximal ideal of the `𝔪 ^ N`-truncation of a local ring vanishes. -/
private lemma pow_maximalIdeal_quotient_eq_bot (A : Type*) [CommRing A] [IsLocalRing A]
    {N : ℕ} (hN : 1 ≤ N) :
    haveI := isLocalRing_quotient_pow_maximalIdeal A hN
    maximalIdeal (A ⧸ maximalIdeal A ^ N) ^ N = ⊥ := by
  have := isLocalRing_quotient_pow_maximalIdeal A hN
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (maximalIdeal A ^ N)) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

/-- **A local homomorphism into a `𝔪 ^ N`-truncation kills `𝔪 ^ N`.** This is what makes a
map out of a local ring into such a truncation factor through the truncation of the source. -/
private lemma eq_zero_of_mem_pow_maximalIdeal {A C : Type*} [CommRing A] [CommRing C]
    [IsLocalRing A] [IsLocalRing C] {N : ℕ} (hN : 1 ≤ N)
    (Θ : A →+* C ⧸ maximalIdeal C ^ N)
    (hΘ : haveI := isLocalRing_quotient_pow_maximalIdeal C hN; IsLocalHom Θ)
    {ξ : A} (hξ : ξ ∈ maximalIdeal A ^ N) : Θ ξ = 0 := by
  have := isLocalRing_quotient_pow_maximalIdeal C hN
  have := hΘ
  have hmem : Θ ξ ∈ maximalIdeal (C ⧸ maximalIdeal C ^ N) ^ N := by
    have hle : (maximalIdeal A ^ N).map Θ ≤ maximalIdeal (C ⧸ maximalIdeal C ^ N) ^ N := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le Θ) N
    exact hle (Ideal.mem_map_of_mem _ hξ)
  rw [pow_maximalIdeal_quotient_eq_bot C hN] at hmem
  simpa using hmem

/-- **The kernel of `AdicCompletion.evalₐ` at `N` is the ideal generated by `I ^ N`.** This is
the completeness of the completion, [Stacks Project, Tag 05GG], in the form in which it says
that `𝒪^∧ / 𝔪 ^ N = 𝒪 / 𝔪 ^ N`. -/
private lemma evalₐ_eq_zero_iff_mem_map_pow {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I.FG) (N : ℕ) (ξ : AdicCompletion I A) :
    AdicCompletion.evalₐ I N ξ = 0 ↔
      ξ ∈ Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ N) := by
  have hle₁ : (I ^ N : Ideal A) ≤ I ^ N • ⊤ := by simp
  have hle₂ : (I ^ N • ⊤ : Ideal A) ≤ I ^ N := by simp
  have hker : ξ ∈ Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ N) ↔
      AdicCompletion.eval I A N ξ = 0 := by
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact Iff.rfl
  rw [hker]
  constructor
  · intro h
    rw [← AdicCompletion.factor_evalₐ_eq_eval I ξ hle₁, h, map_zero]
  · intro h
    rw [← AdicCompletion.factor_eval_eq_evalₐ I ξ hle₂, h, map_zero]

/-- `AdicCompletion.evalₐ` on the image of the ring is the quotient map. -/
private lemma evalₐ_algebraMap {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (a : A) :
    AdicCompletion.evalₐ I N (algebraMap A (AdicCompletion I A) a) =
      Ideal.Quotient.mk (I ^ N) a := by
  rw [AdicCompletion.algebraMap_apply]
  simp

/-- The kernel of `AdicCompletion.evalₐ` at `N` is the `N`-th power of the maximal ideal of the
completion of a Noetherian local ring. -/
private lemma evalₐ_eq_zero_iff_mem_pow_maximalIdeal (C : Type u) [CommRing C] [IsLocalRing C]
    [IsNoetherianRing C] (N : ℕ) (ζ : AdicCompletion (maximalIdeal C) C) :
    AdicCompletion.evalₐ (maximalIdeal C) N ζ = 0 ↔
      ζ ∈ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ N := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  exact evalₐ_eq_zero_iff_mem_map_pow (maximalIdeal C).fg_of_isNoetherianRing N ζ

/-- A local homomorphism of completions carries the kernel of one evaluation into the other. -/
private lemma evalₐ_map_eq_zero_of_isLocalHom {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (N : ℕ)
    (k : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    [IsLocalHom k] {ζ : AdicCompletion (maximalIdeal A) A}
    (hζ : AdicCompletion.evalₐ (maximalIdeal A) N ζ = 0) :
    AdicCompletion.evalₐ (maximalIdeal B) N (k ζ) = 0 := by
  refine (evalₐ_eq_zero_iff_mem_pow_maximalIdeal B N (k ζ)).mpr ?_
  have hmem := (evalₐ_eq_zero_iff_mem_pow_maximalIdeal A N ζ).mp hζ
  have hle : (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ N).map k ≤
      maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le k) N
  exact hle (Ideal.mem_map_of_mem _ hmem)

/-- **A local homomorphism of completions induces a map of `𝔪 ^ N`-truncations.** -/
private lemma exists_quotient_pow_map_of_adicCompletion_ringHom {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (N : ℕ) (k : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    [IsLocalHom k] :
    ∃ κ : (A ⧸ maximalIdeal A ^ N) →+* (B ⧸ maximalIdeal B ^ N),
      ∀ ξ : AdicCompletion (maximalIdeal A) A,
        κ (AdicCompletion.evalₐ (maximalIdeal A) N ξ) =
          AdicCompletion.evalₐ (maximalIdeal B) N (k ξ) := by
  refine ⟨Ideal.Quotient.lift (maximalIdeal A ^ N)
    ((AdicCompletion.evalₐ (maximalIdeal B) N).toRingHom.comp
      (k.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)))) ?_, ?_⟩
  · intro a ha
    refine evalₐ_map_eq_zero_of_isLocalHom N k ?_
    rw [evalₐ_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  · intro ξ
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal A) N ξ)
    have hdiff : AdicCompletion.evalₐ (maximalIdeal A) N
        (ξ - algebraMap A (AdicCompletion (maximalIdeal A) A) a) = 0 := by
      rw [map_sub, ← ha, evalₐ_algebraMap, sub_self]
    have h0 := evalₐ_map_eq_zero_of_isLocalHom N k hdiff
    rw [map_sub, map_sub, sub_eq_zero] at h0
    rw [← ha, Ideal.Quotient.lift_mk]
    exact h0.symm

/-- **An isomorphism of completions induces an isomorphism of `𝔪 ^ N`-truncations.** This is
what turns the isomorphism `φ` of Tag 0CB1, and the isomorphisms of completions attached to the
two elementary étale neighbourhoods of the diagram, into the identifications of truncations
appearing in clause (5) of Tag 0CAW. -/
private lemma exists_ringEquiv_quotient_pow_of_adicCompletion_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (N : ℕ)
    (e : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B) :
    ∃ ε : (A ⧸ maximalIdeal A ^ N) ≃+* (B ⧸ maximalIdeal B ^ N),
      ∀ ξ : AdicCompletion (maximalIdeal A) A,
        ε (AdicCompletion.evalₐ (maximalIdeal A) N ξ) =
          AdicCompletion.evalₐ (maximalIdeal B) N (e ξ) := by
  have : IsLocalHom (e : AdicCompletion (maximalIdeal A) A →+*
    AdicCompletion (maximalIdeal B) B) := ⟨(isLocalHom_equiv e).map_nonunit⟩
  have : IsLocalHom (e.symm : AdicCompletion (maximalIdeal B) B →+*
    AdicCompletion (maximalIdeal A) A) := ⟨(isLocalHom_equiv e.symm).map_nonunit⟩
  obtain ⟨fwd, hfwd⟩ := exists_quotient_pow_map_of_adicCompletion_ringHom N
    (e : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
  obtain ⟨bwd, hbwd⟩ := exists_quotient_pow_map_of_adicCompletion_ringHom N
    (e.symm : AdicCompletion (maximalIdeal B) B →+* AdicCompletion (maximalIdeal A) A)
  refine ⟨RingEquiv.ofBijective fwd (Function.bijective_iff_has_inverse.mpr ⟨bwd, ?_, ?_⟩),
    fun ξ => hfwd ξ⟩
  · intro q
    obtain ⟨ξ, hξ⟩ := AdicCompletion.surjective_evalₐ (maximalIdeal A) N q
    show bwd (fwd q) = q
    rw [← hξ, hfwd, hbwd]
    exact congrArg _ (e.symm_apply_apply ξ)
  · intro q
    obtain ⟨ξ, hξ⟩ := AdicCompletion.surjective_evalₐ (maximalIdeal B) N q
    show fwd (bwd q) = q
    rw [← hξ, hbwd, hfwd]
    exact congrArg _ (e.apply_symm_apply ξ)

/-- The map of `𝔪 ^ N`-truncations induced by a local homomorphism of local rings. -/
private def quotientPowMap {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (N : ℕ) :
    (A ⧸ maximalIdeal A ^ N) →+* (B ⧸ maximalIdeal B ^ N) :=
  Ideal.quotientMap _ f (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le f) N)

private lemma quotientPowMap_mk {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (N : ℕ) (a : A) :
    quotientPowMap f N (Ideal.Quotient.mk (maximalIdeal A ^ N) a) =
      Ideal.Quotient.mk (maximalIdeal B ^ N) (f a) :=
  Ideal.quotientMap_mk

/-- The quotient map onto a `𝔪 ^ N`-truncation is a local homomorphism. -/
private lemma isLocalHom_quotient_mk_pow_maximalIdeal (C : Type*) [CommRing C] [IsLocalRing C]
    {N : ℕ} (hN : 1 ≤ N) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal C ^ N)) :=
  have := isLocalRing_quotient_pow_maximalIdeal C hN
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- The completion map of a morphism, read on the image of the uncompleted local ring. -/
private lemma completionMapAt_algebraMap {U Y : Scheme.{u}} {uu : U} {yy : Y} (c : U ⟶ Y)
    (hc : c uu = yy) (z : Y.presheaf.stalk yy) :
    c.completionMapAt hc (algebraMap (Y.presheaf.stalk yy)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk yy)) (Y.presheaf.stalk yy)) z) =
      algebraMap (U.presheaf.stalk uu)
        (AdicCompletion (maximalIdeal (U.presheaf.stalk uu)) (U.presheaf.stalk uu))
        (c.stalkHomAt hc z) := by
  rw [Scheme.Hom.completionMapAt]
  exact RingHom.congr_fun (adicCompletionMap_comp_algebraMap (c.stalkHomAt hc)
    (maximalIdeal (Y.presheaf.stalk yy)) (maximalIdeal (U.presheaf.stalk uu))
    (IsLocalRing.map_maximalIdeal_le _)) z

/-- The `𝔪 ^ N`-truncation of the completion map of a morphism is the induced map of
truncations. -/
private lemma evalₐ_completionMapAt {U Y : Scheme.{u}} {uu : U} {yy : Y} (c : U ⟶ Y)
    (hc : c uu = yy) (N : ℕ)
    (ξ : AdicCompletion (maximalIdeal (Y.presheaf.stalk yy)) (Y.presheaf.stalk yy)) :
    AdicCompletion.evalₐ (maximalIdeal (U.presheaf.stalk uu)) N (c.completionMapAt hc ξ) =
      quotientPowMap (c.stalkHomAt hc) N
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk yy)) N ξ) := by
  rw [Scheme.Hom.completionMapAt, adicCompletionMap_evalₐ]
  rfl

/-- An étale morphism which is an isomorphism on residue fields at `u` identifies the
`𝔪 ^ N`-truncations of the local rings, compatibly with the completion map and with the local
homomorphism of stalks. -/
private lemma exists_ringEquiv_quotient_pow_of_etale
    {U Z : Scheme.{u}} [IsLocallyNoetherian U] [IsLocallyNoetherian Z] (f : U ⟶ Z) [Etale f]
    {u : U} {z : Z} (hz : f u = z) (hres : IsIso (f.residueFieldMap u)) (N : ℕ) :
    ∃ ε : (Z.presheaf.stalk z ⧸ maximalIdeal (Z.presheaf.stalk z) ^ N) ≃+*
        (U.presheaf.stalk u ⧸ maximalIdeal (U.presheaf.stalk u) ^ N),
      (∀ ξ : AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z),
        ε (AdicCompletion.evalₐ (maximalIdeal (Z.presheaf.stalk z)) N ξ) =
          AdicCompletion.evalₐ (maximalIdeal (U.presheaf.stalk u)) N (f.completionMapAt hz ξ)) ∧
      ∀ a : Z.presheaf.stalk z,
        ε (Ideal.Quotient.mk (maximalIdeal (Z.presheaf.stalk z) ^ N) a) =
          Ideal.Quotient.mk (maximalIdeal (U.presheaf.stalk u) ^ N) (f.stalkHomAt hz a) := by
  have hEt : RingHom.IsEtaleLocalHom (f.stalkHomAt hz) :=
    isEtaleLocalHom_stalkCongr_comp f u hz ((etale_iff_forall_isEtaleAt f).mp inferInstance u)
  obtain ⟨ε, hε⟩ := exists_ringEquiv_quotient_pow_of_adicCompletion_ringEquiv N
    (RingEquiv.ofBijective (f.completionMapAt hz)
      (RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom (f.stalkHomAt hz) hEt
        ((bijective_residueField_map_stalkHomAt_iff f u hz).mpr hres)))
  refine ⟨ε, hε, fun a => ?_⟩
  rw [← evalₐ_algebraMap, hε]
  exact (congrArg (AdicCompletion.evalₐ (maximalIdeal (U.presheaf.stalk u)) N)
    (completionMapAt_algebraMap f hz a)).trans (evalₐ_algebraMap _ N _)

/-- **The order-`N` comparison of two base changes of one morphism.** Let `pA : A ⟶ D` be a
morphism, let `mZ : Z ⟶ D` and `mV : V' ⟶ D` carry `zz` and `vv` to one point `d` of `D`, and
let `uZ` and `wV` be points of `A ×_D Z` and `A ×_D V'` over `a` and over `zz`, `vv`. Assume
every element of `𝒪_{Z, zz}` agrees with one from `𝒪_{D, d}` modulo `𝔪_d` — for instance
because `mZ` is an isomorphism on residue fields at `zz` and generates the maximal ideal — and
assume the two structure maps `𝒪_{D, d} → 𝒪_{Z, zz}` and `𝒪_{D, d} → 𝒪_{V', vv}` are
reconciled modulo `𝔪_{vv} ^ N` by a ring map `cmp`. Then there is a local ring map
`𝒪_{A ×_D Z, uZ} → 𝒪_{A ×_D V', wV} / 𝔪_{wV} ^ N` compatible with the two maps from `𝒪_{A, a}`.

This is the identification which clause (5) of [Stacks Project, Tag 0CAW] calls the canonical
isomorphism of `Y_σ` with `Y ×_{T, τ} V` over `𝒪_{V, v} / 𝔪_v ^ N = 𝒪_{S, s} / 𝔪_s ^ N`, in the
form the proof uses it: a map out of the local ring of the first base change which is compatible
with the maps from the common source. It exists because the local ring of a fibre product is a
localization of the tensor product of the local rings
(`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`), so a map out of it is a
compatible pair of maps out of the two factors; the congruence modulo `𝔪_{vv} ^ N` is exactly
what makes the pair compatible. -/
private lemma exists_ringHom_stalk_pullback_comparison
    {A D Z V' : Scheme.{u}} (pA : A ⟶ D) (mZ : Z ⟶ D) (mV : V' ⟶ D)
    {a : A} {d : D} {zz : Z} {vv : V'}
    (uZ : (pullback pA mZ : Scheme.{u})) (hua : pullback.fst pA mZ uZ = a)
    (huz : pullback.snd pA mZ uZ = zz)
    (wV : (pullback pA mV : Scheme.{u})) (hwa : pullback.fst pA mV wV = a)
    (hwv : pullback.snd pA mV wV = vv)
    (hda : pA a = d) (hdz : mZ zz = d) (hdv : mV vv = d) {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ b : Z.presheaf.stalk zz, ∃ r : D.presheaf.stalk d,
      b - mZ.stalkHomAt hdz r ∈
        (maximalIdeal (D.presheaf.stalk d)).map (mZ.stalkHomAt hdz))
    (cmp : Z.presheaf.stalk zz →+*
      (V'.presheaf.stalk vv) ⧸ (maximalIdeal (V'.presheaf.stalk vv) ^ N))
    (hcmp : cmp.comp (mZ.stalkHomAt hdz) =
      (Ideal.Quotient.mk (maximalIdeal (V'.presheaf.stalk vv) ^ N)).comp
        (mV.stalkHomAt hdv)) :
    ∃ Θ : (pullback pA mZ).presheaf.stalk uZ →+*
        ((pullback pA mV).presheaf.stalk wV) ⧸
          (maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N),
      IsLocalHom Θ ∧
      Θ.comp ((pullback.fst pA mZ).stalkHomAt hua) =
        (Ideal.Quotient.mk (maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N)).comp
          ((pullback.fst pA mV).stalkHomAt hwa) ∧
      Θ.comp ((pullback.snd pA mZ).stalkHomAt huz) =
        (quotientPowMap ((pullback.snd pA mV).stalkHomAt hwv) N).comp cmp := by
  have := isLocalRing_quotient_pow_maximalIdeal ((pullback pA mV).presheaf.stalk wV) hN
  have := isLocalHom_quotient_mk_pow_maximalIdeal
    ((pullback pA mV).presheaf.stalk wV) hN
  have := isLocalRing_quotient_pow_maximalIdeal (V'.presheaf.stalk vv) hN
  -- the map out of `𝒪_{A, a}`: the local ring of the second base change, truncated
  set u := (Ideal.Quotient.mk
      (maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N)).comp
    ((pullback.fst pA mV).stalkHomAt hwa) with hu
  have : IsLocalHom u := by
    rw [hu]
    exact RingHom.isLocalHom_comp _ _
  -- the map out of `𝒪_{Z, zz}`: through the comparison and the second projection
  set v := (quotientPowMap ((pullback.snd pA mV).stalkHomAt hwv) N).comp cmp with hv
  -- the two agree over `𝒪_{D, d}`, by the pullback square and the hypothesis on `cmp`
  have hsq := stalkHomAt_comp_eq_of_comp_eq pullback.condition hwa hda hwv hdv
  have huv : u.comp (pA.stalkHomAt hda) = v.comp (mZ.stalkHomAt hdz) := by
    refine RingHom.ext fun α => ?_
    have h1 := RingHom.congr_fun hsq α
    have h2 := RingHom.congr_fun hcmp α
    change Ideal.Quotient.mk _ ((pullback.fst pA mV).stalkHomAt hwa (pA.stalkHomAt hda α)) =
      quotientPowMap ((pullback.snd pA mV).stalkHomAt hwv) N (cmp (mZ.stalkHomAt hdz α))
    rw [show (pullback.fst pA mV).stalkHomAt hwa (pA.stalkHomAt hda α) =
        (pullback.snd pA mV).stalkHomAt hwv (mV.stalkHomAt hdv α) from h1,
      show cmp (mZ.stalkHomAt hdz α) =
        Ideal.Quotient.mk _ (mV.stalkHomAt hdv α) from h2,
      quotientPowMap_mk]
  obtain ⟨Θ, hΘloc, hΘl, hΘr⟩ :=
    exists_ringHom_stalk_pullback pA mZ uZ hua huz hda hdz hB u v inferInstance huv
  exact ⟨Θ, hΘloc, hΘl.trans hu, hΘr⟩

/-- **The order-`N` comparison of two base changes of one morphism, as an isomorphism of
truncations.** In the setting of
`StacksDraft.ArtinApproximation.exists_ringHom_stalk_pullback_comparison`, assume in addition
that every element of `𝒪_{V', vv}` agrees with one from `𝒪_{D, d}` modulo `𝔪_d` — the same
generation hypothesis as for `𝒪_{Z, zz}`, read on the other side — and that the two structure
maps of `𝒪_{D, d}` are reconciled by an *isomorphism* `e` of the two truncated local rings of
the bases, not merely by a ring map into one of them. Then the comparison of the two base
changes is itself an isomorphism
`𝒪_{A ×_D Z, uZ}/𝔪_{uZ} ^ N ≅ 𝒪_{A ×_D V', wV}/𝔪_{wV} ^ N`,
compatible with the two maps from `𝒪_{A, a}` and with `e` on the two maps from the bases.

This is the `≅` that clause (5) of [Stacks Project, Tag 0CAW] draws between the two base
changes, where the one-directional map suffices for the commutativity of the square alone. Both
directions are produced by
`StacksDraft.ArtinApproximation.exists_ringHom_stalk_pullback_comparison`, and they are mutually
inverse because a map out of the local ring of a fibre product is determined by the two
projections (`StacksDraft.ArtinApproximation.ringHom_stalk_pullback_ext`). -/
private lemma exists_ringEquiv_quotient_pow_stalk_pullback_comparison
    {A D Z V' : Scheme.{u}} (pA : A ⟶ D) (mZ : Z ⟶ D) (mV : V' ⟶ D)
    {a : A} {d : D} {zz : Z} {vv : V'}
    (uZ : (pullback pA mZ : Scheme.{u})) (hua : pullback.fst pA mZ uZ = a)
    (huz : pullback.snd pA mZ uZ = zz)
    (wV : (pullback pA mV : Scheme.{u})) (hwa : pullback.fst pA mV wV = a)
    (hwv : pullback.snd pA mV wV = vv)
    (hda : pA a = d) (hdz : mZ zz = d) (hdv : mV vv = d) {N : ℕ} (hN : 1 ≤ N)
    (hBZ : ∀ b : Z.presheaf.stalk zz, ∃ r : D.presheaf.stalk d,
      b - mZ.stalkHomAt hdz r ∈
        (maximalIdeal (D.presheaf.stalk d)).map (mZ.stalkHomAt hdz))
    (hBV : ∀ b : V'.presheaf.stalk vv, ∃ r : D.presheaf.stalk d,
      b - mV.stalkHomAt hdv r ∈
        (maximalIdeal (D.presheaf.stalk d)).map (mV.stalkHomAt hdv))
    (e : (Z.presheaf.stalk zz ⧸ maximalIdeal (Z.presheaf.stalk zz) ^ N) ≃+*
      (V'.presheaf.stalk vv ⧸ maximalIdeal (V'.presheaf.stalk vv) ^ N))
    (he : ∀ r : D.presheaf.stalk d,
      e (Ideal.Quotient.mk (maximalIdeal (Z.presheaf.stalk zz) ^ N) (mZ.stalkHomAt hdz r)) =
        Ideal.Quotient.mk (maximalIdeal (V'.presheaf.stalk vv) ^ N) (mV.stalkHomAt hdv r)) :
    ∃ θ : ((pullback pA mZ).presheaf.stalk uZ ⧸
          maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N) ≃+*
        ((pullback pA mV).presheaf.stalk wV ⧸
          maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N),
      (∀ c : A.presheaf.stalk a,
        θ (Ideal.Quotient.mk (maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N)
            ((pullback.fst pA mZ).stalkHomAt hua c)) =
          Ideal.Quotient.mk (maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N)
            ((pullback.fst pA mV).stalkHomAt hwa c)) ∧
      ∀ b : Z.presheaf.stalk zz,
        θ (Ideal.Quotient.mk (maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N)
            ((pullback.snd pA mZ).stalkHomAt huz b)) =
          quotientPowMap ((pullback.snd pA mV).stalkHomAt hwv) N
            (e (Ideal.Quotient.mk (maximalIdeal (Z.presheaf.stalk zz) ^ N) b)) := by
  have := isLocalRing_quotient_pow_maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) hN
  have := isLocalRing_quotient_pow_maximalIdeal ((pullback pA mV).presheaf.stalk wV) hN
  have := isLocalHom_quotient_mk_pow_maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) hN
  have := isLocalHom_quotient_mk_pow_maximalIdeal ((pullback pA mV).presheaf.stalk wV) hN
  have := isLocalRing_quotient_pow_maximalIdeal (Z.presheaf.stalk zz) hN
  have := isLocalRing_quotient_pow_maximalIdeal (V'.presheaf.stalk vv) hN
  -- the comparisons in the two directions
  obtain ⟨Θ, hΘloc, hΘl, hΘr⟩ := exists_ringHom_stalk_pullback_comparison pA mZ mV uZ hua huz
    wV hwa hwv hda hdz hdv hN hBZ (e.toRingHom.comp (Ideal.Quotient.mk _))
    (RingHom.ext fun r => he r)
  obtain ⟨Θ', hΘ'loc, hΘ'l, hΘ'r⟩ := exists_ringHom_stalk_pullback_comparison pA mV mZ wV hwa
    hwv uZ hua huz hda hdv hdz hN hBV (e.symm.toRingHom.comp (Ideal.Quotient.mk _))
    (RingHom.ext fun r => (congrArg e.symm (he r)).symm.trans (e.symm_apply_apply _))
  -- the two one-sided compatibilities, read on elements
  have hΘfst : ∀ c : A.presheaf.stalk a,
      Θ ((pullback.fst pA mZ).stalkHomAt hua c) =
        Ideal.Quotient.mk (maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N)
          ((pullback.fst pA mV).stalkHomAt hwa c) := fun c => RingHom.congr_fun hΘl c
  have hΘsnd : ∀ b : Z.presheaf.stalk zz,
      Θ ((pullback.snd pA mZ).stalkHomAt huz b) =
        quotientPowMap ((pullback.snd pA mV).stalkHomAt hwv) N
          (e (Ideal.Quotient.mk (maximalIdeal (Z.presheaf.stalk zz) ^ N) b)) :=
    fun b => RingHom.congr_fun hΘr b
  have hΘ'fst : ∀ c : A.presheaf.stalk a,
      Θ' ((pullback.fst pA mV).stalkHomAt hwa c) =
        Ideal.Quotient.mk (maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N)
          ((pullback.fst pA mZ).stalkHomAt hua c) := fun c => RingHom.congr_fun hΘ'l c
  have hΘ'snd : ∀ b : V'.presheaf.stalk vv,
      Θ' ((pullback.snd pA mV).stalkHomAt hwv b) =
        quotientPowMap ((pullback.snd pA mZ).stalkHomAt huz) N
          (e.symm (Ideal.Quotient.mk (maximalIdeal (V'.presheaf.stalk vv) ^ N) b)) :=
    fun b => RingHom.congr_fun hΘ'r b
  -- both descend to the truncations
  let θfwd : ((pullback pA mZ).presheaf.stalk uZ ⧸
      maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N) →+*
      ((pullback pA mV).presheaf.stalk wV ⧸
        maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N) :=
    Ideal.Quotient.lift _ Θ fun ξ hξ => eq_zero_of_mem_pow_maximalIdeal hN Θ hΘloc hξ
  let θbwd : ((pullback pA mV).presheaf.stalk wV ⧸
      maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N) →+*
      ((pullback pA mZ).presheaf.stalk uZ ⧸
        maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N) :=
    Ideal.Quotient.lift _ Θ' fun ξ hξ => eq_zero_of_mem_pow_maximalIdeal hN Θ' hΘ'loc hξ
  have hfwd : ∀ ξ : (pullback pA mZ).presheaf.stalk uZ,
      θfwd (Ideal.Quotient.mk (maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N) ξ) =
        Θ ξ := fun ξ => Ideal.Quotient.lift_mk _ _ _
  have hbwd : ∀ ξ : (pullback pA mV).presheaf.stalk wV,
      θbwd (Ideal.Quotient.mk (maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N) ξ) =
        Θ' ξ := fun ξ => Ideal.Quotient.lift_mk _ _ _
  -- the composite out of `𝒪_{A ×_D Z, uZ}` is the quotient map, by uniqueness
  have hZZ : θbwd.comp Θ =
      Ideal.Quotient.mk (maximalIdeal ((pullback pA mZ).presheaf.stalk uZ) ^ N) := by
    refine ringHom_stalk_pullback_ext pA mZ uZ hua huz _ _ (RingHom.ext fun c => ?_)
      (RingHom.ext fun b => ?_)
    · change θbwd (Θ ((pullback.fst pA mZ).stalkHomAt hua c)) = _
      rw [hΘfst c, hbwd, hΘ'fst c]
      rfl
    · obtain ⟨ψ, hψ⟩ := Ideal.Quotient.mk_surjective
        (e (Ideal.Quotient.mk (maximalIdeal (Z.presheaf.stalk zz) ^ N) b))
      change θbwd (Θ ((pullback.snd pA mZ).stalkHomAt huz b)) = _
      rw [hΘsnd b, ← hψ, quotientPowMap_mk, hbwd, hΘ'snd ψ, hψ, e.symm_apply_apply,
        quotientPowMap_mk]
      rfl
  -- and the composite out of `𝒪_{A ×_D V', wV}`
  have hVV : θfwd.comp Θ' =
      Ideal.Quotient.mk (maximalIdeal ((pullback pA mV).presheaf.stalk wV) ^ N) := by
    refine ringHom_stalk_pullback_ext pA mV wV hwa hwv _ _ (RingHom.ext fun c => ?_)
      (RingHom.ext fun b => ?_)
    · change θfwd (Θ' ((pullback.fst pA mV).stalkHomAt hwa c)) = _
      rw [hΘ'fst c, hfwd, hΘfst c]
      rfl
    · obtain ⟨ψ, hψ⟩ := Ideal.Quotient.mk_surjective
        (e.symm (Ideal.Quotient.mk (maximalIdeal (V'.presheaf.stalk vv) ^ N) b))
      change θfwd (Θ' ((pullback.snd pA mV).stalkHomAt hwv b)) = _
      rw [hΘ'snd b, ← hψ, quotientPowMap_mk, hfwd, hΘsnd ψ, hψ, e.apply_symm_apply,
        quotientPowMap_mk]
      rfl
  refine ⟨RingEquiv.ofBijective θfwd
    (Function.bijective_iff_has_inverse.mpr ⟨θbwd, ?_, ?_⟩), fun c => ?_, fun b => ?_⟩
  · intro ρ
    obtain ⟨ξ, hξ⟩ := Ideal.Quotient.mk_surjective ρ
    show θbwd (θfwd ρ) = ρ
    rw [← hξ, hfwd]
    exact RingHom.congr_fun hZZ ξ
  · intro ρ
    obtain ⟨ξ, hξ⟩ := Ideal.Quotient.mk_surjective ρ
    show θfwd (θbwd ρ) = ρ
    rw [← hξ, hbwd]
    exact RingHom.congr_fun hVV ξ
  · change θfwd (Ideal.Quotient.mk _ ((pullback.fst pA mZ).stalkHomAt hua c)) = _
    rw [hfwd, hΘfst c]
  · change θfwd (Ideal.Quotient.mk _ ((pullback.snd pA mZ).stalkHomAt huz b)) = _
    rw [hfwd, hΘsnd b]

/-- The first projection of a base change induces an isomorphism on residue fields at a point
whose second projection does. -/
private lemma pullback_fst_residueFieldMap_isIso_of_snd_residueFieldMap
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor)
    (h : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :
    IsIso ((pullback.fst f g).residueFieldMap (T.SpecTensorTo p)) := by
  have hFromSpec (Z : Scheme.{u}) (z : Z) (q : Spec (Z.residueField z)) :
      IsIso ((Z.fromSpecResidueField z).residueFieldMap q) := by
    have : IsPreimmersion (Z.fromSpecResidueField z) := by
      dsimp only [Scheme.fromSpecResidueField]
      rw [IsPreimmersion.comp_iff]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨((Z.fromSpecResidueField z).residueFieldMap q).hom.injective, ?_⟩
    have hs : Function.Surjective
        ((Z.fromSpecResidueField z).stalkMap q ≫
          (Spec (Z.residueField z)).residue q).hom := by
      rw [CommRingCat.hom_comp]
      exact ((Spec (Z.residueField z)).residue_surjective q).comp
        ((Z.fromSpecResidueField z).stalkMap_surjective q)
    rw [← Scheme.residue_residueFieldMap, CommRingCat.hom_comp, RingHom.coe_comp] at hs
    exact Function.Surjective.of_comp hs
  have hpush : IsPushout
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
      T.tensorInl T.tensorInr := IsPushout.of_hasPushout _ _
  have : IsIso T.tensorInl := hpush.isIso_inl_of_isIso h
  have : IsIso (Spec.map T.tensorInl) := inferInstance
  have hpoint : (T.SpecTensorTo ≫ pullback.fst f g) p =
      (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x) p := by
    rw [T.specTensorTo_fst]
  have hcongr : IsIso (X.residueFieldCongr hpoint).hom :=
    (X.residueFieldCongr hpoint).isIso_hom
  have hbase : IsIso
      ((pullback.fst f g).residueFieldMap (T.SpecTensorTo p) ≫
        T.SpecTensorTo.residueFieldMap p) := by
    rw [← Scheme.residueFieldMap_comp]
    rw [Scheme.Hom.residueFieldMap_congr T.specTensorTo_fst p]
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hcongr
      (IsIso.comp_isIso' (hFromSpec X T.x (Spec.map T.tensorInl p)) inferInstance)
  have hTensor : IsIso (T.SpecTensorTo.residueFieldMap p) := by
    have hcomp :=
      AlgebraicGeometry.Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso
        T p
    have : IsIso ((Scheme.Spec.residueFieldIso T.tensor p).hom) := inferInstance
    have : IsIso (T.SpecTensorTo.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso T.tensor p).hom) := hcomp
    exact IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso T.tensor p).hom
  let := hTensor
  let := hbase
  exact IsIso.of_isIso_comp_right _ (T.SpecTensorTo.residueFieldMap p)

/-- The first projection of a base change induces an isomorphism on residue fields at any point
at which the second projection does. -/
private lemma isIso_residueFieldMap_pullback_fst
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : (pullback f g : Scheme.{u}))
    [hIso : IsIso (g.residueFieldMap (pullback.snd f g z))] :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  have h : IsIso ((S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint z).hy).inv ≫
      g.residueFieldMap (Scheme.Pullback.Triplet.ofPoint z).y) := by
    change IsIso ((S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint z).hy).inv ≫
      g.residueFieldMap (pullback.snd f g z))
    exact IsIso.comp_isIso'
      (S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint z).hy).isIso_inv hIso
  have H := pullback_fst_residueFieldMap_isIso_of_snd_residueFieldMap f g
    (Scheme.Pullback.Triplet.ofPoint z) (Scheme.Pullback.SpecOfPoint z) h
  rwa [Scheme.Pullback.SpecTensorTo_SpecOfPoint (f := f) (g := g) z] at H

/-- A point of a base change above a prescribed pair of points, at which the first projection
induces an isomorphism on residue fields. -/
private lemma exists_pullback_point_with_fst_residueFieldMap_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) (y : Y) (hxy : f x = g y)
    (h : IsIso ((S.residueFieldCongr hxy.symm).inv ≫ g.residueFieldMap y)) :
    ∃ z : (pullback f g : Scheme.{u}), pullback.fst f g z = x ∧ pullback.snd f g z = y ∧
      IsIso ((pullback.fst f g).residueFieldMap z) := by
  obtain ⟨z, hzX, hzY⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  have hT : IsIso ((S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint z).hy).inv ≫
      g.residueFieldMap (Scheme.Pullback.Triplet.ofPoint z).y) := by
    have : IsIso ((S.residueFieldCongr hxy.symm).inv ≫ g.residueFieldMap y) := h
    have hyIso : IsIso (g.residueFieldMap y) :=
      IsIso.of_isIso_comp_left ((S.residueFieldCongr hxy.symm).inv) (g.residueFieldMap y)
    have : IsIso (g.residueFieldMap (Scheme.Pullback.Triplet.ofPoint z).y) := by
      change IsIso (g.residueFieldMap (pullback.snd f g z))
      rw [hzY]
      exact hyIso
    infer_instance
  have hres := pullback_fst_residueFieldMap_isIso_of_snd_residueFieldMap f g
    (Scheme.Pullback.Triplet.ofPoint z) (Scheme.Pullback.SpecOfPoint z) hT
  refine ⟨z, hzX, hzY, ?_⟩
  rwa [Scheme.Pullback.SpecTensorTo_SpecOfPoint (f := f) (g := g) z] at hres

/-- A morphism which is surjective on stalks induces isomorphisms on residue fields. -/
private alias isIso_residueFieldMap_of_surjectiveOnStalks :=
  AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks

/-- The canonical morphism from the spectrum of a local ring of a scheme is flat. -/
@[ega "IV 20.3.6" "partial"]
private lemma flat_fromSpecStalk (S : Scheme.{u}) (s : S) : Flat (S.fromSpecStalk s) := by
  let V : S.Opens := (S.affineCover.f (S.affineCover.idx s)).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange (S.affineCover.f (S.affineCover.idx s))
  have hsV : s ∈ V := Scheme.Hom.mem_opensRange.mpr (S.affineCover.covers s)
  change Flat (Spec.map (S.presheaf.germ V s hsV) ≫ hV.fromSpec)
  have h1 : Flat (Spec.map (S.presheaf.germ V s hsV)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(S, V) (S.presheaf.stalk s) := (S.presheaf.germ V s hsV).hom.toAlgebra
    have := hV.isLocalization_stalk ⟨s, hsV⟩
    change RingHom.Flat (algebraMap Γ(S, V) (S.presheaf.stalk s))
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (S.presheaf.stalk s)
        ((hV.primeIdealOf ⟨s, hsV⟩).asIdeal.primeCompl))
  infer_instance

/-! ### Completions of local rings -/

/-- Transposing a factorisation through a ring isomorphism. -/
private lemma ringEquiv_symm_comp_of_comp_eq {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] (e : A ≃+* B) (f : R →+* A) (g : R →+* B)
    (h : e.toRingHom.comp f = g) : e.symm.toRingHom.comp g = f := by
  ext r
  have hr := congrArg (fun k : R →+* B => k r) h
  simpa using (congrArg e.symm hr).symm

/-- The completion of a local G-ring at its maximal ideal is again a G-ring. -/
private lemma completion_isGRing (R : Type v) [CommRing R] [IsLocalRing R]
    (hG : IsGRing R) : IsGRing (AdicCompletion (maximalIdeal R) R) := by
  have : IsNoetherianRing R := hG.1
  exact isGRing_of_isPrecomplete_maximalIdeal _

/-- Being a G-ring transports along a ring isomorphism. -/
private lemma isGRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hA : IsGRing A) : IsGRing B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let f : A →ₐ[A] B := { toRingHom := e.toRingHom, commutes' := fun _ ↦ rfl }
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_surjective f e.surjective
  let : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_finiteType A B
  exact isGRing_of_essFiniteType hA

/-- A flat local homomorphism of local rings with finitely generated maximal ideal which
generates the maximal ideal of the target and is bijective on residue fields induces an
isomorphism of completions. -/
private lemma completion_ringEquiv_of_flat_local_hom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hfg : (maximalIdeal A).FG)
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B))) :
    ∃ e : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B,
      ∀ a : A,
        e (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
          algebraMap B (AdicCompletion (maximalIdeal B) B) (algebraMap A B a) :=
  exists_adicCompletion_ringEquiv_of_flat hfg hmax hres

/-- Two maps of completions of Noetherian local rings which agree on the image of the source
ring and carry the maximal ideal into the maximal ideal are equal. -/
private lemma adicCompletion_ringHom_ext {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f g : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    (hf : Ideal.map f (maximalIdeal (AdicCompletion (maximalIdeal A) A)) ≤
      maximalIdeal (AdicCompletion (maximalIdeal B) B))
    (hg : Ideal.map g (maximalIdeal (AdicCompletion (maximalIdeal A) A)) ≤
      maximalIdeal (AdicCompletion (maximalIdeal B) B))
    (h : f.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      g.comp (algebraMap A (AdicCompletion (maximalIdeal A) A))) : f = g := by
  have hHaus : IsHausdorff (maximalIdeal (AdicCompletion (maximalIdeal B) B))
    (AdicCompletion (maximalIdeal B) B) := inferInstance
  apply RingHom.ext
  intro x
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal (AdicCompletion (maximalIdeal B) B))]
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
  have hxa : x - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n := by
    rw [← ker_evalₐ_eq_pow_maximalIdeal A n, RingHom.mem_ker]
    change AdicCompletion.evalₐ (maximalIdeal A) n
      (x - algebraMap A (AdicCompletion (maximalIdeal A) A) a) = 0
    rw [map_sub, ← ha]
    change (Ideal.Quotient.mk _ a) -
      AdicCompletion.evalₐ (maximalIdeal A) n (AdicCompletion.of _ A a) = 0
    rw [AdicCompletion.evalₐ_of, sub_self]
  have hfb : Ideal.map f (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) ≤
      maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hf n
  have hgb : Ideal.map g (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) ≤
      maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hg n
  have hfx : f x - f (algebraMap A (AdicCompletion (maximalIdeal A) A) a) ∈
      maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ n := by
    simpa only [map_sub] using hfb (Ideal.mem_map_of_mem f hxa)
  have hgx : g x - g (algebraMap A (AdicCompletion (maximalIdeal A) A) a) ∈
      maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ n := by
    simpa only [map_sub] using hgb (Ideal.mem_map_of_mem g hxa)
  have hmid : f (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      g (algebraMap A (AdicCompletion (maximalIdeal A) A) a) :=
    congrArg (fun k : A →+* AdicCompletion (maximalIdeal B) B => k a) h
  apply Ideal.Quotient.eq.mpr
  have hsub : f x - g x ∈ maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ n := by
    have hright : g (algebraMap A (AdicCompletion (maximalIdeal A) A) a) - g x ∈
        maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ n := by
      simpa only [sub_eq_add_neg, neg_add_rev, neg_neg] using (neg_mem hgx)
    simpa [hmid, sub_eq_add_neg, add_assoc] using Ideal.add_mem _ hfx hright
  simpa [Ideal.smul_top_eq_map] using hsub

/-! ### Descending an étale pair along a cofiltered limit -/

/-- The terminal scheme is locally Noetherian. -/
private lemma isLocallyNoetherian_terminal : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact isLocallyNoetherian_of_isOpenImmersion
    (terminalIsTerminal.uniqueUpToIso (specULiftZIsTerminal.{u})).hom

/-- A morphism from the limit of a cofiltered system of qcqs schemes with affine transition
morphisms over a base `B` into a scheme locally of finite presentation over `B` factors through
a finite stage, by a morphism which is itself over `B`. -/
private lemma exists_factorization_over_base_finitePresentation
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {T B : Scheme.{u}} (hTB : T ⟶ B) [LocallyOfFinitePresentation hTB]
    (t : D ⟶ (Functor.const I).obj B) (a : c.pt ⟶ T)
    (ha : c.π ≫ t = (Functor.const _).map (a ≫ hTB)) :
    ∃ (i : I) (g : D.obj i ⟶ T), c.π.app i ≫ g = a ∧ g ≫ hTB = t.app i :=
  Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t hTB c hc a ha

/-- Transporting a base change along an equality of the base morphisms. -/
private def overPullbackCongr {B C : Scheme.{u}} {f g : B ⟶ C} (h : f = g) (A : Over C) :
    (Over.pullback f).obj A ≅ (Over.pullback g).obj A := by
  cases h
  exact Iso.refl _

/-- Base changing twice along a factorisation `a ≫ g = b` is base changing once along `b`. -/
private def pullbackTransitionIso {B C Z : Scheme.{u}} (g : C ⟶ B)
    (a : Z ⟶ C) (b : Z ⟶ B) (h : a ≫ g = b) (A : Over B) :
    (Over.pullback a).obj ((Over.pullback g).obj A) ≅ (Over.pullback b).obj A :=
  h ▸ Over.isoMk (pullbackLeftPullbackSndIso A.hom g a) (by simp)

/-- The first projection of `pullbackTransitionIso`. -/
private lemma pullbackTransitionIso_hom_fst {B C Z : Scheme.{u}} (g : C ⟶ B)
    (a : Z ⟶ C) (b : Z ⟶ B) (h : a ≫ g = b) (A : Over B) :
    (pullbackTransitionIso g a b h A).hom.left ≫ pullback.fst A.hom b =
      pullback.fst ((Over.pullback g).obj A).hom a ≫ pullback.fst A.hom g := by
  subst h
  exact pullbackLeftPullbackSndIso_hom_fst A.hom g a

/-- The first projection of the inverse of `pullbackTransitionIso`. -/
private lemma pullbackTransitionIso_inv_fst {B C Z : Scheme.{u}} (g : C ⟶ B)
    (a : Z ⟶ C) (b : Z ⟶ B) (h : a ≫ g = b) (A : Over B) :
    (pullbackTransitionIso g a b h A).inv.left ≫
      pullback.fst ((Over.pullback g).obj A).hom a ≫ pullback.fst A.hom g =
        pullback.fst A.hom b := by
  rw [← pullbackTransitionIso_hom_fst g a b h A, ← Category.assoc]
  simp

/-- Étaleness of a morphism of base changes descends through the comparison isomorphism of
`pullbackTransitionIso`. -/
private lemma etale_pullback_map_of_projection {B C Z : Scheme.{u}}
    (g : C ⟶ B) (a : Z ⟶ C) (b : Z ⟶ B) (h : a ≫ g = b)
    (A X : Over B) (f : (Over.pullback b).obj A ⟶ (Over.pullback b).obj X)
    (f' : (Over.pullback g).obj A ⟶ (Over.pullback g).obj X)
    (e : (Over.pullback a).obj ((Over.pullback g).obj A) ≅ (Over.pullback b).obj A)
    (heq : e.hom.left ≫ f.left ≫ pullback.fst X.hom b =
      pullback.fst ((Over.pullback g).obj A).hom a ≫ f'.left ≫ pullback.fst X.hom g)
    [Etale f.left] : Etale ((Over.pullback a).map f').left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget Z).map e.hom))
  have : IsIso (pullbackTransitionIso g a b h X).inv.left :=
    inferInstanceAs (IsIso ((Over.forget Z).map (pullbackTransitionIso g a b h X).inv))
  have H : ((Over.pullback a).map f').left ≫ (pullbackTransitionIso g a b h X).hom.left =
      e.hom.left ≫ f.left := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullbackTransitionIso_hom_fst,
        Over.pullback_map_left, pullback.lift_fst_assoc] using heq.symm
    · change _ ≫ ((Over.pullback b).obj X).hom = _ ≫ ((Over.pullback b).obj X).hom
      simp only [Category.assoc, Over.w]
  have H' : ((Over.pullback a).map f').left =
      e.hom.left ≫ f.left ≫ (pullbackTransitionIso g a b h X).inv.left := by
    rw [← Category.assoc, ← H, Category.assoc]
    simp
  rw [H']
  infer_instance

/-- Finite presentation is stable under base change. -/
private lemma finitePresentation_pullback {B C : Scheme.{u}} (g : C ⟶ B)
    (A : Over B) (hA : AlgebraicGeometry.FinitePresentation A.hom) :
    AlgebraicGeometry.FinitePresentation ((Over.pullback g).obj A).hom := by
  let := hA.1
  let := hA.2.1
  let := hA.2.2
  change AlgebraicGeometry.FinitePresentation (pullback.snd A.hom g)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A pair of morphisms out of a common finitely presented base change over the limit descends
to a finite stage, étaleness of each leg descending with it.

Only the second leg is required to be étale. The first leg's étaleness is not used to produce
the stage — the stage comes from `AlgebraicGeometry.exists_morphism_after_baseChange`, which
knows nothing of étaleness — so it is returned as an implication instead of being assumed. Tag
0GDX, whose two legs are both étale, supplies it; Tag 0CAW, whose first leg is the morphism to
`X` that Tag 0CAU produces and which is not étale, does not. -/
private lemma exists_span_model_of_etale_snd
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (A X Y : Over (D.obj i))
    (hA : AlgebraicGeometry.FinitePresentation A.hom)
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    (hY : AlgebraicGeometry.FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj X)
    (g : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj Y)
    [Etale g.left] :
    ∃ (j : I) (e : j ⟶ i)
      (f' : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj X)
      (g' : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj A) ≅
        (Over.pullback (c.π.app i)).obj A),
      α.hom.left ≫ pullback.fst A.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
          pullback.fst A.hom (D.map e) ∧
      α.hom.left ≫ f.left ≫ pullback.fst X.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
          f'.left ≫ pullback.fst X.hom (D.map e) ∧
      α.hom.left ≫ g.left ≫ pullback.fst Y.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
          g'.left ≫ pullback.fst Y.hom (D.map e) ∧
      (Etale f.left → Etale ((Over.pullback (c.π.app j)).map f').left) ∧
      Etale ((Over.pullback (c.π.app j)).map g').left := by
  let P : Over (D.obj i) := Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)
  let px : P ⟶ X := Over.homMk (pullback.fst X.hom Y.hom) rfl
  let py : P ⟶ Y := Over.homMk (pullback.snd X.hom Y.hom) pullback.condition.symm
  let := hX.1
  let := hX.2.1
  let := hX.2.2
  let := hY.1
  let := hY.2.1
  let := hY.2.2
  have hP : AlgebraicGeometry.FinitePresentation P.hom := by
    dsimp [P]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let F : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj P :=
    Over.homMk (pullback.lift
      (pullback.lift (f.left ≫ pullback.fst X.hom (c.π.app i))
        (g.left ≫ pullback.fst Y.hom (c.π.app i)) (by
          simp only [Category.assoc, pullback.condition]
          exact congrArg (· ≫ c.π.app i) ((Over.w f).trans (Over.w g).symm)))
      ((Over.pullback (c.π.app i)).obj A).hom (by
        dsimp [P]
        rw [pullback.lift_fst_assoc, Category.assoc, pullback.condition]
        exact congrArg (· ≫ c.π.app i) (Over.w f)))
      (pullback.lift_snd _ _ _)
  have hFx : F.left ≫ pullback.fst P.hom (c.π.app i) ≫ px.left =
      f.left ≫ pullback.fst X.hom (c.π.app i) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ px.left) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _))
  have hFy : F.left ≫ pullback.fst P.hom (c.π.app i) ≫ py.left =
      g.left ≫ pullback.fst Y.hom (c.π.app i) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ py.left) (pullback.lift_fst _ _ _)).trans (pullback.lift_snd _ _ _))
  obtain ⟨j, e, F', α, β, hα, hβ, hF⟩ :=
    AlgebraicGeometry.exists_morphism_after_baseChange D c hc i A P hA hP F
  let f' := F' ≫ (Over.pullback (D.map e)).map px
  let g' := F' ≫ (Over.pullback (D.map e)).map py
  have hproj : α.hom.left ≫ F.left ≫ pullback.fst P.hom (c.π.app i) =
      pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
        F'.left ≫ pullback.fst P.hom (D.map e) := by
    have hh := congrArg (fun k => k.left ≫ pullback.fst P.hom (c.π.app i)) hF
    simpa only [Over.comp_left, Category.assoc, hβ, Over.pullback_map_left,
      pullback.lift_fst_assoc] using hh
  have hfx : α.hom.left ≫ f.left ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
        f'.left ≫ pullback.fst X.hom (D.map e) := by
    simpa only [Category.assoc, hFx, f', Over.comp_left, Over.pullback_map_left,
      pullback.lift_fst] using congrArg (· ≫ px.left) hproj
  have hgy : α.hom.left ≫ g.left ≫ pullback.fst Y.hom (c.π.app i) =
      pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
        g'.left ≫ pullback.fst Y.hom (D.map e) := by
    simpa only [Category.assoc, hFy, g', Over.comp_left, Over.pullback_map_left,
      pullback.lift_fst] using congrArg (· ≫ py.left) hproj
  exact ⟨j, e, f', g', α, hα, hfx, hgy,
    fun hfe => by
      have := hfe
      exact etale_pullback_map_of_projection (D.map e) _ _ (c.w e) A X f f' α hfx,
    etale_pullback_map_of_projection (D.map e) _ _ (c.w e) A Y g g' α hgy⟩

/-- A pair of étale morphisms out of a common finitely presented base change over the limit
descends to a finite stage. This is
`StacksDraft.ArtinApproximation.exists_span_model_of_etale_snd` read for a first leg which is
étale to begin with, so that its conclusion about the descended first leg is unconditional. -/
private lemma exists_span_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (A X Y : Over (D.obj i))
    (hA : AlgebraicGeometry.FinitePresentation A.hom)
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    (hY : AlgebraicGeometry.FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj X)
    (g : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj Y)
    [Etale f.left] [Etale g.left] :
    ∃ (j : I) (e : j ⟶ i)
      (f' : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj X)
      (g' : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj A) ≅
        (Over.pullback (c.π.app i)).obj A),
      α.hom.left ≫ pullback.fst A.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
          pullback.fst A.hom (D.map e) ∧
      α.hom.left ≫ f.left ≫ pullback.fst X.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
          f'.left ≫ pullback.fst X.hom (D.map e) ∧
      α.hom.left ≫ g.left ≫ pullback.fst Y.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app j) ≫
          g'.left ≫ pullback.fst Y.hom (D.map e) ∧
      Etale ((Over.pullback (c.π.app j)).map f').left ∧
      Etale ((Over.pullback (c.π.app j)).map g').left := by
  obtain ⟨j, e, f', g', α, hα, hfx, hgy, hfe, hge⟩ :=
    exists_span_model_of_etale_snd D c hc i A X Y hA hX hY f g
  exact ⟨j, e, f', g', α, hα, hfx, hgy, hfe inferInstance, hge⟩

/-- Étaleness of a base-changed morphism is inherited by a further base change. -/
private lemma etale_pullback_comp {B C E : Scheme.{u}} (a : C ⟶ B) (b : E ⟶ C)
    {X Y : Over B} (f : X ⟶ Y) [Etale ((Over.pullback a).map f).left] :
    Etale ((Over.pullback (b ≫ a)).map f).left := by
  have h : ((Over.pullback (b ≫ a)).map f).left ≫ ((Over.pullbackComp b a).app Y).hom.left =
      ((Over.pullbackComp b a).app X).hom.left ≫
        ((Over.pullback b).map ((Over.pullback a).map f)).left :=
    congrArg (fun k => k.left) ((Over.pullbackComp b a).hom.naturality f)
  have : Etale ((Over.pullback b).map ((Over.pullback a).map f)).left :=
    MorphismProperty.overPullbackMap b _ inferInstance
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsIso ((Over.pullbackComp b a).app Y).hom.left :=
    inferInstanceAs (IsIso ((Over.forget E).map ((Over.pullbackComp b a).app Y).hom))
  have : IsIso ((Over.pullbackComp b a).app X).hom.left :=
    inferInstanceAs (IsIso ((Over.forget E).map ((Over.pullbackComp b a).app X).hom))
  apply (MorphismProperty.cancel_right_of_respectsIso @Etale _
    ((Over.pullbackComp b a).app Y).hom.left).mp
  rw [h]
  infer_instance

/-- A pair of morphisms at one stage which become étale over the limit is étale at some later
stage. -/
private lemma exists_etale_pair_pullback
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (A X Y : Over (D.obj i)) (f : A ⟶ X) (g : A ⟶ Y)
    [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    [LocallyOfFinitePresentation f.left] [LocallyOfFinitePresentation g.left]
    [Etale ((Over.pullback (c.π.app i)).map f).left]
    [Etale ((Over.pullback (c.π.app i)).map g).left] :
    ∃ (j : I) (e : j ⟶ i), Etale ((Over.pullback (D.map e)).map f).left ∧
      Etale ((Over.pullback (D.map e)).map g).left := by
  obtain ⟨r, hr⟩ := AlgebraicGeometry.exists_etale_pullback_of_isLimit D c hc i A X f
  obtain ⟨s, hs⟩ := AlgebraicGeometry.exists_etale_pullback_of_isLimit D c hc i A Y g
  obtain ⟨t, tr, ts, _⟩ := IsCofilteredOrEmpty.cone_objs r s
  refine ⟨t.left, t.hom, ?_, ?_⟩
  · have := hr
    have H := etale_pullback_comp (D.map r.hom) (D.map tr.left) f
    have he : D.map tr.left ≫ D.map r.hom = D.map t.hom :=
      (D.map_comp _ _).symm.trans (congrArg D.map (Over.w tr))
    rwa [he] at H
  · have := hs
    have H := etale_pullback_comp (D.map s.hom) (D.map ts.left) g
    have he : D.map ts.left ≫ D.map s.hom = D.map t.hom :=
      (D.map_comp _ _).symm.trans (congrArg D.map (Over.w ts))
    rwa [he] at H

/-- A morphism out of a quasi-compact scheme factors through a quasi-compact open of the
target. -/
private lemma exists_quasiCompact_open_factorization {A X : Scheme.{u}}
    [CompactSpace A] (f : A ⟶ X) :
    ∃ (U : X.Opens) (g : A ⟶ U.toScheme), CompactSpace U.toScheme ∧ g ≫ U.ι = f := by
  classical
  have hcover : Set.range f ⊆ ⋃ i : X.affineOpens, (i.1 : Set X) := by
    rw [← TopologicalSpace.Opens.coe_iSup, iSup_affineOpens_eq_top]
    exact Set.subset_univ _
  obtain ⟨s, hs⟩ := (isCompact_range f.continuous).elim_finite_subcover
    (fun i : X.affineOpens => (i.1 : Set X)) (fun i => i.1.isOpen) hcover
  have hc : IsCompact ((⨆ i ∈ s, (i : X.affineOpens).1 : X.Opens) : Set X) := by
    simpa only [TopologicalSpace.Opens.coe_iSup] using
      s.isCompact_biUnion (fun i _ => i.2.isCompact)
  have hr : Set.range f ⊆ Set.range (⨆ i ∈ s, (i : X.affineOpens).1 : X.Opens).ι := by
    simpa only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_iSup] using hs
  exact ⟨_, IsOpenImmersion.lift _ f hr, isCompact_iff_compactSpace.mp hc,
    IsOpenImmersion.lift_fac _ _ _⟩

/-! ### Tag 0GDX: the full approximation diagram -/

/-- The morphism `Spec 𝒪^∧_{S, s} ⟶ T` determined by a local homomorphism
`σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`. Its base change of `Y ⟶ T` is the scheme `Y_σ` of Tag 0GDX. -/
abbrev relativeBaseChangeMorphism {S T : Scheme.{u}} (s : S) {t : T}
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) :
    specCompletedStalk S s ⟶ T :=
  Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t

/-- The closed point of `Spec 𝒪^∧_{S, s}` lies over `s`. -/
theorem specCompletedStalkTo_specCompletedStalkPoint (S : Scheme.{u}) [IsLocallyNoetherian S]
    (s : S) : specCompletedStalkTo S s (specCompletedStalkPoint S s) = s := by
  exact fromSpecStalk_specMap_closedPoint _

/-- The closed point of `Spec 𝒪^∧_{S, s}` is carried to `t` by the morphism attached to a local
homomorphism `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`. -/
theorem relativeBaseChangeMorphism_specCompletedStalkPoint {S T : Scheme.{u}}
    [IsLocallyNoetherian S] (s : S) {t : T}
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    [IsLocalHom σ] :
    relativeBaseChangeMorphism s σ (specCompletedStalkPoint S s) = t := by
  exact fromSpecStalk_specMap_closedPoint σ

/-- For `h : T ⟶ S` carrying `t` to `s`, the morphism `Spec 𝒪^∧_{S, s} ⟶ T` attached to a local
homomorphism `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` lies over `S` as soon as `σ` is a map of
`𝒪_{S, s}`-algebras. This is the compatibility over the base `S` which the setting of Tag 0CAW
provides. -/
theorem relativeBaseChangeMorphism_comp {S T : Scheme.{u}} (h : T ⟶ S) {t : T} {s : S}
    (hts : h t = s)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσbase : σ.comp (h.stalkHomAt hts) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) :
    relativeBaseChangeMorphism s σ ≫ h = specCompletedStalkTo S s := by
  subst hts
  have hring : h.stalkMap t ≫ CommRingCat.ofHom σ =
      CommRingCat.ofHom (algebraMap (S.presheaf.stalk (h t))
        (AdicCompletion (maximalIdeal (S.presheaf.stalk (h t))) (S.presheaf.stalk (h t)))) := by
    rw [← hσbase, stalkHomAt_rfl]
    rfl
  calc relativeBaseChangeMorphism (h t) σ ≫ h
      = Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t ≫ h := by
        simp only [relativeBaseChangeMorphism, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (h.stalkMap t) ≫ S.fromSpecStalk (h t) :=
        congrArg (Spec.map (CommRingCat.ofHom σ) ≫ ·)
          (Scheme.SpecMap_stalkMap_fromSpecStalk h (x := t)).symm
    _ = (Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (h.stalkMap t)) ≫ S.fromSpecStalk (h t) :=
        (Category.assoc _ _ _).symm
    _ = specCompletedStalkTo S (h t) :=
        congrArg (· ≫ S.fromSpecStalk (h t))
          ((Spec.map_comp (h.stalkMap t) (CommRingCat.ofHom σ)).symm.trans
            (congrArg Spec.map hring))

/-- **Tag 0CAV in the `stalkHomAt` spelling.** Tag 0CAV with the two compatibilities
read as maps out of the local ring at a common image point, rather than at the image of `x`. -/
private theorem exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv_at
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (y : Y) {s : S} (hxs : f x = s) (hys : g y = s)
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (Φ : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hΦ : Φ.toRingHom.comp ((algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))).comp
          (g.stalkHomAt hys)) =
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (f.stalkHomAt hxs)) :
    ∃ (U : EtaleNeighborhood X x) (c : U.scheme ⟶ Y) (hcEt : Etale c) (hc : c U.point = y),
      U.IsElementary ∧ (U.along c hcEt hc).IsElementary ∧ c ≫ g = U.toBase ≫ f ∧
        ∀ w : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y),
          @HSub.hSub _ _ _ instHSub (U.completionMap (Φ w))
              ((U.along c hcEt hc).completionMap w) ∈
            Ideal.map (algebraMap (U.scheme.presheaf.stalk U.point)
              (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
                (U.scheme.presheaf.stalk U.point)))
              (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N) := by
  subst hxs
  refine exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv
    f g x y hys.symm hG N hN Φ ?_
  refine hΦ.trans (congrArg ((algebraMap (X.presheaf.stalk x)
    (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp) ?_)
  change (((S.presheaf.stalkCongr (.of_eq (rfl : f x = f x))).hom ≫
    f.stalkMap x)).hom = _
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]

/-- The completion map `𝒪_{S, s} → 𝒪^∧_{S, s}`, read as the local homomorphism attached to
`Spec 𝒪^∧_{S, s} ⟶ S` at the closed point, through the identification of the stalk of
`Spec 𝒪^∧_{S, s}` at its closed point with `𝒪^∧_{S, s}`. -/
private theorem stalkHomAt_specCompletedStalkTo (S : Scheme.{u}) [IsLocallyNoetherian S]
    (s : S) :
    (specCompletedStalkTo S s).stalkHomAt
        (specCompletedStalkTo_specCompletedStalkPoint S s) =
      (stalkClosedPointIso (CommRingCat.of
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
            (S.presheaf.stalk s)))).inv.hom.comp
        (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) := by
  have : IsLocalHom (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
  set e := stalkClosedPointIso (CommRingCat.of
    (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) with he
  set hap := specCompletedStalkTo_specCompletedStalkPoint S s with hhap
  have hid : Scheme.stalkClosedPointTo (𝟙 (specCompletedStalk S s)) = e.hom :=
    (congrArg (fun k => k ≫ e.hom)
        (Scheme.Hom.stalkMap_id (specCompletedStalk S s)
          (specCompletedStalkPoint S s))).trans (Category.id_comp e.hom)
  have h : e.hom.hom.comp ((specCompletedStalkTo S s).stalkHomAt hap) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) := by
    rw [← hid]
    exact stalkClosedPointTo_comp_stalkHomAt (𝟙 (specCompletedStalk S s))
      (specCompletedStalkTo S s)
      (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
      (Category.id_comp _) hap
  have hid' : e.inv.hom.comp e.hom.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, e.hom_inv_id]
    rfl
  calc (specCompletedStalkTo S s).stalkHomAt hap
      = (RingHom.id _).comp ((specCompletedStalkTo S s).stalkHomAt hap) :=
        (RingHom.id_comp _).symm
    _ = (e.inv.hom.comp e.hom.hom).comp ((specCompletedStalkTo S s).stalkHomAt hap) := by
        rw [hid']
    _ = e.inv.hom.comp (e.hom.hom.comp ((specCompletedStalkTo S s).stalkHomAt hap)) :=
        RingHom.comp_assoc _ _ _
    _ = e.inv.hom.comp (algebraMap _ _) := by rw [h]

/-- **The isomorphism `φ` transported to the base change of `X` along `Spec 𝒪^∧_{S, s} ⟶ S`.**
Let `x ∈ X` lie over `s`, let `W` be a scheme locally of finite type over `Spec 𝒪^∧_{S, s}` and
let `w ∈ W` lie over the closed point. An isomorphism `φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{W, w}` of
`𝒪_{S, s}`-algebras then yields a point `x_σ` of `X ×_S Spec 𝒪^∧_{S, s}` over `x` and over the
closed point, at which the first projection induces an isomorphism on residue fields, and an
isomorphism `𝒪^∧_{W, w} ≅ 𝒪^∧_{X_σ, x_σ}` compatible with the two maps from the local ring of
`Spec 𝒪^∧_{S, s}` at the closed point.

The point is that `𝒪_{X, x} → 𝒪_{X_σ, x_σ}` is flat, generates the maximal ideal and is
bijective on residue fields, so it induces an isomorphism of completions. This puts the data of
Tag 0GDX into the shape in which Tag 0CAV consumes it, over the base `Spec 𝒪^∧_{S, s}`. -/
private theorem exists_point_and_ringEquiv_pullback_completedStalk
    {X S W : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) [LocallyOfFiniteType p]
    {x : X} {s : S} (hx : p x = s) (hG : IsGRing (S.presheaf.stalk s))
    (gW : W ⟶ specCompletedStalk S s) [LocallyOfFiniteType gW]
    (w : W) (hw : gW w = specCompletedStalkPoint S s)
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal (W.presheaf.stalk w)) (W.presheaf.stalk w))
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (p.stalkHomAt hx)) =
      (algebraMap (W.presheaf.stalk w)
          (AdicCompletion (maximalIdeal (W.presheaf.stalk w)) (W.presheaf.stalk w))).comp
        ((gW.stalkHomAt hw).comp ((specCompletedStalkTo S s).stalkHomAt
          (specCompletedStalkTo_specCompletedStalkPoint S s)))) :
    ∃ (xσ : (pullback p (specCompletedStalkTo S s) : Scheme.{u}))
      (hxσX : pullback.fst p (specCompletedStalkTo S s) xσ = x)
      (hxσZ : pullback.snd p (specCompletedStalkTo S s) xσ = specCompletedStalkPoint S s),
      IsIso ((pullback.fst p (specCompletedStalkTo S s)).residueFieldMap xσ) ∧
      ∃ Φ : AdicCompletion (maximalIdeal (W.presheaf.stalk w)) (W.presheaf.stalk w) ≃+*
          AdicCompletion
            (maximalIdeal ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
            ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ),
        (Φ.toRingHom.comp ((algebraMap (W.presheaf.stalk w)
            (AdicCompletion (maximalIdeal (W.presheaf.stalk w))
              (W.presheaf.stalk w))).comp (gW.stalkHomAt hw)) =
          (algebraMap ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)
              (AdicCompletion
                (maximalIdeal ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
                ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))).comp
            ((pullback.snd p (specCompletedStalkTo S s)).stalkHomAt hxσZ)) ∧
        ∀ b : X.presheaf.stalk x,
          Φ (φ (algebraMap (X.presheaf.stalk x)
              (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) b)) =
            algebraMap ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)
              (AdicCompletion
                (maximalIdeal ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
                ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
              ((pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hxσX b) := by
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have hGhat := completion_isGRing (S.presheaf.stalk s) hG
  have : IsNoetherianRing (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)) := hGhat.1
  have : IsIso ((specCompletedStalkTo S s).residueFieldMap (specCompletedStalkPoint S s)) :=
    isIso_residueFieldMap_specCompletedStalkTo S s
  have hxy : p x = specCompletedStalkTo S s (specCompletedStalkPoint S s) :=
    hx.trans (specCompletedStalkTo_specCompletedStalkPoint S s).symm
  obtain ⟨xσ, hxσX, hxσZ, hfstRes⟩ :=
    exists_pullback_point_with_fst_residueFieldMap_isIso p (specCompletedStalkTo S s) x
      (specCompletedStalkPoint S s) hxy inferInstance
  refine ⟨xσ, hxσX, hxσZ, hfstRes, ?_⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have : IsLocallyNoetherian (specCompletedStalk S s) := inferInstance
  have : IsLocallyNoetherian (pullback p (specCompletedStalkTo S s)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (specCompletedStalkTo S s))
  have : IsNoetherianRing ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) :=
    inferInstance
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian gW
  have : IsNoetherianRing (W.presheaf.stalk w) := inferInstance
  -- the local homomorphism `𝒪_{X, x} → 𝒪_{X_σ, x_σ}`
  let : Algebra (X.presheaf.stalk x)
      ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) :=
    ((pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hxσX).toAlgebra
  have halg : algebraMap (X.presheaf.stalk x)
      ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) =
      (pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hxσX := rfl
  have : IsLocalHom (algebraMap (X.presheaf.stalk x)
      ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)) := by
    rw [halg]
    infer_instance
  -- it is bijective on residue fields
  have hSigmaResidue : Function.Bijective (ResidueField.map
      (algebraMap (X.presheaf.stalk x)
        ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))) :=
    (bijective_residueField_map_stalkHomAt_iff _ _ hxσX).mpr hfstRes
  -- it is flat
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))) := by
    rw [Flat.SpecMap_iff]
    change RingHom.Flat (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    exact RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)
  have : Flat (specCompletedStalkTo S s) := by
    have : Flat (S.fromSpecStalk s) := flat_fromSpecStalk S s
    infer_instance
  have : Module.Flat (X.presheaf.stalk x)
      ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) := by
    apply RingHom.flat_algebraMap_iff.mp
    rw [halg]
    change RingHom.Flat
      (((pullback.fst p (specCompletedStalkTo S s)).stalkMap xσ).hom.comp
        ((X.presheaf.stalkCongr (.of_eq hxσX.symm)).hom).hom)
    exact .comp (.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (Flat.stalkMap (pullback.fst p (specCompletedStalkTo S s)) xσ)
  -- it generates the maximal ideal
  have hSigmaMax : (maximalIdeal (X.presheaf.stalk x)).map
      (algebraMap (X.presheaf.stalk x)
        ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)) =
      maximalIdeal ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) := by
    have hm := maximalIdeal_map_pullback_fst_completion p s xσ hxσZ
    rw [halg]
    change (maximalIdeal (X.presheaf.stalk x)).map
      (((pullback.fst p (specCompletedStalkTo S s)).stalkMap xσ).hom.comp
        ((X.presheaf.stalkCongr (.of_eq hxσX.symm)).hom).hom) = _
    rw [← Ideal.map_map, map_maximalIdeal_of_surjective _
      (ConcreteCategory.bijective_of_isIso
        ((X.presheaf.stalkCongr (.of_eq hxσX.symm)).hom)).surjective]
    exact hm
  obtain ⟨eC, heC⟩ := completion_ringEquiv_of_flat_local_hom
    (maximalIdeal (X.presheaf.stalk x)).fg_of_isNoetherianRing hSigmaMax hSigmaResidue
  have heC' : ∀ a : X.presheaf.stalk x,
      eC.toRingHom (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a) =
        algebraMap ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)
          (AdicCompletion
            (maximalIdeal ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
            ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
          (algebraMap (X.presheaf.stalk x)
            ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) a) := heC
  -- the identification of the stalk of `Spec 𝒪^∧_{S, s}` at its closed point
  let eS : AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) ≃+*
      (specCompletedStalk S s).presheaf.stalk (specCompletedStalkPoint S s) :=
    (stalkClosedPointIso (CommRingCat.of (AdicCompletion
      (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s)))).symm.commRingCatIsoToRingEquiv
  have heS : ∀ a : S.presheaf.stalk s,
      eS.toRingHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) a) =
      ((specCompletedStalkTo S s).stalkHomAt
        (specCompletedStalkTo_specCompletedStalkPoint S s)) a := fun a =>
    (RingHom.congr_fun (stalkHomAt_specCompletedStalkTo S s) a).symm
  -- the commuting square of local rings
  have hSquare := stalkHomAt_comp_eq_of_comp_eq pullback.condition.symm hxσZ
    (specCompletedStalkTo_specCompletedStalkPoint S s) hxσX hx
  have hφSymm := ringEquiv_symm_comp_of_comp_eq φ _ _ hφ
  have : IsLocalHom eC.toRingHom := ⟨(isLocalHom_equiv eC).map_nonunit⟩
  have : IsLocalHom φ.symm.toRingHom := ⟨(isLocalHom_equiv φ.symm).map_nonunit⟩
  have : IsLocalHom eS.toRingHom := ⟨(isLocalHom_equiv eS).map_nonunit⟩
  have hFG : eC.toRingHom.comp (φ.symm.toRingHom.comp
        ((algebraMap (W.presheaf.stalk w)
            (AdicCompletion (maximalIdeal (W.presheaf.stalk w))
              (W.presheaf.stalk w))).comp ((gW.stalkHomAt hw).comp eS.toRingHom))) =
      (algebraMap ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)
          (AdicCompletion
            (maximalIdeal ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
            ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))).comp
        (((pullback.snd p (specCompletedStalkTo S s)).stalkHomAt hxσZ).comp
          eS.toRingHom) := by
    refine adicCompletion_ringHom_ext _ _ (map_maximalIdeal_le _) (map_maximalIdeal_le _)
      (RingHom.ext fun a => ?_)
    have hp := RingHom.congr_fun hφSymm a
    have hsq := RingHom.congr_fun hSquare a
    simp only [RingHom.comp_apply] at hp hsq ⊢
    rw [heS a, hp, heC', hsq, halg]
  refine ⟨φ.symm.trans eC, RingHom.ext fun b => ?_, fun b => ?_⟩
  · obtain ⟨a, rfl⟩ := eS.surjective b
    exact RingHom.congr_fun hFG a
  · change eC (φ.symm (φ (algebraMap (X.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) b))) = _
    rw [φ.symm_apply_apply]
    exact heC' b

/-- The comparison morphism `Y ×_{T, β} Z ⟶ Y ×_{T, τ} D` attached to a factorisation
`β = m ≫ τ` of a morphism `β : Z ⟶ T` through `τ : D ⟶ T`. -/
private def baseChangeCompare {Z D Y T : Scheme.{u}} (q : Y ⟶ T) (τ : D ⟶ T) (m : Z ⟶ D)
    (β : Z ⟶ T) (hm : m ≫ τ = β) : (pullback q β : Scheme.{u}) ⟶ pullback q τ :=
  (pullbackTransitionIso τ m β hm (Over.mk q)).inv.left ≫ pullback.fst (pullback.snd q τ) m

@[reassoc]
private lemma baseChangeCompare_fst {Z D Y T : Scheme.{u}} (q : Y ⟶ T) (τ : D ⟶ T) (m : Z ⟶ D)
    (β : Z ⟶ T) (hm : m ≫ τ = β) :
    baseChangeCompare q τ m β hm ≫ pullback.fst q τ = pullback.fst q β := by
  change ((pullbackTransitionIso τ m β hm (Over.mk q)).inv.left ≫
    pullback.fst (pullback.snd q τ) m) ≫ pullback.fst q τ = _
  rw [Category.assoc]
  exact pullbackTransitionIso_inv_fst τ m β hm (Over.mk q)

@[reassoc]
private lemma baseChangeCompare_snd {Z D Y T : Scheme.{u}} (q : Y ⟶ T) (τ : D ⟶ T) (m : Z ⟶ D)
    (β : Z ⟶ T) (hm : m ≫ τ = β) :
    baseChangeCompare q τ m β hm ≫ pullback.snd q τ = pullback.snd q β ≫ m := by
  change ((pullbackTransitionIso τ m β hm (Over.mk q)).inv.left ≫
    pullback.fst (pullback.snd q τ) m) ≫ pullback.snd q τ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ m) (Over.w (pullbackTransitionIso τ m β hm (Over.mk q)).inv)

/-- Two points of `Y ×_{T, β} Z` over a point of `Z` at which `m` is an isomorphism on residue
fields, with the same image under `baseChangeCompare`, are equal. -/
private lemma eq_of_baseChangeCompare_eq {Z D Y T : Scheme.{u}} (q : Y ⟶ T) (τ : D ⟶ T)
    (m : Z ⟶ D) (β : Z ⟶ T) (hm : m ≫ τ = β) (z : Z) (hz : IsIso (m.residueFieldMap z))
    {a b : (pullback q β : Scheme.{u})}
    (h : baseChangeCompare q τ m β hm a = baseChangeCompare q τ m β hm b)
    (ha : pullback.snd q β a = z) (hb : pullback.snd q β b = z) : a = b := by
  have : IsIso (pullbackTransitionIso τ m β hm (Over.mk q)).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (pullbackTransitionIso τ m β hm (Over.mk q)).inv))
  have hw (c : (pullback q β : Scheme.{u})) : pullback.snd (pullback.snd q τ) m
      ((pullbackTransitionIso τ m β hm (Over.mk q)).inv.left c) = pullback.snd q β c :=
    congrArg (fun k : (pullback q β : Scheme.{u}) ⟶ Z => k c)
      (Over.w (pullbackTransitionIso τ m β hm (Over.mk q)).inv)
  exact (pullbackTransitionIso τ m β hm (Over.mk q)).inv.left.isOpenEmbedding.injective
    (AlgebraicGeometry.Scheme.Pullback.point_eq_of_isIso_residueFieldMap (pullback.snd q τ) m z hz
      _ _ h ((hw a).trans ha) ((hw b).trans hb))

/-- **Descending a pair of étale morphisms out of a common source to a finite stage.** Let `D`
be a cofiltered system of qcqs schemes with affine transition morphisms and limit `c`, let `p_X`
and `p_Y` be of finite presentation over `S` and `T`, and let an object `A` of finite
presentation over a stage `k` carry two étale morphisms, after base change to the limit, to the
base changes of `p_X` and `p_Y` along the limit's structure morphisms. Then at a later stage the
object and both étale morphisms are defined, and the comparison with the limit is computed on
the affine model `Aff` of `A` over the limit.

This is Tags 01ZM and 07RP combined: the morphisms descend by 01ZM and become étale by 07RP. -/
private theorem exists_etale_pair_descent_of_etale_snd
    {K : Type u} [SmallCategory K] [IsCofiltered K] (D : K ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c)
    [∀ {i j : K} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ k : K, CompactSpace (D.obj k)] [∀ k : K, QuasiSeparatedSpace (D.obj k)]
    [∀ k : K, IsLocallyNoetherian (D.obj k)]
    {X Y S T Aff : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ T)
    (hpX : AlgebraicGeometry.FinitePresentation pX)
    (hpY : AlgebraicGeometry.FinitePresentation pY)
    (k₁ : K) (ρK : D.obj k₁ ⟶ S) (τK : D.obj k₁ ⟶ T)
    (AK : Over (D.obj k₁)) (hAKfp : AlgebraicGeometry.FinitePresentation AK.hom)
    (hA : Aff ⟶ c.pt) (eAK : Over.mk hA ≅ (Over.pullback (c.π.app k₁)).obj AK)
    (fK : (Over.pullback (c.π.app k₁)).obj AK ⟶
      (Over.pullback (c.π.app k₁)).obj ((Over.pullback ρK).obj (Over.mk pX)))
    (gK : (Over.pullback (c.π.app k₁)).obj AK ⟶
      (Over.pullback (c.π.app k₁)).obj ((Over.pullback τK).obj (Over.mk pY)))
    (hgK : Etale gK.left) :
    ∃ (j₂ : K) (e : j₂ ⟶ k₁) (A₂ : Over (D.obj j₂))
      (fD : A₂ ⟶ (Over.pullback (D.map e ≫ ρK)).obj (Over.mk pX))
      (gD : A₂ ⟶ (Over.pullback (D.map e ≫ τK)).obj (Over.mk pY))
      (_ : Etale fK.left → Etale fD.left) (_ : Etale gD.left) (dA : Aff ⟶ A₂.left),
      dA ≫ A₂.hom = hA ≫ c.π.app j₂ ∧
        dA ≫ fD.left ≫ pullback.fst pX (D.map e ≫ ρK) =
          eAK.hom.left ≫ fK.left ≫
            pullback.fst ((Over.pullback ρK).obj (Over.mk pX)).hom (c.π.app k₁) ≫
              pullback.fst pX ρK ∧
        dA ≫ gD.left ≫ pullback.fst pY (D.map e ≫ τK) =
          eAK.hom.left ≫ gK.left ≫
            pullback.fst ((Over.pullback τK).obj (Over.mk pY)).hom (c.π.app k₁) ≫
              pullback.fst pY τK ∧
        ∃ (εA : Aff ⟶ (pullback A₂.hom (c.π.app j₂) : Scheme.{u})) (_ : IsIso εA),
          εA ≫ pullback.fst A₂.hom (c.π.app j₂) = dA ∧
            εA ≫ pullback.snd A₂.hom (c.π.app j₂) = hA := by
  classical
  have := hgK
  let := hpX.1
  let := hpX.2.1
  let := hpX.2.2
  let := hpY.1
  let := hpY.2.1
  let := hpY.2.2
  let XK : Over (D.obj k₁) := (Over.pullback ρK).obj (Over.mk pX)
  let YK : Over (D.obj k₁) := (Over.pullback τK).obj (Over.mk pY)
  have hXK : AlgebraicGeometry.FinitePresentation XK.hom :=
    finitePresentation_pullback _ _ hpX
  have hYK : AlgebraicGeometry.FinitePresentation YK.hom :=
    finitePresentation_pullback _ _ hpY
  obtain ⟨j₁, e₁, f₁, g₁, α₁, hα₁, hf₁, hg₁, hetf₁, hetg₁⟩ :=
    exists_span_model_of_etale_snd D c hc k₁ AK XK YK hAKfp hXK hYK fK gK
  let A₁ : Over (D.obj j₁) := (Over.pullback (D.map e₁)).obj AK
  let X₁ : Over (D.obj j₁) := (Over.pullback (D.map e₁)).obj XK
  let Y₁ : Over (D.obj j₁) := (Over.pullback (D.map e₁)).obj YK
  have hA₁fp : AlgebraicGeometry.FinitePresentation A₁.hom :=
    finitePresentation_pullback _ _ hAKfp
  have hX₁fp : AlgebraicGeometry.FinitePresentation X₁.hom :=
    finitePresentation_pullback _ _ hXK
  have hY₁fp : AlgebraicGeometry.FinitePresentation Y₁.hom :=
    finitePresentation_pullback _ _ hYK
  let := hA₁fp.1
  let := hA₁fp.2.1
  let := hA₁fp.2.2
  let := hX₁fp.1
  let := hX₁fp.2.1
  let := hX₁fp.2.2
  let := hY₁fp.1
  let := hY₁fp.2.1
  let := hY₁fp.2.2
  have : CompactSpace A₁.left := QuasiCompact.compactSpace_of_compactSpace A₁.hom
  have : CompactSpace X₁.left := QuasiCompact.compactSpace_of_compactSpace X₁.hom
  have : CompactSpace Y₁.left := QuasiCompact.compactSpace_of_compactSpace Y₁.hom
  have : QuasiSeparatedSpace A₁.left := quasiSeparatedSpace_of_quasiSeparated A₁.hom
  have : QuasiSeparatedSpace X₁.left := quasiSeparatedSpace_of_quasiSeparated X₁.hom
  have : QuasiSeparatedSpace Y₁.left := quasiSeparatedSpace_of_quasiSeparated Y₁.hom
  have : IsLocallyNoetherian X₁.left := LocallyOfFiniteType.isLocallyNoetherian X₁.hom
  have : IsLocallyNoetherian Y₁.left := LocallyOfFiniteType.isLocallyNoetherian Y₁.hom
  have : LocallyOfFiniteType f₁.left := by
    have : LocallyOfFiniteType (f₁.left ≫ X₁.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp f₁.left X₁.hom
  have : LocallyOfFiniteType g₁.left := by
    have : LocallyOfFiniteType (g₁.left ≫ Y₁.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp g₁.left Y₁.hom
  have : LocallyOfFinitePresentation f₁.left := inferInstance
  have : LocallyOfFinitePresentation g₁.left := inferInstance
  have := hetg₁
  -- A stage at which the second leg is étale, and at which the first leg is étale as soon as
  -- it is étale over the limit. Only the second leg is needed to choose the stage.
  obtain ⟨j₂, e₂, hetg₂, hetf₂⟩ : ∃ (j₂ : K) (e₂ : j₂ ⟶ j₁),
      Etale ((Over.pullback (D.map e₂)).map g₁).left ∧
        (Etale fK.left → Etale ((Over.pullback (D.map e₂)).map f₁).left) := by
    by_cases hfe : Etale fK.left
    · have := hetf₁ hfe
      obtain ⟨j₂, e₂, hf, hg⟩ := exists_etale_pair_pullback D c hc j₁ A₁ X₁ Y₁ f₁ g₁
      exact ⟨j₂, e₂, hg, fun _ => hf⟩
    · obtain ⟨r, hr⟩ :=
        AlgebraicGeometry.exists_etale_pullback_of_isLimit D c hc j₁ A₁ Y₁ g₁
      exact ⟨r.left, r.hom, hr, fun h => absurd h hfe⟩
  let A₂ : Over (D.obj j₂) := (Over.pullback (D.map e₂)).obj A₁
  let f₂ := (Over.pullback (D.map e₂)).map f₁
  let g₂ := (Over.pullback (D.map e₂)).map g₁
  have hf₂et : Etale fK.left → Etale f₂.left := hetf₂
  have : Etale g₂.left := hetg₂
  have hρeq : D.map e₂ ≫ D.map e₁ ≫ ρK = D.map (e₂ ≫ e₁) ≫ ρK := by
    rw [← Category.assoc, ← D.map_comp]
  have hτeq : D.map e₂ ≫ D.map e₁ ≫ τK = D.map (e₂ ≫ e₁) ≫ τK := by
    rw [← Category.assoc, ← D.map_comp]
  let eX₁ := pullbackTransitionIso ρK (D.map e₁) (D.map e₁ ≫ ρK) rfl (Over.mk pX)
  let eY₁ := pullbackTransitionIso τK (D.map e₁) (D.map e₁ ≫ τK) rfl (Over.mk pY)
  let eX₂ : (Over.pullback (D.map e₂)).obj X₁ ≅
      (Over.pullback (D.map (e₂ ≫ e₁) ≫ ρK)).obj (Over.mk pX) :=
    (Over.pullback (D.map e₂)).mapIso eX₁ ≪≫
      pullbackTransitionIso (D.map e₁ ≫ ρK) (D.map e₂) (D.map (e₂ ≫ e₁) ≫ ρK) hρeq
        (Over.mk pX)
  let eY₂ : (Over.pullback (D.map e₂)).obj Y₁ ≅
      (Over.pullback (D.map (e₂ ≫ e₁) ≫ τK)).obj (Over.mk pY) :=
    (Over.pullback (D.map e₂)).mapIso eY₁ ≪≫
      pullbackTransitionIso (D.map e₁ ≫ τK) (D.map e₂) (D.map (e₂ ≫ e₁) ≫ τK) hτeq
        (Over.mk pY)
  let f₂X : A₂ ⟶ (Over.pullback (D.map (e₂ ≫ e₁) ≫ ρK)).obj (Over.mk pX) := f₂ ≫ eX₂.hom
  let g₂Y : A₂ ⟶ (Over.pullback (D.map (e₂ ≫ e₁) ≫ τK)).obj (Over.mk pY) := g₂ ≫ eY₂.hom
  have : IsIso eX₂.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eX₂.hom))
  have : IsIso eY₂.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eY₂.hom))
  have hf₂Xet : Etale fK.left → Etale f₂X.left := fun hfe => by
    have := hf₂et hfe
    change Etale (f₂.left ≫ eX₂.hom.left); infer_instance
  have : Etale g₂Y.left := by
    change Etale (g₂.left ≫ eY₂.hom.left); infer_instance
  let α₂ := pullbackTransitionIso (D.map e₂) (c.π.app j₂) (c.π.app j₁) (c.w e₂) A₁
  let eA₂ : Over.mk hA ≅ (Over.pullback (c.π.app j₂)).obj A₂ := eAK ≪≫ α₁.symm ≪≫ α₂.symm
  let dA : Aff ⟶ A₂.left := eA₂.hom.left ≫ pullback.fst A₂.hom (c.π.app j₂)
  -- the projections of the comparison isomorphisms
  have heX₂fst : eX₂.hom.left ≫ pullback.fst pX (D.map (e₂ ≫ e₁) ≫ ρK) =
      pullback.fst X₁.hom (D.map e₂) ≫
        pullback.fst XK.hom (D.map e₁) ≫ pullback.fst pX ρK := by
    have h1 : (pullbackTransitionIso (D.map e₁ ≫ ρK) (D.map e₂) (D.map (e₂ ≫ e₁) ≫ ρK) hρeq
          (Over.mk pX)).hom.left ≫ pullback.fst pX (D.map (e₂ ≫ e₁) ≫ ρK) =
        pullback.fst ((Over.pullback (D.map e₁ ≫ ρK)).obj (Over.mk pX)).hom (D.map e₂) ≫
          pullback.fst pX (D.map e₁ ≫ ρK) :=
      pullbackTransitionIso_hom_fst _ _ _ _ _
    have h2 : eX₁.hom.left ≫ pullback.fst pX (D.map e₁ ≫ ρK) =
        pullback.fst XK.hom (D.map e₁) ≫ pullback.fst pX ρK :=
      pullbackTransitionIso_hom_fst _ _ _ _ _
    have hm : ((Over.pullback (D.map e₂)).map eX₁.hom).left ≫
        pullback.fst ((Over.pullback (D.map e₁ ≫ ρK)).obj (Over.mk pX)).hom (D.map e₂) =
        pullback.fst X₁.hom (D.map e₂) ≫ eX₁.hom.left := by
      simp only [X₁, XK, Over.pullback_map_left, pullback.lift_fst]
    change ((Over.pullback (D.map e₂)).map eX₁.hom).left ≫
      (pullbackTransitionIso (D.map e₁ ≫ ρK) (D.map e₂) (D.map (e₂ ≫ e₁) ≫ ρK) hρeq
        (Over.mk pX)).hom.left ≫ pullback.fst pX (D.map (e₂ ≫ e₁) ≫ ρK) = _
    rw [h1, ← Category.assoc, hm, Category.assoc, h2]
  have heY₂fst : eY₂.hom.left ≫ pullback.fst pY (D.map (e₂ ≫ e₁) ≫ τK) =
      pullback.fst Y₁.hom (D.map e₂) ≫
        pullback.fst YK.hom (D.map e₁) ≫ pullback.fst pY τK := by
    have h1 : (pullbackTransitionIso (D.map e₁ ≫ τK) (D.map e₂) (D.map (e₂ ≫ e₁) ≫ τK) hτeq
          (Over.mk pY)).hom.left ≫ pullback.fst pY (D.map (e₂ ≫ e₁) ≫ τK) =
        pullback.fst ((Over.pullback (D.map e₁ ≫ τK)).obj (Over.mk pY)).hom (D.map e₂) ≫
          pullback.fst pY (D.map e₁ ≫ τK) :=
      pullbackTransitionIso_hom_fst _ _ _ _ _
    have h2 : eY₁.hom.left ≫ pullback.fst pY (D.map e₁ ≫ τK) =
        pullback.fst YK.hom (D.map e₁) ≫ pullback.fst pY τK :=
      pullbackTransitionIso_hom_fst _ _ _ _ _
    have hm : ((Over.pullback (D.map e₂)).map eY₁.hom).left ≫
        pullback.fst ((Over.pullback (D.map e₁ ≫ τK)).obj (Over.mk pY)).hom (D.map e₂) =
        pullback.fst Y₁.hom (D.map e₂) ≫ eY₁.hom.left := by
      simp only [Y₁, YK, Over.pullback_map_left, pullback.lift_fst]
    change ((Over.pullback (D.map e₂)).map eY₁.hom).left ≫
      (pullbackTransitionIso (D.map e₁ ≫ τK) (D.map e₂) (D.map (e₂ ≫ e₁) ≫ τK) hτeq
        (Over.mk pY)).hom.left ≫ pullback.fst pY (D.map (e₂ ≫ e₁) ≫ τK) = _
    rw [h1, ← Category.assoc, hm, Category.assoc, h2]
  have hf₂fst : f₂.left ≫ pullback.fst X₁.hom (D.map e₂) =
      pullback.fst A₁.hom (D.map e₂) ≫ f₁.left := by
    simp only [f₂, A₁, X₁, Over.pullback_map_left, pullback.lift_fst]
  have hg₂fst : g₂.left ≫ pullback.fst Y₁.hom (D.map e₂) =
      pullback.fst A₁.hom (D.map e₂) ≫ g₁.left := by
    simp only [g₂, A₁, Y₁, Over.pullback_map_left, pullback.lift_fst]
  have hdAα : dA ≫ pullback.fst A₁.hom (D.map e₂) =
      eAK.hom.left ≫ α₁.inv.left ≫ pullback.fst A₁.hom (c.π.app j₁) := by
    have H := pullbackTransitionIso_inv_fst (D.map e₂) (c.π.app j₂) (c.π.app j₁)
      (c.w e₂) A₁
    change (eAK.hom.left ≫ α₁.inv.left ≫ α₂.inv.left) ≫
      pullback.fst A₂.hom (c.π.app j₂) ≫ pullback.fst A₁.hom (D.map e₂) = _
    simp only [Category.assoc]
    rw [H]
  have : IsIso eA₂.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eA₂.hom))
  refine ⟨j₂, e₂ ≫ e₁, A₂, f₂X, g₂Y, hf₂Xet, inferInstance, dA, ?_, ?_, ?_,
    eA₂.hom.left, inferInstance, rfl, Over.w eA₂.hom⟩
  · change (eA₂.hom.left ≫ pullback.fst A₂.hom (c.π.app j₂)) ≫ A₂.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ c.π.app j₂) (Over.w eA₂.hom)
  · have e0 : f₂X.left ≫ pullback.fst pX (D.map (e₂ ≫ e₁) ≫ ρK) =
        pullback.fst A₁.hom (D.map e₂) ≫ f₁.left ≫
          pullback.fst XK.hom (D.map e₁) ≫ pullback.fst pX ρK := by
      change (f₂.left ≫ eX₂.hom.left) ≫ pullback.fst pX (D.map (e₂ ≫ e₁) ≫ ρK) = _
      rw [Category.assoc, heX₂fst, ← Category.assoc, hf₂fst, Category.assoc]
    rw [e0, ← Category.assoc, hdAα]
    simp only [Category.assoc]
    rw [← reassoc_of% hf₁, ← Category.assoc α₁.inv.left α₁.hom.left, ← Over.comp_left,
      α₁.inv_hom_id, Over.id_left, Category.id_comp]
  · have e0 : g₂Y.left ≫ pullback.fst pY (D.map (e₂ ≫ e₁) ≫ τK) =
        pullback.fst A₁.hom (D.map e₂) ≫ g₁.left ≫
          pullback.fst YK.hom (D.map e₁) ≫ pullback.fst pY τK := by
      change (g₂.left ≫ eY₂.hom.left) ≫ pullback.fst pY (D.map (e₂ ≫ e₁) ≫ τK) = _
      rw [Category.assoc, heY₂fst, ← Category.assoc, hg₂fst, Category.assoc]
    rw [e0, ← Category.assoc, hdAα]
    simp only [Category.assoc]
    rw [← reassoc_of% hg₁, ← Category.assoc α₁.inv.left α₁.hom.left, ← Over.comp_left,
      α₁.inv_hom_id, Over.id_left, Category.id_comp]


/-- **Descending a pair of étale morphisms out of a common source to a finite stage**, for a
pair both of whose legs are étale. This is
`StacksDraft.ArtinApproximation.exists_etale_pair_descent_of_etale_snd` with étaleness of the
first leg supplied, so that étaleness of the descended first leg is unconditional. -/
private theorem exists_etale_pair_descent
    {K : Type u} [SmallCategory K] [IsCofiltered K] (D : K ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c)
    [∀ {i j : K} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ k : K, CompactSpace (D.obj k)] [∀ k : K, QuasiSeparatedSpace (D.obj k)]
    [∀ k : K, IsLocallyNoetherian (D.obj k)]
    {X Y S T Aff : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ T)
    (hpX : AlgebraicGeometry.FinitePresentation pX)
    (hpY : AlgebraicGeometry.FinitePresentation pY)
    (k₁ : K) (ρK : D.obj k₁ ⟶ S) (τK : D.obj k₁ ⟶ T)
    (AK : Over (D.obj k₁)) (hAKfp : AlgebraicGeometry.FinitePresentation AK.hom)
    (hA : Aff ⟶ c.pt) (eAK : Over.mk hA ≅ (Over.pullback (c.π.app k₁)).obj AK)
    (fK : (Over.pullback (c.π.app k₁)).obj AK ⟶
      (Over.pullback (c.π.app k₁)).obj ((Over.pullback ρK).obj (Over.mk pX)))
    (gK : (Over.pullback (c.π.app k₁)).obj AK ⟶
      (Over.pullback (c.π.app k₁)).obj ((Over.pullback τK).obj (Over.mk pY)))
    (hfK : Etale fK.left) (hgK : Etale gK.left) :
    ∃ (j₂ : K) (e : j₂ ⟶ k₁) (A₂ : Over (D.obj j₂))
      (fD : A₂ ⟶ (Over.pullback (D.map e ≫ ρK)).obj (Over.mk pX))
      (gD : A₂ ⟶ (Over.pullback (D.map e ≫ τK)).obj (Over.mk pY))
      (_ : Etale fD.left) (_ : Etale gD.left) (dA : Aff ⟶ A₂.left),
      dA ≫ A₂.hom = hA ≫ c.π.app j₂ ∧
        dA ≫ fD.left ≫ pullback.fst pX (D.map e ≫ ρK) =
          eAK.hom.left ≫ fK.left ≫
            pullback.fst ((Over.pullback ρK).obj (Over.mk pX)).hom (c.π.app k₁) ≫
              pullback.fst pX ρK ∧
        dA ≫ gD.left ≫ pullback.fst pY (D.map e ≫ τK) =
          eAK.hom.left ≫ gK.left ≫
            pullback.fst ((Over.pullback τK).obj (Over.mk pY)).hom (c.π.app k₁) ≫
              pullback.fst pY τK ∧
        ∃ (εA : Aff ⟶ (pullback A₂.hom (c.π.app j₂) : Scheme.{u})) (_ : IsIso εA),
          εA ≫ pullback.fst A₂.hom (c.π.app j₂) = dA ∧
            εA ≫ pullback.snd A₂.hom (c.π.app j₂) = hA := by
  obtain ⟨j₂, e, A₂, fD, gD, hfD, hgD, dA, hdABase, hdAX, hdAY, hrest⟩ :=
    exists_etale_pair_descent_of_etale_snd D c hc pX pY hpX hpY k₁ ρK τK AK hAKfp hA eAK
      fK gK hgK
  exact ⟨j₂, e, A₂, fD, gD, hfD hfK, hgD, dA, hdABase, hdAX, hdAY, hrest⟩

/-- **The descent of a pointed span over `Spec 𝒪^∧_{S, s}` to a smooth stage.** Let `(Usch, u)`
be a pointed scheme over `Spec 𝒪^∧_{S, s}` carrying a morphism `fU` to
`X ×_S Spec 𝒪^∧_{S, s}` and an **étale** morphism `gU` to `Y ×_{T, β} Spec 𝒪^∧_{S, s}`, both
over `Spec 𝒪^∧_{S, s}`. Then there are a scheme `D` smooth over `S`, a morphism
`m : Spec 𝒪^∧_{S, s} ⟶ D` over `S` through which `β` factors as `m ≫ τ`, an object `A` over `D`
with a morphism to `X ×_S D` and an étale morphism to `Y ×_T D`, together with a point of `A`
over the image of the closed point which reproduces `x` and `u`.

Only `gU` is required to be étale. Tag 0CAV produces a pointed scheme étale over *both* base
changes — the input of Tags 0GDX and 0CB1 — and étaleness of the `X`-leg is then returned as an
implication, together with the residue-field condition on that leg. Tag 0CAU produces one étale
over the `Y`-side only, with the morphism to `X` that approximates `φ`, and that is the input of
Tag 0CAW.

`Spec 𝒪^∧_{S, s}` is a cofiltered inverse limit of affine schemes smooth over an affine open of
`S` (Popescu's theorem), the two étale morphisms out of an affine open of `U` descend to a stage
by Tag 01ZM, and étaleness descends by Tag 07RP.

The base `B` carries both `S` and `T`, with `β` a morphism over `B`; it is what makes `β`
descend to a stage. For `B` terminal this is the hypothesis "`T` is locally of finite
presentation over `Spec ℤ`" of Tag 0GDX, and for `B = S` it is "`T ⟶ S` is locally of finite
type" of Tag 0CAW. -/
private theorem exists_stage_etale_pair_of_pointed_span
    {X S Y T B : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsLocallyNoetherian T]
    (bS : S ⟶ B) (hTB : T ⟶ B) [LocallyOfFinitePresentation hTB]
    {x : X} {s : S} (hG : IsGRing (S.presheaf.stalk s))
    (β : specCompletedStalk S s ⟶ T)
    (hβB : β ≫ hTB = specCompletedStalkTo S s ≫ bS)
    (xσ : (pullback p (specCompletedStalkTo S s) : Scheme.{u}))
    (hxσX : pullback.fst p (specCompletedStalkTo S s) xσ = x)
    (hxσZ : pullback.snd p (specCompletedStalkTo S s) xσ = specCompletedStalkPoint S s)
    (yσ : (pullback q β : Scheme.{u}))
    (hyσZ : pullback.snd q β yσ = specCompletedStalkPoint S s)
    (Usch : Scheme.{u}) (u : Usch)
    (fU : Usch ⟶ (pullback p (specCompletedStalkTo S s) : Scheme.{u})) (hfU : fU u = xσ)
    (gU : Usch ⟶ pullback q β) (hgUEt : Etale gU) (hgU : gU u = yσ)
    (hgUres : IsIso (gU.residueFieldMap u))
    (hUBase : gU ≫ pullback.snd q β =
      fU ≫ pullback.snd p (specCompletedStalkTo S s)) :
    ∃ (D : Scheme.{u}) (ρ : D ⟶ S) (_ : Smooth ρ) (τ : D ⟶ T)
      (m : specCompletedStalk S s ⟶ D)
      (_ : m ≫ ρ = specCompletedStalkTo S s) (hmτ : m ≫ τ = β)
      (A : Over D) (fD : A ⟶ (Over.pullback ρ).obj (Over.mk p))
      (gD : A ⟶ (Over.pullback τ).obj (Over.mk q))
      (_ : Etale fU → Etale fD.left) (_ : Etale gD.left) (a : A.left),
      τ ≫ hTB = ρ ≫ bS ∧
        A.hom a = m (specCompletedStalkPoint S s) ∧
        (fD.left ≫ pullback.fst p ρ) a = x ∧
        (IsIso ((fU ≫ pullback.fst p (specCompletedStalkTo S s)).residueFieldMap u) →
          IsIso ((fD.left ≫ pullback.fst p ρ).residueFieldMap a)) ∧
        IsIso (gD.left.residueFieldMap a) ∧
        gD.left a = baseChangeCompare q τ m β hmτ yσ ∧
        ∃ (aσ : (pullback A.hom m : Scheme.{u}))
          (_ : pullback.fst A.hom m aσ = a)
          (_ : pullback.snd A.hom m aσ = specCompletedStalkPoint S s)
          (Uaff : Scheme.{u}) (jUaff : Uaff ⟶ Usch) (_ : IsOpenImmersion jUaff)
          (eAff : Uaff ⟶ (pullback A.hom m : Scheme.{u})) (_ : IsIso eAff) (a₀ : Uaff)
          (_ : jUaff a₀ = u) (_ : eAff a₀ = aσ),
          jUaff ≫ fU ≫ pullback.fst p (specCompletedStalkTo S s) =
              eAff ≫ pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ ∧
            jUaff ≫ gU ≫ pullback.fst q β =
              eAff ≫ pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ ∧
            jUaff ≫ fU ≫ pullback.snd p (specCompletedStalkTo S s) =
              eAff ≫ pullback.snd A.hom m := by
  classical
  have := hgUEt
  have := hgUres
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have hGhat := completion_isGRing (S.presheaf.stalk s) hG
  have : IsNoetherianRing (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)) := hGhat.1
  have : IsLocallyNoetherian (specCompletedStalk S s) := inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  -- Popescu's theorem: `Spec 𝒪^∧_{S, s}` is a cofiltered limit of smooth affine `S`-schemes.
  obtain ⟨S₀, hS₀, hs₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := s) (U := ⊤) (by simp)
  have : IsNoetherianRing Γ(S, S₀) := IsLocallyNoetherian.component_noetherian ⟨S₀, hS₀⟩
  obtain ⟨K, instK, instKc, pres, fS, hAff, hSm, hpi⟩ :=
    exists_limitPresentation_spec_completedStalk_of_isAffineOpen hS₀ hs₀ hG
  have (k : K) : IsAffine (pres.diag.obj k) := hAff k
  have {i j : K} (e : i ⟶ j) : IsAffineHom (pres.diag.map e) := inferInstance
  have (k : K) : CompactSpace (pres.diag.obj k) := inferInstance
  have (k : K) : QuasiSeparatedSpace (pres.diag.obj k) := inferInstance
  have (k : K) : Smooth (fS.app k) := hSm k
  have (k : K) : IsLocallyNoetherian (pres.diag.obj k) :=
    LocallyOfFiniteType.isLocallyNoetherian (fS.app k ≫ hS₀.fromSpec)
  have hnat : ∀ {i j : K} (e : i ⟶ j), pres.diag.map e ≫ fS.app j = fS.app i := by
    intro i j e
    simp
  have hopen : Spec.map (S.presheaf.germ S₀ s hs₀ ≫ CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)))) ≫ hS₀.fromSpec = specCompletedStalkTo S s := by
    have h1 : Spec.map (S.presheaf.germ S₀ s hs₀ ≫ CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk s) (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))) =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
          Spec.map (S.presheaf.germ S₀ s hs₀) := Spec.map_comp _ _
    have h2 : Spec.map (S.presheaf.germ S₀ s hs₀) ≫ hS₀.fromSpec = S.fromSpecStalk s :=
      hS₀.fromSpecStalk_eq_fromSpecStalk hs₀
    rw [h1, Category.assoc, h2]
  have hρ : ∀ k : K, pres.π.app k ≫ (fS.app k ≫ hS₀.fromSpec) =
      specCompletedStalkTo S s := fun k => by
    rw [← Category.assoc, hpi k]
    exact hopen
  -- factor `β` through a stage
  let tB : pres.diag ⟶ (Functor.const K).obj B :=
    { app := fun k => fS.app k ≫ hS₀.fromSpec ≫ bS
      naturality := fun i j e => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          ← Category.assoc, hnat e] }
  obtain ⟨k₀, τ₀, hτ₀, hτ₀B⟩ := exists_factorization_over_base_finitePresentation
    pres.diag pres.cone pres.isLimit hTB tB β
    (by
      ext k
      change pres.cone.π.app k ≫ fS.app k ≫ hS₀.fromSpec ≫ bS = β ≫ hTB
      calc pres.cone.π.app k ≫ fS.app k ≫ hS₀.fromSpec ≫ bS
          = (pres.cone.π.app k ≫ fS.app k ≫ hS₀.fromSpec) ≫ bS := by
            simp only [Category.assoc]
        _ = specCompletedStalkTo S s ≫ bS := congrArg (· ≫ bS) (hρ k)
        _ = β ≫ hTB := hβB.symm)
  -- an affine open of `Usch` through its distinguished point
  obtain ⟨Aff, jU, hjU, a₀, ha₀⟩ := Usch.exists_Spec_apply_eq u
  have : IsOpenImmersion jU := hjU
  let hA : Spec Aff ⟶ specCompletedStalk S s :=
    jU ≫ fU ≫ pullback.snd p (specCompletedStalkTo S s)
  -- the structure morphism is read through the étale leg, which is what makes it of finite
  -- presentation: the `X`-leg `fU` is an arbitrary morphism.
  have hAeq : hA = jU ≫ gU ≫ pullback.snd q β :=
    congrArg (jU ≫ ·) hUBase.symm
  have : LocallyOfFiniteType hA := by rw [hAeq]; infer_instance
  have : QuasiCompact hA := by rw [hAeq]; infer_instance
  have hAfp : AlgebraicGeometry.FinitePresentation hA :=
    AlgebraicGeometry.finitePresentation_of_finiteType hA
  obtain ⟨iA, Aᵢ, hAᵢfp, eAᵢ⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation
      pres.diag pres.cone pres.isLimit (Over.mk hA) hAfp
  obtain ⟨k₁, k₁₀, k₁A, -⟩ := IsCofilteredOrEmpty.cone_objs k₀ iA
  let τK : pres.diag.obj k₁ ⟶ T := pres.diag.map k₁₀ ≫ τ₀
  have hτK : pres.cone.π.app k₁ ≫ τK = β := by
    dsimp only [τK]
    rw [← Category.assoc, pres.cone.w k₁₀, hτ₀]
  let ρK : pres.diag.obj k₁ ⟶ S := fS.app k₁ ≫ hS₀.fromSpec
  have hρK : pres.cone.π.app k₁ ≫ ρK = specCompletedStalkTo S s := hρ k₁
  let AK : Over (pres.diag.obj k₁) := (Over.pullback (pres.diag.map k₁A)).obj Aᵢ
  have hAKfp : AlgebraicGeometry.FinitePresentation AK.hom :=
    finitePresentation_pullback _ _ hAᵢfp
  let eAK : Over.mk hA ≅ (Over.pullback (pres.cone.π.app k₁)).obj AK :=
    eAᵢ.some ≪≫ overPullbackCongr (pres.cone.w k₁A).symm Aᵢ ≪≫
      (Over.pullbackComp (pres.cone.π.app k₁) (pres.diag.map k₁A)).app Aᵢ
  -- quasi-compact opens of `X` and `Y` through which the affine piece factors
  obtain ⟨UX, aX, hCX, haX⟩ := exists_quasiCompact_open_factorization
    (jU ≫ fU ≫ pullback.fst p (specCompletedStalkTo S s))
  obtain ⟨UY, aY, hCY, haY⟩ := exists_quasiCompact_open_factorization
    (jU ≫ gU ≫ pullback.fst q β)
  let := hCX
  let := hCY
  let pX := UX.ι ≫ p
  let pY := UY.ι ≫ q
  have : LocallyOfFiniteType pX := inferInstanceAs (LocallyOfFiniteType (UX.ι ≫ p))
  have : LocallyOfFiniteType pY := inferInstanceAs (LocallyOfFiniteType (UY.ι ≫ q))
  have : QuasiCompact pX := inferInstanceAs (QuasiCompact (UX.ι ≫ p))
  have : QuasiCompact pY := inferInstanceAs (QuasiCompact (UY.ι ≫ q))
  have hpX := AlgebraicGeometry.finitePresentation_of_finiteType pX
  have hpY := AlgebraicGeometry.finitePresentation_of_finiteType pY
  have haXbase : aX ≫ pX = hA ≫ specCompletedStalkTo S s := by
    dsimp only [pX, hA]
    rw [← Category.assoc, haX]
    simp only [Category.assoc, pullback.condition]
  have haYbase : aY ≫ pY = hA ≫ β := by
    dsimp only [pY, hA]
    rw [← Category.assoc, haY]
    simp only [Category.assoc, pullback.condition]
    simpa only [Category.assoc] using
      congrArg (jU ≫ ·) (congrArg (· ≫ β) hUBase)
  let fAX : Over.mk hA ⟶ (Over.pullback (specCompletedStalkTo S s)).obj (Over.mk pX) :=
    Over.homMk (pullback.lift aX hA haXbase) (pullback.lift_snd _ _ _)
  let fAY : Over.mk hA ⟶ (Over.pullback β).obj (Over.mk pY) :=
    Over.homMk (pullback.lift aY hA haYbase) (pullback.lift_snd _ _ _)
  have hfAXet : Etale fU → Etale fAX.left := fun _ => by
    let kk : (Over.pullback (specCompletedStalkTo S s)).obj (Over.mk pX) ⟶
        (Over.pullback (specCompletedStalkTo S s)).obj (Over.mk p) :=
      (Over.pullback (specCompletedStalkTo S s)).map (Over.homMk UX.ι rfl)
    have : Etale kk.left :=
      MorphismProperty.overPullbackMap (specCompletedStalkTo S s) _
        (inferInstanceAs (Etale UX.ι))
    have heq : fAX.left ≫ kk.left = jU ≫ fU := by
      apply pullback.hom_ext
      · simpa only [fAX, kk, hA, Over.homMk_left, Over.pullback_map_left, Over.mk_hom,
          Over.mk_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd, pullback.lift_snd_assoc] using haX
      · simp only [fAX, kk, hA, Over.homMk_left, Over.pullback_map_left, Over.mk_hom,
          Over.mk_left, Category.assoc, pullback.lift_snd]
    have : Etale (fAX.left ≫ kk.left) := by
      rw [heq]
      infer_instance
    exact Etale.of_comp fAX.left kk.left
  have : Etale fAY.left := by
    let kk : (Over.pullback β).obj (Over.mk pY) ⟶ (Over.pullback β).obj (Over.mk q) :=
      (Over.pullback β).map (Over.homMk UY.ι rfl)
    have : Etale kk.left :=
      MorphismProperty.overPullbackMap β _ (inferInstanceAs (Etale UY.ι))
    have heq : fAY.left ≫ kk.left = jU ≫ gU := by
      apply pullback.hom_ext
      · simpa only [fAY, kk, hA, Over.homMk_left, Over.pullback_map_left, Over.mk_hom,
          Over.mk_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd, pullback.lift_snd_assoc] using haY
      · simp only [fAY, kk, hA, Over.homMk_left, Over.pullback_map_left, Over.mk_hom,
          Over.mk_left, Category.assoc, pullback.lift_snd]
        simpa only [Category.assoc] using congrArg (jU ≫ ·) hUBase.symm
    have : Etale (fAY.left ≫ kk.left) := by
      rw [heq]
      infer_instance
    exact Etale.of_comp fAY.left kk.left
  let XK : Over (pres.diag.obj k₁) := (Over.pullback ρK).obj (Over.mk pX)
  let YK : Over (pres.diag.obj k₁) := (Over.pullback τK).obj (Over.mk pY)
  let eXK := pullbackTransitionIso ρK (pres.cone.π.app k₁) (specCompletedStalkTo S s) hρK
    (Over.mk pX)
  let eYK := pullbackTransitionIso τK (pres.cone.π.app k₁) β hτK (Over.mk pY)
  let fK : (Over.pullback (pres.cone.π.app k₁)).obj AK ⟶
      (Over.pullback (pres.cone.π.app k₁)).obj XK := eAK.inv ≫ fAX ≫ eXK.inv
  let gK : (Over.pullback (pres.cone.π.app k₁)).obj AK ⟶
      (Over.pullback (pres.cone.π.app k₁)).obj YK := eAK.inv ≫ fAY ≫ eYK.inv
  have : IsIso eAK.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eAK.inv))
  have : IsIso eXK.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eXK.inv))
  have : IsIso eYK.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eYK.inv))
  have hfKet : Etale fU → Etale fK.left := fun hfUet => by
    have := hfAXet hfUet
    change Etale (eAK.inv.left ≫ fAX.left ≫ eXK.inv.left)
    infer_instance
  have : Etale gK.left := by
    change Etale (eAK.inv.left ≫ fAY.left ≫ eYK.inv.left)
    infer_instance
  obtain ⟨j₂, e, A₂, fX, gY, hetfX, hetgY, dA, hdABase, hdAX0, hdAY0,
    εA, hεAiso, hεAfst, hεAsnd⟩ :=
    exists_etale_pair_descent_of_etale_snd pres.diag pres.cone pres.isLimit pX pY hpX hpY k₁
      ρK τK AK hAKfp hA eAK fK gK inferInstance
  have hfXet : Etale fU → Etale fX.left := fun hfUet => hetfX (hfKet hfUet)
  have := hetgY
  let m := pres.cone.π.app j₂
  let ρ : pres.diag.obj j₂ ⟶ S := pres.diag.map e ≫ ρK
  let τ : pres.diag.obj j₂ ⟶ T := pres.diag.map e ≫ τK
  have hmρ : m ≫ ρ = specCompletedStalkTo S s := by
    change pres.cone.π.app j₂ ≫ pres.diag.map e ≫ ρK = _
    rw [← Category.assoc, pres.cone.w e, hρK]
  have hmτ : m ≫ τ = β := by
    change pres.cone.π.app j₂ ≫ pres.diag.map e ≫ τK = _
    rw [← Category.assoc, pres.cone.w e, hτK]
  have hρsmooth : Smooth ρ := by
    have : pres.diag.map e ≫ ρK = fS.app j₂ ≫ hS₀.fromSpec := by
      change pres.diag.map e ≫ fS.app k₁ ≫ hS₀.fromSpec = _
      rw [← Category.assoc, hnat e]
    change Smooth (pres.diag.map e ≫ ρK)
    rw [this]
    infer_instance
  have := hρsmooth
  have hτρ : τ ≫ hTB = ρ ≫ bS := by
    change (pres.diag.map e ≫ pres.diag.map k₁₀ ≫ τ₀) ≫ hTB =
      (pres.diag.map e ≫ fS.app k₁ ≫ hS₀.fromSpec) ≫ bS
    rw [Category.assoc, Category.assoc, hτ₀B]
    change pres.diag.map e ≫ pres.diag.map k₁₀ ≫ fS.app k₀ ≫ hS₀.fromSpec ≫ bS = _
    rw [← Category.assoc (pres.diag.map k₁₀), hnat k₁₀]
    simp only [Category.assoc]
  -- the composites of `dA` with the two étale morphisms
  have hdAX : dA ≫ fX.left ≫ pullback.fst pX ρ = aX := by
    rw [hdAX0]
    have h₂ : eAK.hom.left ≫ fK.left = fAX.left ≫ eXK.inv.left := by
      change eAK.hom.left ≫ (eAK.inv ≫ fAX ≫ eXK.inv).left = _
      simp only [← Category.assoc, ← Over.comp_left, eAK.hom_inv_id, Category.id_comp]
    have h₃ : eXK.inv.left ≫ pullback.fst XK.hom (pres.cone.π.app k₁) ≫
        pullback.fst pX ρK = pullback.fst pX (specCompletedStalkTo S s) :=
      pullbackTransitionIso_inv_fst _ _ _ _ _
    rw [← Category.assoc, h₂, Category.assoc, h₃]
    exact pullback.lift_fst _ _ _
  have hdAY : dA ≫ gY.left ≫ pullback.fst pY τ = aY := by
    rw [hdAY0]
    have h₂ : eAK.hom.left ≫ gK.left = fAY.left ≫ eYK.inv.left := by
      change eAK.hom.left ≫ (eAK.inv ≫ fAY ≫ eYK.inv).left = _
      simp only [← Category.assoc, ← Over.comp_left, eAK.hom_inv_id, Category.id_comp]
    have h₃ : eYK.inv.left ≫ pullback.fst YK.hom (pres.cone.π.app k₁) ≫
        pullback.fst pY τK = pullback.fst pY β :=
      pullbackTransitionIso_inv_fst _ _ _ _ _
    rw [← Category.assoc, h₂, Category.assoc, h₃]
    exact pullback.lift_fst _ _ _
  -- compose with the open immersions back into `X` and `Y`
  let fD : A₂ ⟶ (Over.pullback ρ).obj (Over.mk p) :=
    fX ≫ (Over.pullback ρ).map (Over.homMk UX.ι rfl)
  let gD : A₂ ⟶ (Over.pullback τ).obj (Over.mk q) :=
    gY ≫ (Over.pullback τ).map (Over.homMk UY.ι rfl)
  have : Etale ((Over.pullback ρ).map (Over.homMk UX.ι rfl :
      Over.mk pX ⟶ Over.mk p)).left :=
    MorphismProperty.overPullbackMap ρ _ (inferInstanceAs (Etale UX.ι))
  have : Etale ((Over.pullback τ).map (Over.homMk UY.ι rfl :
      Over.mk pY ⟶ Over.mk q)).left :=
    MorphismProperty.overPullbackMap τ _ (inferInstanceAs (Etale UY.ι))
  have hfDet : Etale fU → Etale fD.left := fun hfUet => by
    have := hfXet hfUet
    change Etale (fX.left ≫ ((Over.pullback ρ).map (Over.homMk UX.ι rfl :
      Over.mk pX ⟶ Over.mk p)).left)
    infer_instance
  have : Etale gD.left := by
    change Etale (gY.left ≫ ((Over.pullback τ).map (Over.homMk UY.ι rfl :
      Over.mk pY ⟶ Over.mk q)).left)
    infer_instance
  have hfDproj : fD.left ≫ pullback.fst p ρ = fX.left ≫ pullback.fst pX ρ ≫ UX.ι := by
    change (fX.left ≫ ((Over.pullback ρ).map (Over.homMk UX.ι rfl :
      Over.mk pX ⟶ Over.mk p)).left) ≫ pullback.fst p ρ = _
    simp only [Over.pullback_map_left, Over.homMk_left, Over.mk_hom, Over.mk_left,
      Category.assoc, pullback.lift_fst]
  have hgDproj : gD.left ≫ pullback.fst q τ = gY.left ≫ pullback.fst pY τ ≫ UY.ι := by
    change (gY.left ≫ ((Over.pullback τ).map (Over.homMk UY.ι rfl :
      Over.mk pY ⟶ Over.mk q)).left) ≫ pullback.fst q τ = _
    simp only [Over.pullback_map_left, Over.homMk_left, Over.mk_hom, Over.mk_left,
      Category.assoc, pullback.lift_fst]
  have hdAX' : dA ≫ fD.left ≫ pullback.fst p ρ =
      jU ≫ fU ≫ pullback.fst p (specCompletedStalkTo S s) := by
    rw [hfDproj, ← Category.assoc, ← Category.assoc, Category.assoc dA, hdAX]
    exact haX
  have hdAY' : dA ≫ gD.left ≫ pullback.fst q τ = jU ≫ gU ≫ pullback.fst q β := by
    rw [hgDproj, ← Category.assoc, ← Category.assoc, Category.assoc dA, hdAY]
    exact haY
  have hgDbase : dA ≫ gD.left ≫ pullback.snd q τ =
      jU ≫ gU ≫ pullback.snd q β ≫ m := by
    have h : dA ≫ gD.left ≫ pullback.snd q τ = hA ≫ m := by
      have hw : gD.left ≫ pullback.snd q τ = A₂.hom :=
        Over.w gD
      rw [hw]
      exact hdABase
    rw [h]
    change jU ≫ fU ≫ pullback.snd p (specCompletedStalkTo S s) ≫ m = _
    simpa only [Category.assoc] using
      congrArg (fun k => jU ≫ k ≫ m) hUBase.symm
  have hdAg : dA ≫ gD.left = jU ≫ gU ≫ baseChangeCompare q τ m β hmτ := by
    apply pullback.hom_ext (f := q) (g := τ)
    · simp only [Category.assoc]
      rw [baseChangeCompare_fst]
      simpa only [Category.assoc] using hdAY'
    · simp only [Category.assoc]
      rw [baseChangeCompare_snd]
      simpa only [Category.assoc] using hgDbase
  -- the point
  have hApoint : hA a₀ = specCompletedStalkPoint S s := by
    change pullback.snd p (specCompletedStalkTo S s) (fU (jU a₀)) = _
    rw [ha₀, hfU]
    exact hxσZ
  have hdApoint : A₂.hom (dA a₀) = m (specCompletedStalkPoint S s) := by
    change (dA ≫ A₂.hom) a₀ = _
    rw [hdABase]
    change m (hA a₀) = _
    rw [hApoint]
  have hfpoint : (fD.left ≫ pullback.fst p ρ) (dA a₀) = x := by
    change (dA ≫ fD.left ≫ pullback.fst p ρ) a₀ = x
    rw [hdAX']
    change pullback.fst p (specCompletedStalkTo S s) (fU (jU a₀)) = x
    rw [ha₀, hfU]
    exact hxσX
  -- the residue field conditions
  have : IsIso (jU.residueFieldMap a₀) := isIso_residueFieldMap_of_surjectiveOnStalks jU a₀
  have : IsIso (m.residueFieldMap (specCompletedStalkPoint S s)) :=
    isIso_residueFieldMap_of_comp_specCompletedStalkTo ρ m hmρ
  have hjres : IsIso (jU.residueFieldMap a₀) :=
    isIso_residueFieldMap_of_surjectiveOnStalks jU a₀
  have hfres : IsIso ((fU ≫ pullback.fst p (specCompletedStalkTo S s)).residueFieldMap u) →
      IsIso ((fD.left ≫ pullback.fst p ρ).residueFieldMap (dA a₀)) := fun hfUres => by
    have hr2 : IsIso ((fU ≫ pullback.fst p (specCompletedStalkTo S s)).residueFieldMap
        (jU a₀)) := by
      rwa [ha₀]
    have : IsIso ((dA ≫ fD.left ≫ pullback.fst p ρ).residueFieldMap a₀) := by
      rw [hdAX', Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' hr2 hjres
    exact isIso_residueFieldMap_of_comp dA (fD.left ≫ pullback.fst p ρ) a₀
  have hbcres : IsIso ((baseChangeCompare q τ m β hmτ).residueFieldMap yσ) := by
    have : IsIso ((pullbackTransitionIso τ m β hmτ (Over.mk q)).inv.left) :=
      inferInstanceAs (IsIso ((Over.forget _).map
        (pullbackTransitionIso τ m β hmτ (Over.mk q)).inv))
    have hpt : pullback.snd (pullback.snd q τ) m
        ((pullbackTransitionIso τ m β hmτ (Over.mk q)).inv.left yσ) =
        specCompletedStalkPoint S s := by
      have hw := congrArg (fun k : (pullback q β : Scheme.{u}) ⟶ specCompletedStalk S s =>
        k yσ) (Over.w (pullbackTransitionIso τ m β hmτ (Over.mk q)).inv)
      exact hw.trans hyσZ
    have : IsIso (m.residueFieldMap (pullback.snd (pullback.snd q τ) m
        ((pullbackTransitionIso τ m β hmτ (Over.mk q)).inv.left yσ))) := by
      rw [hpt]; infer_instance
    have hbc1 : IsIso ((pullback.fst (pullback.snd q τ) m).residueFieldMap
        ((pullbackTransitionIso τ m β hmτ (Over.mk q)).inv.left yσ)) :=
      isIso_residueFieldMap_pullback_fst _ _ _
    have hbc2 : IsIso (((pullbackTransitionIso τ m β hmτ
        (Over.mk q)).inv.left).residueFieldMap yσ) :=
      isIso_residueFieldMap_of_surjectiveOnStalks _ yσ
    change IsIso (((pullbackTransitionIso τ m β hmτ (Over.mk q)).inv.left ≫
      pullback.fst (pullback.snd q τ) m).residueFieldMap yσ)
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hbc1 hbc2
  have hr3 : IsIso ((gU ≫ baseChangeCompare q τ m β hmτ).residueFieldMap (jU a₀)) := by
    rw [ha₀, Scheme.residueFieldMap_comp]
    have hbc3 : IsIso ((baseChangeCompare q τ m β hmτ).residueFieldMap (gU u)) := by
      rwa [hgU]
    exact IsIso.comp_isIso' hbc3 hgUres
  have : IsIso ((dA ≫ gD.left).residueFieldMap a₀) := by
    rw [hdAg, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hr3 hjres
  have hgres : IsIso (gD.left.residueFieldMap (dA a₀)) :=
    isIso_residueFieldMap_of_comp dA gD.left a₀
  have hgpoint : gD.left (dA a₀) = baseChangeCompare q τ m β hmτ yσ := by
    change (dA ≫ gD.left) a₀ = _
    rw [hdAg]
    change baseChangeCompare q τ m β hmτ (gU (jU a₀)) = _
    rw [ha₀, hgU]
  -- the affine model of `U` is the base change of `A₂` to `Spec 𝒪^∧_{S, s}`, which identifies
  -- the local ring of `U` at its point with that of the base change
  have haσA : pullback.fst A₂.hom m (εA a₀) = dA a₀ :=
    congrArg (fun k : Spec Aff ⟶ A₂.left => k a₀) hεAfst
  have haσZ : pullback.snd A₂.hom m (εA a₀) = specCompletedStalkPoint S s := by
    refine (congrArg (fun k : Spec Aff ⟶ specCompletedStalk S s => k a₀) hεAsnd).trans ?_
    change pullback.snd p (specCompletedStalkTo S s) (fU (jU a₀)) = _
    rw [ha₀, hfU]
    exact hxσZ
  have hX : jU ≫ fU ≫ pullback.fst p (specCompletedStalkTo S s) =
      εA ≫ pullback.fst A₂.hom m ≫ fD.left ≫ pullback.fst p ρ :=
    hdAX'.symm.trans (by rw [← hεAfst]; exact Category.assoc _ _ _)
  have hY : jU ≫ gU ≫ pullback.fst q β =
      εA ≫ pullback.fst A₂.hom m ≫ gD.left ≫ pullback.fst q τ :=
    hdAY'.symm.trans (by rw [← hεAfst]; exact Category.assoc _ _ _)
  exact ⟨pres.diag.obj j₂, ρ, hρsmooth, τ, m, hmρ, hmτ, A₂, fD, gD, hfDet,
    inferInstance, dA a₀, hτρ, hdApoint, hfpoint, hfres, hgres, hgpoint,
    εA a₀, haσA, haσZ, Spec Aff, jU, hjU, εA, hεAiso, a₀, ha₀, rfl, hX, hY, hεAsnd.symm⟩

/-- **The descent of a pointed scheme étale over both base changes to a smooth stage.** This is
`StacksDraft.ArtinApproximation.exists_stage_etale_pair_of_pointed_span` for the input Tag 0CAV
supplies: an elementary étale neighbourhood `U` of `(X ×_S Spec 𝒪^∧_{S, s}, x_σ)` carrying an
étale morphism to `Y ×_{T, β} Spec 𝒪^∧_{S, s}`. Both legs being étale, the two conclusions about
the first leg at the stage are unconditional. -/
private theorem exists_stage_etale_pair_of_common_neighborhood
    {X S Y T B : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsLocallyNoetherian T]
    (bS : S ⟶ B) (hTB : T ⟶ B) [LocallyOfFinitePresentation hTB]
    {x : X} {s : S} (hG : IsGRing (S.presheaf.stalk s))
    (β : specCompletedStalk S s ⟶ T)
    (hβB : β ≫ hTB = specCompletedStalkTo S s ≫ bS)
    (xσ : (pullback p (specCompletedStalkTo S s) : Scheme.{u}))
    (hxσX : pullback.fst p (specCompletedStalkTo S s) xσ = x)
    (hxσZ : pullback.snd p (specCompletedStalkTo S s) xσ = specCompletedStalkPoint S s)
    (hxσres : IsIso ((pullback.fst p (specCompletedStalkTo S s)).residueFieldMap xσ))
    (yσ : (pullback q β : Scheme.{u}))
    (hyσZ : pullback.snd q β yσ = specCompletedStalkPoint S s)
    (U : EtaleNeighborhood (pullback p (specCompletedStalkTo S s)) xσ)
    (hUres : IsIso (U.toBase.residueFieldMap U.point))
    (qU : U.scheme ⟶ pullback q β) (hqUEt : Etale qU) (hqU : qU U.point = yσ)
    (hqUres : IsIso (qU.residueFieldMap U.point))
    (hqUBase : qU ≫ pullback.snd q β =
      U.toBase ≫ pullback.snd p (specCompletedStalkTo S s)) :
    ∃ (D : Scheme.{u}) (ρ : D ⟶ S) (_ : Smooth ρ) (τ : D ⟶ T)
      (m : specCompletedStalk S s ⟶ D)
      (_ : m ≫ ρ = specCompletedStalkTo S s) (hmτ : m ≫ τ = β)
      (A : Over D) (fD : A ⟶ (Over.pullback ρ).obj (Over.mk p))
      (gD : A ⟶ (Over.pullback τ).obj (Over.mk q))
      (_ : Etale fD.left) (_ : Etale gD.left) (a : A.left),
      τ ≫ hTB = ρ ≫ bS ∧
        A.hom a = m (specCompletedStalkPoint S s) ∧
        (fD.left ≫ pullback.fst p ρ) a = x ∧
        IsIso ((fD.left ≫ pullback.fst p ρ).residueFieldMap a) ∧
        IsIso (gD.left.residueFieldMap a) ∧
        gD.left a = baseChangeCompare q τ m β hmτ yσ ∧
        ∃ (aσ : (pullback A.hom m : Scheme.{u}))
          (_ : pullback.fst A.hom m aσ = a)
          (_ : pullback.snd A.hom m aσ = specCompletedStalkPoint S s)
          (Uaff : Scheme.{u}) (jUaff : Uaff ⟶ U.scheme) (_ : IsOpenImmersion jUaff)
          (eAff : Uaff ⟶ (pullback A.hom m : Scheme.{u})) (_ : IsIso eAff) (a₀ : Uaff)
          (_ : jUaff a₀ = U.point) (_ : eAff a₀ = aσ),
          jUaff ≫ U.toBase ≫ pullback.fst p (specCompletedStalkTo S s) =
              eAff ≫ pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ ∧
            jUaff ≫ qU ≫ pullback.fst q β =
              eAff ≫ pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ := by
  have hfUres : IsIso ((U.toBase ≫ pullback.fst p (specCompletedStalkTo S s)).residueFieldMap
      U.point) := by
    have hr1 : IsIso ((pullback.fst p (specCompletedStalkTo S s)).residueFieldMap
        (U.toBase U.point)) := by rwa [U.map_point]
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hr1 hUres
  obtain ⟨D, ρ, hρSm, τ, m, hmρ, hmτ, A, fD, gD, hfD, hgD, a, hτρ, hAa, hfa, hfres, hgres,
    hga, aσ, haσA, haσZ, Uaff, jUaff, hjUaff, eAff, heAffIso, a₀, hja₀, heAffa₀,
    hAffX, hAffY, -⟩ :=
    exists_stage_etale_pair_of_pointed_span p q bS hTB hG β hβB xσ hxσX hxσZ yσ hyσZ
      U.scheme U.point U.toBase U.map_point qU hqUEt hqU hqUres hqUBase
  exact ⟨D, ρ, hρSm, τ, m, hmρ, hmτ, A, fD, gD, hfD U.etale_toBase, hgD, a, hτρ, hAa, hfa,
    hfres hfUres, hgres, hga, aσ, haσA, haσZ, Uaff, jUaff, hjUaff, eAff, heAffIso, a₀, hja₀,
    heAffa₀, hAffX, hAffY⟩

/-- **The local ring of `Spec 𝒪^∧_{S, s}` is generated over a stage modulo the maximal ideal.**
Let `m : Spec 𝒪^∧_{S, s} ⟶ D` be a morphism over `S` which is an isomorphism on residue fields
at the closed point. Then every element of the local ring of `Spec 𝒪^∧_{S, s}` at the closed
point agrees with one coming from `𝒪_{D, m(z)}` modulo the maximal ideal there.

This is the hypothesis under which a map out of the local ring of a base change along `m` is a
compatible pair of maps out of the two factors. It holds because `𝒪_{D, m(z)} → 𝒪^∧_{S, s}`
carries `𝔪_{m(z)}` onto `𝔪^∧` — already `𝔪_s` does, by the completeness of the completion —
and is surjective on residue fields. -/
private lemma exists_sub_mem_map_maximalIdeal_stalkHomAt_stage
    {S D : Scheme.{u}} [IsLocallyNoetherian S] {s : S} (ρ : D ⟶ S)
    (m : specCompletedStalk S s ⟶ D) (hm : m ≫ ρ = specCompletedStalkTo S s)
    [IsIso (m.residueFieldMap (specCompletedStalkPoint S s))] :
    ∀ b : (specCompletedStalk S s).presheaf.stalk (specCompletedStalkPoint S s),
      ∃ r : D.presheaf.stalk (m (specCompletedStalkPoint S s)),
        b - m.stalkHomAt (rfl : m (specCompletedStalkPoint S s) =
            m (specCompletedStalkPoint S s)) r ∈
          (maximalIdeal (D.presheaf.stalk (m (specCompletedStalkPoint S s)))).map
            (m.stalkHomAt (rfl : m (specCompletedStalkPoint S s) =
              m (specCompletedStalkPoint S s))) := by
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have : IsLocalHom (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
  have hpoint : ρ (m (specCompletedStalkPoint S s)) = s := by
    change (m ≫ ρ) (specCompletedStalkPoint S s) = s
    rw [hm]
    exact specCompletedStalkTo_specCompletedStalkPoint S s
  have hbase : (Scheme.stalkClosedPointTo m).hom.comp (ρ.stalkHomAt hpoint) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) :=
    stalkClosedPointTo_comp_stalkHomAt m ρ
      (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) hm hpoint
  have hgen : (maximalIdeal (D.presheaf.stalk (m (specCompletedStalkPoint S s)))).map
      (Scheme.stalkClosedPointTo m).hom =
      maximalIdeal (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)) := by
    refine le_antisymm (IsLocalRing.map_maximalIdeal_le _) ?_
    rw [AdicCompletion.maximalIdeal_eq_map, ← hbase, ← Ideal.map_map]
    exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le (ρ.stalkHomAt hpoint))
  -- `𝒪_{D, d} → 𝒪^∧_{S, s}` is surjective on residue fields because `𝒪_{S, s} → 𝒪^∧_{S, s}`
  -- is, and it factors through it
  have hsurj : Function.Surjective
      (IsLocalRing.ResidueField.map (Scheme.stalkClosedPointTo m).hom) := by
    intro k
    obtain ⟨r, hr⟩ :=
      (AdicCompletion.residueField_map_bijective (S.presheaf.stalk s)).surjective k
    obtain ⟨a, rfl⟩ := residue_surjective r
    refine ⟨residue _ (ρ.stalkHomAt hpoint a), ?_⟩
    have hmap : (Scheme.stalkClosedPointTo m).hom (ρ.stalkHomAt hpoint a) =
        algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) a :=
      RingHom.congr_fun hbase a
    change residue _ ((Scheme.stalkClosedPointTo m).hom (ρ.stalkHomAt hpoint a)) = k
    rw [hmap]
    exact hr
  have hdense := exists_sub_mem_map_maximalIdeal_of_residueField_surjective
    (Scheme.stalkClosedPointTo m).hom hgen hsurj
  have hstalk := exists_sub_mem_map_maximalIdeal_of_comp_equiv
    (m.stalkMap (specCompletedStalkPoint S s)).hom
    (stalkClosedPointIso (CommRingCat.of
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)))).commRingCatIsoToRingEquiv hdense
  intro b
  rw [stalkHomAt_rfl]
  exact hstalk b

/-- **The assembly of the approximating diagram over a stage.** Given a scheme `D` over `S`
locally of finite type, a morphism `m : Spec 𝒪^∧_{S, s} ⟶ D` over `S` through which `β`
factors, and an object `A` over `D` carrying a morphism to `X ×_S D` and an **étale** morphism
to `Y ×_T D` together with a point reproducing `x` and `y_σ`, the first stage of Tag 0CAW
replaces `D` by an elementary étale neighbourhood `(V, v)` of `(S, s)` mapping to `D` through
the image of the closed point, and the base change of `A` along `V ⟶ D` is the `(W, w)` of the
diagram.

Only the leg to `Y ×_T D` is required to be étale: that is what makes `(W, w)` an elementary
étale neighbourhood of `(Y ×_{T, τ_V} V, y_τ)`, which is clause (4) of Tag 0CAW. Étaleness of
the leg to `X ×_S D` — which Tag 0GDX and Tag 0CB1 have and Tag 0CAW does not — is returned as
an implication, and is what makes `(W, w)` an elementary étale neighbourhood of `(X, x)` as
well.

The congruence of clause (5) enters through an arbitrary predicate `P` on pairs of germs, so
that the caller fixes what it means for the two routes to agree: Tag 0CAV's isomorphism for Tag
0GDX and Tag 0CB1, Tag 0CAU's one-sided congruence for Tag 0CAW. -/
private theorem exists_approximationDiagram_of_stage
    {X S Y T B Dst : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    {x : X} {s : S} {y : Y} {t : T}
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (ρ : Dst ⟶ S) [LocallyOfFiniteType ρ] (τ : Dst ⟶ T)
    (bS : S ⟶ B) (hTB : T ⟶ B) (hτρ : τ ≫ hTB = ρ ≫ bS)
    (m : specCompletedStalk S s ⟶ Dst)
    (hmρ : m ≫ ρ = specCompletedStalkTo S s)
    (β : specCompletedStalk S s ⟶ T) (hmτ : m ≫ τ = β)
    (hτm : τ (m (specCompletedStalkPoint S s)) = t)
    (hσstage : (Scheme.stalkClosedPointTo m).hom.comp (τ.stalkHomAt hτm) = σ)
    (A : Over Dst) (fD : A ⟶ (Over.pullback ρ).obj (Over.mk p))
    (gD : A ⟶ (Over.pullback τ).obj (Over.mk q))
    (hgD : Etale gD.left) (a : A.left)
    (hAa : A.hom a = m (specCompletedStalkPoint S s))
    (hfa : (fD.left ≫ pullback.fst p ρ) a = x)
    (hgres : IsIso (gD.left.residueFieldMap a))
    (hgYa : (gD.left ≫ pullback.fst q τ) a = y)
    (yσ : (pullback q β : Scheme.{u}))
    (hyσY : pullback.fst q β yσ = y)
    (hyσZ : pullback.snd q β yσ = specCompletedStalkPoint S s)
    (hga : gD.left a = baseChangeCompare q τ m β hmτ yσ)
    (aσ : (pullback A.hom m : Scheme.{u}))
    (haσA : pullback.fst A.hom m aσ = a)
    (haσZ : pullback.snd A.hom m aσ = specCompletedStalkPoint S s)
    (hAσX : (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ) aσ = x)
    (hAσY : (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ) aσ = y)
    (P : X.presheaf.stalk x → Y.presheaf.stalk y → Prop)
    (hAcong : ∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
      (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ).stalkHomAt hAσX α -
          (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ).stalkHomAt hAσY b ∈
        maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N) :
    ∃ (V : EtaleNeighborhood S s) (τV : V.scheme ⟶ T) (hτV : τV V.point = t)
      (yτ : (pullback q τV : Scheme.{u}))
      (hyτY : pullback.fst q τV yτ = y) (hyτV : pullback.snd q τV yτ = V.point)
      (Wsch : Scheme.{u}) (w : Wsch) (pW : Wsch ⟶ X) (hpW : pW w = x)
      (g : Wsch ⟶ pullback q τV)
      (hgPoint : g w = yτ) (_ : Etale g),
      V.IsElementary ∧ τV ≫ hTB = V.toBase ≫ bS ∧
        IsIso (((pullback q τV).residueFieldCongr hgPoint).inv ≫
          g.residueFieldMap w) ∧
        g ≫ pullback.snd q τV ≫ V.toBase = pW ≫ p ∧
        (Etale fD.left → IsIso ((fD.left ≫ pullback.fst p ρ).residueFieldMap a) →
          Etale pW ∧ IsIso (pW.residueFieldMap w)) ∧
        (∀ b : T.presheaf.stalk t,
          V.completionMap (σ b) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τV.stalkHomAt hτV b) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) ∧
        (∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
          Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
              (pW.stalkHomAt hpW α) =
            Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
              (g.stalkHomAt hgPoint ((pullback.fst q τV).stalkHomAt hyτY b))) ∧
        (∃ (gZ : (pullback A.hom m : Scheme.{u}) ⟶ (pullback q β : Scheme.{u}))
            (hgZ : gZ aσ = yσ),
          gZ ≫ pullback.fst q β =
              pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ ∧
            gZ ≫ pullback.snd q β = pullback.snd A.hom m ∧
            ∃ θ : ((pullback q β).presheaf.stalk yσ ⧸
                  maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N) ≃+*
                ((pullback q τV).presheaf.stalk yτ ⧸
                  maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N),
              (∀ b : Y.presheaf.stalk y,
                θ (Ideal.Quotient.mk
                    (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N)
                    ((pullback.fst q β).stalkHomAt hyσY b)) =
                  Ideal.Quotient.mk
                    (maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N)
                    ((pullback.fst q τV).stalkHomAt hyτY b)) ∧
              (∀ c : S.presheaf.stalk s,
                θ (Ideal.Quotient.mk
                    (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N)
                    ((pullback.snd q β).stalkHomAt hyσZ
                      ((specCompletedStalkTo S s).stalkHomAt
                        (specCompletedStalkTo_specCompletedStalkPoint S s) c))) =
                  Ideal.Quotient.mk
                    (maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N)
                    ((pullback.snd q τV).stalkHomAt hyτV (V.stalkHom c))) ∧
              ∀ (α : X.presheaf.stalk x) (ξ : (pullback q β).presheaf.stalk yσ)
                  (z : (pullback q τV).presheaf.stalk yτ),
                (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ).stalkHomAt hAσX α -
                    gZ.stalkHomAt hgZ ξ ∈
                  maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N →
                θ (Ideal.Quotient.mk
                    (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N) ξ) =
                  Ideal.Quotient.mk
                    (maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N) z →
                Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
                    (g.stalkHomAt hgPoint z) =
                  Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
                    (pW.stalkHomAt hpW α)) ∧
        ∃ (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
            V.scheme.residueField V.point)
          (eFiber : (pullback.snd q β).fiber (specCompletedStalkPoint S s) ≅
            (pullback.snd q τV).fiber V.point),
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              specCompletedStalkTo S s) ∧
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τV =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              β) ∧
          (eFiber.hom ≫ (pullback.snd q τV).fiberι V.point ≫ pullback.fst q τV =
            (pullback.snd q β).fiberι (specCompletedStalkPoint S s) ≫ pullback.fst q β) ∧
          (eFiber.hom ≫ (pullback.snd q τV).fiberToSpecResidueField V.point =
            (pullback.snd q β).fiberToSpecResidueField (specCompletedStalkPoint S s) ≫
              Spec.map eBase.inv) ∧
          (eFiber.hom (((pullback.snd q β).fiberHomeo
              (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩) =
            ((pullback.snd q τV).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  classical
  have := hgD
  have := hgres
  -- the elementary étale neighbourhood replacing the stage
  obtain ⟨V, ι, hι, hVel, hιρ, hιres, hcong⟩ :=
    exists_elementaryEtaleNeighborhood_over_stage ρ m hmρ hG N hN
  have := hιres
  let τV : V.scheme ⟶ T := ι ≫ τ
  have hτV : τV V.point = t := by
    change τ (ι V.point) = t
    rwa [hι]
  have hτVB : τV ≫ hTB = V.toBase ≫ bS := by
    change (ι ≫ τ) ≫ hTB = V.toBase ≫ bS
    rw [Category.assoc, hτρ, ← Category.assoc, hιρ]
  -- the residue field of the base is the same on both sides
  have : IsIso (m.residueFieldMap (specCompletedStalkPoint S s)) :=
    isIso_residueFieldMap_of_comp_specCompletedStalkTo ρ m hmρ
  obtain ⟨eBase, heBase⟩ := exists_residueFieldIso_of_common_point m ι
    (specCompletedStalkPoint S s) V.point hι.symm
  have heBaseS : Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
      (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
        specCompletedStalkTo S s := by
    rw [← hιρ, ← hmρ]
    exact (reassoc_of% heBase) ρ
  have heBaseT : Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τV =
      (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫ β := by
    rw [← hmτ]
    exact (reassoc_of% heBase) τ
  obtain ⟨yτ, hyτY, hyτV, eFiber, heFiberY, heFiberBase, heFiberPoint⟩ :=
    exists_fiberIso_point_of_residueFieldIso q β τV (specCompletedStalkPoint S s) V.point
      eBase heBaseT y yσ hyσY hyσZ
  -- the base change of `A` along `ι`
  obtain ⟨w, hwA, hwV, hwres⟩ :=
    exists_pullback_point_with_fst_residueFieldMap_isIso A.hom ι a V.point
      (hAa.trans hι.symm) (IsIso.comp_isIso' (Dst.residueFieldCongr _).isIso_inv hιres)
  let Wobj : Over V.scheme := (Over.pullback ι).obj A
  let eXV := pullbackTransitionIso ρ ι V.toBase hιρ (Over.mk p)
  let eYV := pullbackTransitionIso τ ι τV rfl (Over.mk q)
  let fW : Wobj ⟶ (Over.pullback V.toBase).obj (Over.mk p) :=
    (Over.pullback ι).map fD ≫ eXV.hom
  let gW : Wobj ⟶ (Over.pullback τV).obj (Over.mk q) :=
    (Over.pullback ι).map gD ≫ eYV.hom
  have : Etale ((Over.pullback ι).map gD).left :=
    MorphismProperty.overPullbackMap ι _ hgD
  have : IsIso eXV.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eXV.hom))
  have : IsIso eYV.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eYV.hom))
  have : Etale gW.left := by
    change Etale (((Over.pullback ι).map gD).left ≫ eYV.hom.left); infer_instance
  let pW : Wobj.left ⟶ X := fW.left ≫ pullback.fst p V.toBase
  have hpWet : Etale fD.left → Etale pW := fun hfD => by
    have : Etale ((Over.pullback ι).map fD).left :=
      MorphismProperty.overPullbackMap ι _ hfD
    have : Etale fW.left := by
      change Etale (((Over.pullback ι).map fD).left ≫ eXV.hom.left); infer_instance
    dsimp only [pW]; infer_instance
  have hpW : pW = pullback.fst A.hom ι ≫ fD.left ≫ pullback.fst p ρ := by
    have h1 : eXV.hom.left ≫ pullback.fst p V.toBase =
        pullback.fst ((Over.pullback ρ).obj (Over.mk p)).hom ι ≫ pullback.fst p ρ :=
      pullbackTransitionIso_hom_fst _ _ _ _ _
    have h2 : ((Over.pullback ι).map fD).left ≫
        pullback.fst ((Over.pullback ρ).obj (Over.mk p)).hom ι =
        pullback.fst A.hom ι ≫ fD.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    change (((Over.pullback ι).map fD).left ≫ eXV.hom.left) ≫ pullback.fst p V.toBase = _
    rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc]
  have hpWpoint : pW w = x := by
    rw [hpW]
    change (fD.left ≫ pullback.fst p ρ) (pullback.fst A.hom ι w) = x
    rw [hwA]
    exact hfa
  have hpWres : IsIso ((fD.left ≫ pullback.fst p ρ).residueFieldMap a) →
      IsIso (pW.residueFieldMap w) := fun hfres => by
    have h1 : IsIso ((fD.left ≫ pullback.fst p ρ).residueFieldMap
        (pullback.fst A.hom ι w)) := by rwa [hwA]
    rw [hpW, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' h1 hwres
  -- the comparison of `Y ×_{T, τ_V} V` with `Y ×_{T, τ} D`
  let bV := baseChangeCompare q τ ι τV rfl
  let dY := baseChangeCompare q τ m β hmτ
  have hgWbV : gW.left ≫ bV = pullback.fst A.hom ι ≫ gD.left := by
    have h2 : ((Over.pullback ι).map gD).left ≫
        pullback.fst ((Over.pullback τ).obj (Over.mk q)).hom ι =
        pullback.fst A.hom ι ≫ gD.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    change (((Over.pullback ι).map gD).left ≫ eYV.hom.left) ≫
      (eYV.inv.left ≫ pullback.fst (pullback.snd q τ) ι) = _
    rw [Category.assoc, ← Category.assoc eYV.hom.left, ← Over.comp_left, eYV.hom_inv_id,
      Over.id_left, Category.id_comp]
    exact h2
  have heFiberD : eFiber.hom ≫ (pullback.snd q τV).fiberι V.point ≫ bV =
      (pullback.snd q β).fiberι (specCompletedStalkPoint S s) ≫ dY := by
    apply pullback.hom_ext (f := q) (g := τ)
    · simp only [Category.assoc]
      rw [baseChangeCompare_fst, baseChangeCompare_fst]
      simpa only [Category.assoc] using heFiberY
    · simp only [Category.assoc]
      rw [baseChangeCompare_snd, baseChangeCompare_snd]
      rw [← Category.assoc ((pullback.snd q τV).fiberι V.point),
        (pullback.snd q τV).fiber_fac V.point]
      rw [← Category.assoc ((pullback.snd q β).fiberι (specCompletedStalkPoint S s)),
        (pullback.snd q β).fiber_fac (specCompletedStalkPoint S s)]
      simp only [Category.assoc]
      rw [← Category.assoc eFiber.hom, heFiberBase]
      simp only [Category.assoc]
      rw [heBase]
  have hyτD : bV yτ = dY yσ := by
    have H := congrArg (fun k : ((pullback.snd q β).fiber
      (specCompletedStalkPoint S s)) ⟶ (pullback q τ : Scheme.{u}) => k
      (((pullback.snd q β).fiberHomeo (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩))
      heFiberD
    simpa only [Scheme.Hom.comp_apply, heFiberPoint,
      Scheme.Hom.fiberι_fiberHomeo_symm] using H
  have hgWpointD : bV (gW.left w) = dY yσ := by
    change (gW.left ≫ bV) w = dY yσ
    rw [hgWbV]
    change gD.left (pullback.fst A.hom ι w) = dY yσ
    rw [hwA]
    exact hga
  have hgWsnd : pullback.snd q τV (gW.left w) = V.point := by
    have hw : gW.left ≫ pullback.snd q τV = Wobj.hom := Over.w gW
    change (gW.left ≫ pullback.snd q τV) w = V.point
    rw [hw]
    exact hwV
  have hgPoint : gW.left w = yτ :=
    eq_of_baseChangeCompare_eq q τ ι τV rfl V.point hιres (hgWpointD.trans hyτD.symm) hgWsnd
      hyτV
  have : IsIso (gW.left.residueFieldMap w) := by
    have hcomp : IsIso ((gW.left ≫ bV).residueFieldMap w) := by
      rw [hgWbV, Scheme.residueFieldMap_comp]
      have h1 : IsIso (gD.left.residueFieldMap (pullback.fst A.hom ι w)) := by rwa [hwA]
      exact IsIso.comp_isIso' h1 hwres
    exact isIso_residueFieldMap_of_comp_left gW.left bV w
  -- the base change of `A` along `m`, with its leg to `Y_β`: this is the pointed scheme the
  -- congruence of clause (5) is handed on, and the one whose local ring is compared with that
  -- of the base change along `ι`
  have hgZcond : (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ) ≫ q =
      pullback.snd A.hom m ≫ β := by
    rw [← hmτ]
    calc (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ) ≫ q
        = pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ ≫ q := by
          simp only [Category.assoc]
      _ = pullback.fst A.hom m ≫ (gD.left ≫ pullback.snd q τ) ≫ τ := by
          rw [pullback.condition]
          simp only [Category.assoc]
      _ = (pullback.fst A.hom m ≫ A.hom) ≫ τ := by
          rw [show gD.left ≫ pullback.snd q τ = A.hom from Over.w gD]
          simp only [Category.assoc]
      _ = (pullback.snd A.hom m ≫ m) ≫ τ := congrArg (· ≫ τ) pullback.condition
      _ = pullback.snd A.hom m ≫ m ≫ τ := by simp only [Category.assoc]
  let gZ : (pullback A.hom m : Scheme.{u}) ⟶ (pullback q β : Scheme.{u}) :=
    pullback.lift (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ)
      (pullback.snd A.hom m) hgZcond
  have hgZfst : gZ ≫ pullback.fst q β =
      pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ := pullback.lift_fst _ _ _
  have hgZsnd : gZ ≫ pullback.snd q β = pullback.snd A.hom m := pullback.lift_snd _ _ _
  let eYZ := pullbackTransitionIso τ m β hmτ (Over.mk q)
  let gZover : (Over.pullback m).obj A ⟶ (Over.pullback β).obj (Over.mk q) :=
    (Over.pullback m).map gD ≫ eYZ.hom
  have : Etale ((Over.pullback m).map gD).left :=
    MorphismProperty.overPullbackMap m _ hgD
  have : IsIso eYZ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eYZ.hom))
  have : Etale gZover.left := by
    change Etale (((Over.pullback m).map gD).left ≫ eYZ.hom.left); infer_instance
  have hgZoverdY : gZover.left ≫ dY = pullback.fst A.hom m ≫ gD.left := by
    have h2 : ((Over.pullback m).map gD).left ≫
        pullback.fst ((Over.pullback τ).obj (Over.mk q)).hom m =
        pullback.fst A.hom m ≫ gD.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    change (((Over.pullback m).map gD).left ≫ eYZ.hom.left) ≫
      (eYZ.inv.left ≫ pullback.fst (pullback.snd q τ) m) = _
    rw [Category.assoc, ← Category.assoc eYZ.hom.left, ← Over.comp_left, eYZ.hom_inv_id,
      Over.id_left, Category.id_comp]
    exact h2
  have heqZ : gZ = gZover.left := by
    refine pullback.hom_ext ?_ ?_
    · have h1 : dY ≫ pullback.fst q τ = pullback.fst q β :=
        baseChangeCompare_fst q τ m β hmτ
      rw [hgZfst, ← h1, ← Category.assoc gZover.left dY (pullback.fst q τ), hgZoverdY,
        Category.assoc]
    · rw [hgZsnd]
      exact (Over.w gZover).symm
  have : Etale gZ := by rw [heqZ]; infer_instance
  have hgZsndpt : pullback.snd q β (gZ aσ) = specCompletedStalkPoint S s := by
    change (gZ ≫ pullback.snd q β) aσ = _
    rw [hgZsnd]
    exact haσZ
  have hgZpoint : gZ aσ = yσ := by
    refine eq_of_baseChangeCompare_eq q τ m β hmτ (specCompletedStalkPoint S s) inferInstance ?_
      hgZsndpt hyσZ
    change (gZ ≫ dY) aσ = dY yσ
    rw [heqZ, hgZoverdY]
    change gD.left (pullback.fst A.hom m aσ) = dY yσ
    rw [haσA]
    exact hga
  have : IsIso ((pullback.fst A.hom m).residueFieldMap aσ) := by
    have : IsIso (m.residueFieldMap (pullback.snd A.hom m aσ)) := by
      rw [haσZ]; infer_instance
    exact isIso_residueFieldMap_pullback_fst _ _ _
  have : IsIso (gZ.residueFieldMap aσ) := by
    have hcomp : IsIso ((gZ ≫ dY).residueFieldMap aσ) := by
      rw [heqZ, hgZoverdY, Scheme.residueFieldMap_comp]
      have h1 : IsIso (gD.left.residueFieldMap (pullback.fst A.hom m aσ)) := by
        rwa [haσA]
      exact IsIso.comp_isIso' h1 inferInstance
    exact isIso_residueFieldMap_of_comp_left gZ dY aσ
  -- the Noetherian local rings in play
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have : IsNoetherianRing (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)) := (completion_isGRing (S.presheaf.stalk s) hG).1
  have : IsLocallyNoetherian (specCompletedStalk S s) := inferInstance
  have : IsLocalRing ((specCompletedStalk S s).presheaf.stalk
    (specCompletedStalkPoint S s)) := inferInstance
  have : IsLocallyNoetherian V.scheme := LocallyOfFiniteType.isLocallyNoetherian V.toBase
  have : IsLocallyNoetherian (pullback q τV) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q τV)
  have : IsLocallyNoetherian ((Over.pullback τV).obj (Over.mk q)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q τV)
  have : IsLocallyNoetherian (pullback q β) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q β)
  have : IsLocallyNoetherian Wobj.left := LocallyOfFiniteType.isLocallyNoetherian gW.left
  have : IsLocallyNoetherian (pullback A.hom m) :=
    LocallyOfFiniteType.isLocallyNoetherian gZ
  -- the two étale legs identify the truncated local rings of `Y_β` and of `Y ×_{T, τ_V} V`
  -- with those of the two base changes of `A`
  obtain ⟨εZ, -, hεZmk⟩ := exists_ringEquiv_quotient_pow_of_etale gZ hgZpoint inferInstance N
  obtain ⟨εW, -, hεWmk⟩ :=
    exists_ringEquiv_quotient_pow_of_etale gW.left hgPoint inferInstance N
  -- the truncated local rings of the two bases, identified by clause (3)
  let eZiso := (stalkClosedPointIso (CommRingCat.of
    (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s)))).commRingCatIsoToRingEquiv
  have hcmp : ((AdicCompletion.evalₐ
          (maximalIdeal (V.scheme.presheaf.stalk V.point)) N).toRingHom.comp
        (V.completionMap.comp eZiso.toRingHom)).comp
        (m.stalkHomAt (rfl : m (specCompletedStalkPoint S s) =
          m (specCompletedStalkPoint S s))) =
      (Ideal.Quotient.mk (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)).comp
        (ι.stalkHomAt hι) := by
    refine RingHom.ext fun α => ?_
    have hz : eZiso (m.stalkHomAt (rfl : m (specCompletedStalkPoint S s) =
        m (specCompletedStalkPoint S s)) α) = (Scheme.stalkClosedPointTo m).hom α := by
      rw [stalkHomAt_rfl]
      rfl
    have h0 : AdicCompletion.evalₐ (maximalIdeal (V.scheme.presheaf.stalk V.point)) N
        (V.completionMap ((Scheme.stalkClosedPointTo m).hom α) -
          algebraMap (V.scheme.presheaf.stalk V.point)
            (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
              (V.scheme.presheaf.stalk V.point)) (ι.stalkHomAt hι α)) = 0 :=
      (evalₐ_eq_zero_iff_mem_map_pow
        (maximalIdeal (V.scheme.presheaf.stalk V.point)).fg_of_isNoetherianRing N _).mpr
        (hcong α)
    rw [map_sub, sub_eq_zero, evalₐ_algebraMap] at h0
    change AdicCompletion.evalₐ (maximalIdeal (V.scheme.presheaf.stalk V.point)) N
      (V.completionMap (eZiso (m.stalkHomAt (rfl : m (specCompletedStalkPoint S s) =
        m (specCompletedStalkPoint S s)) α))) = _
    rw [hz]
    exact h0
  have hVres : IsIso (V.toBase.residueFieldMap V.point) :=
    (EtaleNeighborhood.isElementary_iff V).mp hVel
  obtain ⟨εV, hεV, -⟩ := exists_ringEquiv_quotient_pow_of_etale V.toBase V.map_point hVres N
  let eBaseTr := (quotientPowEquiv eZiso N).trans
    ((completionQuotientEquiv (S.presheaf.stalk s) N).trans εV)
  have heBaseTr : ∀ ζ : (specCompletedStalk S s).presheaf.stalk
        (specCompletedStalkPoint S s),
      eBaseTr (Ideal.Quotient.mk (maximalIdeal ((specCompletedStalk S s).presheaf.stalk
          (specCompletedStalkPoint S s)) ^ N) ζ) =
        AdicCompletion.evalₐ (maximalIdeal (V.scheme.presheaf.stalk V.point)) N
          (V.completionMap (eZiso ζ)) := fun ζ =>
    (congrArg (fun ρ' => εV (completionQuotientEquiv (S.presheaf.stalk s) N ρ'))
        (quotientPowEquiv_mk eZiso N ζ)).trans
      ((congrArg εV (completionQuotientEquiv_quotient_mk (S.presheaf.stalk s) N
          (eZiso ζ))).trans (hεV (eZiso ζ)))
  have heBaseTrStage : ∀ r : Dst.presheaf.stalk (m (specCompletedStalkPoint S s)),
      eBaseTr (Ideal.Quotient.mk (maximalIdeal ((specCompletedStalk S s).presheaf.stalk
            (specCompletedStalkPoint S s)) ^ N)
          (m.stalkHomAt (rfl : m (specCompletedStalkPoint S s) =
            m (specCompletedStalkPoint S s)) r)) =
        Ideal.Quotient.mk (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)
          (ι.stalkHomAt hι r) := fun r =>
    (heBaseTr _).trans (RingHom.congr_fun hcmp r)
  -- the maximal ideal of `𝒪_{V, v}` is generated by that of the stage
  have hρpoint : ρ (m (specCompletedStalkPoint S s)) = s := by
    change (m ≫ ρ) (specCompletedStalkPoint S s) = s
    rw [hmρ]
    exact specCompletedStalkTo_specCompletedStalkPoint S s
  have hVstalk : (ι.stalkHomAt hι).comp (ρ.stalkHomAt hρpoint) = V.stalkHom :=
    (Scheme.Hom.stalkHomAt_comp ι ρ hι hρpoint).symm.trans
      (stalkHomAt_congr hιρ _ V.map_point)
  have hBV : ∀ b : V.scheme.presheaf.stalk V.point,
      ∃ r : Dst.presheaf.stalk (m (specCompletedStalkPoint S s)),
        b - ι.stalkHomAt hι r ∈
          (maximalIdeal (Dst.presheaf.stalk (m (specCompletedStalkPoint S s)))).map
            (ι.stalkHomAt hι) :=
    exists_sub_mem_map_maximalIdeal_of_comp_left (ρ.stalkHomAt hρpoint) (ι.stalkHomAt hι)
      (by
        rw [hVstalk]
        exact exists_sub_mem_map_maximalIdeal_of_residueField_surjective V.stalkHom
          (map_maximalIdeal_stalkHom V)
          ((bijective_residueField_map_stalkHomAt_iff _ _ V.map_point).mpr hVres).surjective)
  -- the comparison of the two base changes of `A`, as an isomorphism of truncations
  obtain ⟨θA, hθAfst, hθAsnd⟩ :=
    exists_ringEquiv_quotient_pow_stalk_pullback_comparison A.hom m ι
      aσ haσA haσZ w hwA hwV hAa rfl hι hN
      (exists_sub_mem_map_maximalIdeal_stalkHomAt_stage ρ m hmρ) hBV eBaseTr heBaseTrStage
  -- the two routes out of `𝒪_{A, a}`
  have hXA : (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ).stalkHomAt hAσX =
      ((pullback.fst A.hom m).stalkHomAt haσA).comp
        ((fD.left ≫ pullback.fst p ρ).stalkHomAt hfa) :=
    Scheme.Hom.stalkHomAt_comp (pullback.fst A.hom m)
      (fD.left ≫ pullback.fst p ρ) haσA hfa
  have hYA : (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ).stalkHomAt hAσY =
      ((pullback.fst A.hom m).stalkHomAt haσA).comp
        ((gD.left ≫ pullback.fst q τ).stalkHomAt hgYa) :=
    Scheme.Hom.stalkHomAt_comp (pullback.fst A.hom m)
      (gD.left ≫ pullback.fst q τ) haσA hgYa
  -- the same two routes read through `W`
  have hwX : (pullback.fst A.hom ι ≫ fD.left ≫ pullback.fst p ρ) w = x := by
    change (fD.left ≫ pullback.fst p ρ) (pullback.fst A.hom ι w) = x
    rwa [hwA]
  have hXW : pW.stalkHomAt hpWpoint = ((pullback.fst A.hom ι).stalkHomAt hwA).comp
      ((fD.left ≫ pullback.fst p ρ).stalkHomAt hfa) :=
    (stalkHomAt_congr hpW hpWpoint hwX).trans
      (Scheme.Hom.stalkHomAt_comp (pullback.fst A.hom ι)
        (fD.left ≫ pullback.fst p ρ) hwA hfa)
  have hgWfst : gW.left ≫ pullback.fst q τV =
      pullback.fst A.hom ι ≫ gD.left ≫ pullback.fst q τ := by
    have h1 : bV ≫ pullback.fst q τ = pullback.fst q τV :=
      baseChangeCompare_fst q τ ι τV rfl
    rw [← h1, ← Category.assoc, hgWbV, Category.assoc]
  have hYW := stalkHomAt_comp_eq_of_comp_eq hgWfst hgPoint hyτY hwA hgYa
  have hWbase : (pullback.snd A.hom ι).stalkHomAt hwV =
      (gW.left.stalkHomAt hgPoint).comp ((pullback.snd q τV).stalkHomAt hyτV) :=
    (stalkHomAt_congr (Over.w gW) hgWsnd hwV).symm.trans
      (Scheme.Hom.stalkHomAt_comp gW.left (pullback.snd q τV) hgPoint hyτV)
  -- and the two routes read through the base change of `A` along `m`
  have hYZ := stalkHomAt_comp_eq_of_comp_eq hgZfst hgZpoint hyσY haσA hgYa
  have hZsndHom : (gZ.stalkHomAt hgZpoint).comp ((pullback.snd q β).stalkHomAt hyσZ) =
      (pullback.snd A.hom m).stalkHomAt haσZ :=
    (Scheme.Hom.stalkHomAt_comp gZ (pullback.snd q β) hgZpoint hyσZ).symm.trans
      (stalkHomAt_congr hgZsnd hgZsndpt haσZ)
  refine ⟨V, τV, hτV, yτ, hyτY, hyτV, Wobj.left, w, pW, hpWpoint, gW.left, hgPoint,
    inferInstance, hVel, hτVB, ?_, ?_, fun hfD hfres => ⟨hpWet hfD, hpWres hfres⟩, ?_, ?_,
    ⟨gZ, hgZpoint, hgZfst, hgZsnd, εZ.trans (θA.trans εW.symm), ?_, ?_, ?_⟩,
    eBase, eFiber, heBaseS, heBaseT, heFiberY, heFiberBase, heFiberPoint⟩
  · exact IsIso.comp_isIso' ((pullback q τV).residueFieldCongr hgPoint).isIso_inv
      inferInstance
  · change gW.left ≫ ((Over.pullback τV).obj (Over.mk q)).hom ≫ V.toBase =
      (fW.left ≫ pullback.fst p V.toBase) ≫ p
    rw [← Category.assoc, Over.w gW, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ V.toBase) (Over.w fW).symm
  · intro b
    have h := hcong (τ.stalkHomAt hτm b)
    have h1 : (Scheme.stalkClosedPointTo m).hom (τ.stalkHomAt hτm b) = σ b :=
      RingHom.congr_fun hσstage b
    have h2 : ι.stalkHomAt hι (τ.stalkHomAt hτm b) = τV.stalkHomAt hτV b :=
      (RingHom.congr_fun (Scheme.Hom.stalkHomAt_comp ι τ hι hτm) b).symm
    rw [h1, h2] at h
    exact h
  · -- clause (5) through the predicate `P`: the comparison of the two base changes of `A`
    -- identifies the two routes out of `𝒪_{X, x}` and out of `𝒪_{Y, y}`
    intro α b hP
    have hd : ((pullback.fst A.hom m).stalkHomAt haσA)
          ((fD.left ≫ pullback.fst p ρ).stalkHomAt hfa α) -
        ((pullback.fst A.hom m).stalkHomAt haσA)
          ((gD.left ≫ pullback.fst q τ).stalkHomAt hgYa b) ∈
          maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N := by
      have h := hAcong α b hP
      rw [hXA, hYA] at h
      exact h
    have h4 := congrArg θA ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hd)
    rw [hθAfst, hθAfst] at h4
    exact (congrArg (Ideal.Quotient.mk (maximalIdeal (Wobj.left.presheaf.stalk w) ^ N))
        (RingHom.congr_fun hXW α)).trans
      (h4.trans (congrArg (Ideal.Quotient.mk (maximalIdeal (Wobj.left.presheaf.stalk w) ^ N))
        (RingHom.congr_fun hYW b)).symm)
  · -- the identification is compatible with the two maps from `𝒪_{Y, y}`
    intro b
    refine εW.injective ?_
    have hL : εW ((εZ.trans (θA.trans εW.symm)) (Ideal.Quotient.mk
          (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N)
          ((pullback.fst q β).stalkHomAt hyσY b))) =
        θA (εZ (Ideal.Quotient.mk (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N)
          ((pullback.fst q β).stalkHomAt hyσY b))) := εW.apply_symm_apply _
    refine hL.trans ?_
    refine (congrArg θA (hεZmk ((pullback.fst q β).stalkHomAt hyσY b))).trans ?_
    refine (congrArg (fun ζ => θA (Ideal.Quotient.mk
        (maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N) ζ))
        (RingHom.congr_fun hYZ b)).trans ?_
    refine (hθAfst ((gD.left ≫ pullback.fst q τ).stalkHomAt hgYa b)).trans ?_
    refine (congrArg (Ideal.Quotient.mk (maximalIdeal (Wobj.left.presheaf.stalk w) ^ N))
      (RingHom.congr_fun hYW b).symm).trans ?_
    exact (hεWmk ((pullback.fst q τV).stalkHomAt hyτY b)).symm
  · -- and with the two maps from `𝒪_{S, s}`
    intro c
    refine εW.injective ?_
    have hzz : eZiso ((specCompletedStalkTo S s).stalkHomAt
        (specCompletedStalkTo_specCompletedStalkPoint S s) c) =
        algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) c :=
      (congrArg eZiso (RingHom.congr_fun (stalkHomAt_specCompletedStalkTo S s) c)).trans
        (RingHom.congr_fun (congrArg CommRingCat.Hom.hom (stalkClosedPointIso
          (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
            (S.presheaf.stalk s)))).inv_hom_id)
          (algebraMap (S.presheaf.stalk s) (AdicCompletion
            (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) c))
    have hζ : eBaseTr (Ideal.Quotient.mk (maximalIdeal
          ((specCompletedStalk S s).presheaf.stalk (specCompletedStalkPoint S s)) ^ N)
          ((specCompletedStalkTo S s).stalkHomAt
            (specCompletedStalkTo_specCompletedStalkPoint S s) c)) =
        Ideal.Quotient.mk (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)
          (V.stalkHom c) :=
      (heBaseTr _).trans
        ((congrArg (fun ζ => AdicCompletion.evalₐ
            (maximalIdeal (V.scheme.presheaf.stalk V.point)) N (V.completionMap ζ)) hzz).trans
          ((congrArg (AdicCompletion.evalₐ
              (maximalIdeal (V.scheme.presheaf.stalk V.point)) N)
              (completionMapAt_algebraMap V.toBase V.map_point c)).trans
            (evalₐ_algebraMap _ N _)))
    have hL : εW ((εZ.trans (θA.trans εW.symm)) (Ideal.Quotient.mk
          (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N)
          ((pullback.snd q β).stalkHomAt hyσZ ((specCompletedStalkTo S s).stalkHomAt
            (specCompletedStalkTo_specCompletedStalkPoint S s) c)))) =
        θA (εZ (Ideal.Quotient.mk (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N)
          ((pullback.snd q β).stalkHomAt hyσZ ((specCompletedStalkTo S s).stalkHomAt
            (specCompletedStalkTo_specCompletedStalkPoint S s) c)))) :=
      εW.apply_symm_apply _
    refine hL.trans ?_
    refine (congrArg θA (hεZmk ((pullback.snd q β).stalkHomAt hyσZ
      ((specCompletedStalkTo S s).stalkHomAt
        (specCompletedStalkTo_specCompletedStalkPoint S s) c)))).trans ?_
    refine (congrArg (fun ζ => θA (Ideal.Quotient.mk
        (maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N) ζ))
        (RingHom.congr_fun hZsndHom ((specCompletedStalkTo S s).stalkHomAt
          (specCompletedStalkTo_specCompletedStalkPoint S s) c))).trans ?_
    refine (hθAsnd ((specCompletedStalkTo S s).stalkHomAt
      (specCompletedStalkTo_specCompletedStalkPoint S s) c)).trans ?_
    refine (congrArg (quotientPowMap ((pullback.snd A.hom ι).stalkHomAt hwV) N) hζ).trans ?_
    refine (quotientPowMap_mk ((pullback.snd A.hom ι).stalkHomAt hwV) N (V.stalkHom c)).trans ?_
    refine (congrArg (Ideal.Quotient.mk (maximalIdeal (Wobj.left.presheaf.stalk w) ^ N))
      (RingHom.congr_fun hWbase (V.stalkHom c))).trans ?_
    exact (hεWmk ((pullback.snd q τV).stalkHomAt hyτV (V.stalkHom c))).symm
  · -- clause (5): the square of Tag 0CAW commutes
    intro α ξ z hcongξ hz
    have h1 : θA (εZ (Ideal.Quotient.mk
          (maximalIdeal ((pullback q β).presheaf.stalk yσ) ^ N) ξ)) =
        Ideal.Quotient.mk (maximalIdeal (Wobj.left.presheaf.stalk w) ^ N)
          (gW.left.stalkHomAt hgPoint z) :=
      (εW.apply_symm_apply _).symm.trans ((congrArg εW hz).trans (hεWmk z))
    have h1' : θA (Ideal.Quotient.mk
          (maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N)
          (gZ.stalkHomAt hgZpoint ξ)) =
        Ideal.Quotient.mk (maximalIdeal (Wobj.left.presheaf.stalk w) ^ N)
          (gW.left.stalkHomAt hgPoint z) :=
      (congrArg θA (hεZmk ξ)).symm.trans h1
    have hd : ((pullback.fst A.hom m).stalkHomAt haσA)
          ((fD.left ≫ pullback.fst p ρ).stalkHomAt hfa α) -
        gZ.stalkHomAt hgZpoint ξ ∈
          maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N := by
      have h := hcongξ
      rw [hXA] at h
      exact h
    have h4 := congrArg θA ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hd)
    rw [hθAfst] at h4
    exact (h4.trans h1').symm.trans
      (congrArg (Ideal.Quotient.mk (maximalIdeal (Wobj.left.presheaf.stalk w) ^ N))
        (RingHom.congr_fun hXW α)).symm

/-- **The approximating diagram of Tag 0CAW from a pointed span over `Spec 𝒪^∧_{S, s}`.**
This is the whole of the construction behind Tags 0GDX, 0CB1 and 0CAW, with the step that
produces its input left to the caller. The input is a pointed scheme `(Usch, u)` over
`Spec 𝒪^∧_{S, s}` with a morphism `fU` to `X ×_S Spec 𝒪^∧_{S, s}`, an **étale** morphism `gU` to
`Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` which is residually trivial at `u`, and a congruence modulo
`𝔪_u ^ N` between the two routes out of `𝒪_{X, x}` and `𝒪_{Y, y}` — expressed through an
arbitrary predicate `P`, so that the caller fixes what the two routes are compared by.

The output is the diagram of Tag 0CAW: an elementary étale neighbourhood `(V, v)` of `(S, s)`, a
morphism `τ : V ⟶ T` over `B` carrying `v` to `t` whose square with `σ` commutes modulo
`𝔪_v ^ N`, a point `y_τ` of `Y ×_{T, τ} V` over `y` and `v`, a pointed scheme `(Wsch, w)` étale
and residually trivial over `(Y ×_{T, τ} V, y_τ)`, a morphism `pW : Wsch ⟶ X` carrying `w` to
`x` and compatible over `S`, the congruence of clause (5) read through `P`, and the
identification of the closed fibres.

Étaleness of `fU`, which Tags 0GDX and 0CB1 have from Tag 0CAV and Tag 0CAW does not have, is
returned as an implication: with it `(Wsch, w)` is an elementary étale neighbourhood of `(X, x)`
as well. -/
private theorem exists_approximationDiagram_over_base_of_span
    {X S Y T B : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsLocallyNoetherian T]
    (bS : S ⟶ B) (hTB : T ⟶ B) [LocallyOfFinitePresentation hTB]
    {x : X} {s : S} {y : Y} {t : T}
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (hβB : relativeBaseChangeMorphism s σ ≫ hTB = specCompletedStalkTo S s ≫ bS)
    (xσ : (pullback p (specCompletedStalkTo S s) : Scheme.{u}))
    (hxσX : pullback.fst p (specCompletedStalkTo S s) xσ = x)
    (hxσZ : pullback.snd p (specCompletedStalkTo S s) xσ = specCompletedStalkPoint S s)
    (yσ : (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hyσY : pullback.fst q (relativeBaseChangeMorphism s σ) yσ = y)
    (hyσZ : pullback.snd q (relativeBaseChangeMorphism s σ) yσ =
      specCompletedStalkPoint S s)
    (Usch : Scheme.{u}) (u : Usch)
    (fU : Usch ⟶ (pullback p (specCompletedStalkTo S s) : Scheme.{u})) (hfU : fU u = xσ)
    (gU : Usch ⟶ (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hgUEt : Etale gU) (hgU : gU u = yσ) (hgUres : IsIso (gU.residueFieldMap u))
    (hUBase : gU ≫ pullback.snd q (relativeBaseChangeMorphism s σ) =
      fU ≫ pullback.snd p (specCompletedStalkTo S s))
    (P : X.presheaf.stalk x → Y.presheaf.stalk y → Prop)
    (hUX : (fU ≫ pullback.fst p (specCompletedStalkTo S s)) u = x)
    (hUY : (gU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)) u = y)
    (hUcong : ∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
      (fU ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α -
          (gU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hUY b ∈
        maximalIdeal (Usch.presheaf.stalk u) ^ N) :
    ∃ (V : EtaleNeighborhood S s) (τV : V.scheme ⟶ T) (hτV : τV V.point = t)
      (yτ : (pullback q τV : Scheme.{u}))
      (hyτY : pullback.fst q τV yτ = y) (hyτV : pullback.snd q τV yτ = V.point)
      (Wsch : Scheme.{u}) (w : Wsch) (pW : Wsch ⟶ X) (hpW : pW w = x)
      (g : Wsch ⟶ pullback q τV)
      (hgPoint : g w = yτ) (_ : Etale g),
      V.IsElementary ∧ τV ≫ hTB = V.toBase ≫ bS ∧
        IsIso (((pullback q τV).residueFieldCongr hgPoint).inv ≫
          g.residueFieldMap w) ∧
        g ≫ pullback.snd q τV ≫ V.toBase = pW ≫ p ∧
        (Etale fU →
          IsIso ((fU ≫ pullback.fst p (specCompletedStalkTo S s)).residueFieldMap u) →
          Etale pW ∧ IsIso (pW.residueFieldMap w)) ∧
        (∀ b : T.presheaf.stalk t,
          V.completionMap (σ b) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τV.stalkHomAt hτV b) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) ∧
        (∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
          Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
              (pW.stalkHomAt hpW α) =
            Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
              (g.stalkHomAt hgPoint ((pullback.fst q τV).stalkHomAt hyτY b))) ∧
        ∃ (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
            V.scheme.residueField V.point)
          (eFiber : (pullback.snd q (relativeBaseChangeMorphism s σ)).fiber
              (specCompletedStalkPoint S s) ≅
            (pullback.snd q τV).fiber V.point),
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              specCompletedStalkTo S s) ∧
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τV =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              relativeBaseChangeMorphism s σ) ∧
          (eFiber.hom ≫ (pullback.snd q τV).fiberι V.point ≫ pullback.fst q τV =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberι
                (specCompletedStalkPoint S s) ≫
              pullback.fst q (relativeBaseChangeMorphism s σ)) ∧
          (eFiber.hom ≫ (pullback.snd q τV).fiberToSpecResidueField V.point =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberToSpecResidueField
                (specCompletedStalkPoint S s) ≫ Spec.map eBase.inv) ∧
          (eFiber.hom (((pullback.snd q (relativeBaseChangeMorphism s σ)).fiberHomeo
              (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩) =
            ((pullback.snd q τV).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  classical
  have := hσ
  have : IsLocalHom (CommRingCat.ofHom σ).hom := inferInstanceAs (IsLocalHom σ)
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have hGhat := completion_isGRing (S.presheaf.stalk s) hG
  have : IsNoetherianRing (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)) := hGhat.1
  have : IsLocallyNoetherian (specCompletedStalk S s) := inferInstance
  -- descend the pair to a smooth stage of the presentation of `Spec 𝒪^∧_{S, s}`
  obtain ⟨Dst, ρ, hρSm, τ, m, hmρ, hmτ, A, fD, gD, hfD₀, hgD, a, hτρ, hAa, hfa, hfres₀, hgres,
    hga, aσ, haσA, haσZ, Uaff, jUaff, hjUaff, eAff, heAffIso, a₀, hja₀, heAffa₀,
    hAffX, hAffY, hAffZ⟩ :=
    exists_stage_etale_pair_of_pointed_span p q bS hTB hG
      (relativeBaseChangeMorphism s σ) hβB xσ hxσX hxσZ yσ hyσZ Usch u fU
      hfU gU hgUEt hgU hgUres hUBase
  have := hρSm
  have : LocallyOfFiniteType ρ := inferInstance
  have hτm : τ (m (specCompletedStalkPoint S s)) = t := by
    change (m ≫ τ) (specCompletedStalkPoint S s) = t
    rw [hmτ]
    exact relativeBaseChangeMorphism_specCompletedStalkPoint s σ
  have hσstage : (Scheme.stalkClosedPointTo m).hom.comp (τ.stalkHomAt hτm) = σ :=
    stalkClosedPointTo_comp_stalkHomAt m τ (CommRingCat.ofHom σ) hmτ hτm
  -- the two routes out of `𝒪_{A, a}`, and the point of the base change of `A` along `m`
  have hgYa : (gD.left ≫ pullback.fst q τ) a = y := by
    change pullback.fst q τ (gD.left a) = y
    rw [hga]
    change (baseChangeCompare q τ m (relativeBaseChangeMorphism s σ) hmτ ≫
      pullback.fst q τ) yσ = y
    rw [baseChangeCompare_fst]
    exact hyσY
  have hAσX : (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ) aσ = x := by
    change (fD.left ≫ pullback.fst p ρ) (pullback.fst A.hom m aσ) = x
    rw [haσA]
    exact hfa
  have hAσY : (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ) aσ = y := by
    change (gD.left ≫ pullback.fst q τ) (pullback.fst A.hom m aσ) = y
    rw [haσA]
    exact hgYa
  -- the Noetherian local rings in play
  have : IsLocallyNoetherian (pullback q (relativeBaseChangeMorphism s σ)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd q (relativeBaseChangeMorphism s σ))
  have : IsLocallyNoetherian (pullback p (specCompletedStalkTo S s)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (specCompletedStalkTo S s))
  have := hgUEt
  have : IsLocallyNoetherian Usch := LocallyOfFiniteType.isLocallyNoetherian gU
  have : IsNoetherianRing
    ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) := inferInstance
  have : IsNoetherianRing
    ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) := inferInstance
  have : IsNoetherianRing (Usch.presheaf.stalk u) := inferInstance
  -- **Clause (5).** The congruence in `𝒪_{Usch, u}` is a congruence in
  -- `𝒪_{A ×_D Spec 𝒪^∧_{S, s}, aσ}`, `Usch` being that base change near its point.
  have hAcong : ∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
      (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ).stalkHomAt hAσX α -
          (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ).stalkHomAt hAσY b ∈
        maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N := by
    intro α b hP
    have hdiffU := hUcong α b hP
    -- transport along the identification of the local ring of `U` with that of the base
    -- change of `A` along `m`
    have := hjUaff
    have := heAffIso
    have : IsOpenImmersion eAff := inferInstance
    have : IsIso (eAff.stalkMap a₀) := inferInstance
    have : IsIso (((pullback A.hom m).presheaf.stalkCongr
      (.of_eq heAffa₀.symm)).hom) := inferInstance
    have hfbij : Function.Bijective (eAff.stalkHomAt heAffa₀) :=
      ConcreteCategory.bijective_of_isIso
        (((pullback A.hom m).presheaf.stalkCongr (.of_eq heAffa₀.symm)).hom ≫
          eAff.stalkMap a₀)
    have hX := RingHom.congr_fun
      (stalkHomAt_comp_eq_of_comp_eq hAffX hja₀ hUX heAffa₀ hAσX) α
    have hY := RingHom.congr_fun
      (stalkHomAt_comp_eq_of_comp_eq hAffY hja₀ hUY heAffa₀ hAσY) b
    simp only [RingHom.comp_apply] at hX hY
    have hfdiff : eAff.stalkHomAt heAffa₀
        ((pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ).stalkHomAt hAσX α -
          (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ).stalkHomAt hAσY b) ∈
          maximalIdeal (Uaff.presheaf.stalk a₀) ^ N := by
      rw [map_sub, ← hX, ← hY, ← map_sub]
      have hle : (maximalIdeal (Usch.presheaf.stalk u) ^ N).map
          (jUaff.stalkHomAt hja₀) ≤ maximalIdeal (Uaff.presheaf.stalk a₀) ^ N := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) N
      exact hle (Ideal.mem_map_of_mem _ hdiffU)
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (eAff.stalkHomAt heAffa₀)
      hfbij.surjective, ← Ideal.map_pow] at hfdiff
    obtain ⟨η, hη, hfη⟩ :=
      (Ideal.mem_map_iff_of_surjective _ hfbij.surjective).mp hfdiff
    exact hfbij.injective hfη ▸ hη
  obtain ⟨V, τV, hτV, yτ, hyτY, hyτV, Wsch, w, pW, hpW, g, hgPoint, hgEt, hVel, hτVB, hresg,
    hover, hXcond, hc3, hc5, hgZθ, hfib⟩ :=
    exists_approximationDiagram_of_stage p q hG N hN σ ρ τ bS hTB hτρ m
      hmρ (relativeBaseChangeMorphism s σ) hmτ hτm hσstage A fD gD hgD a hAa hfa
      hgres hgYa yσ hyσY hyσZ hga aσ haσA haσZ hAσX hAσY P hAcong
  exact ⟨V, τV, hτV, yτ, hyτY, hyτV, Wsch, w, pW, hpW, g, hgPoint, hgEt, hVel, hτVB, hresg,
    hover, fun hfe hfr => hXcond (hfD₀ hfe) (hfres₀ hfr), hc3, hc5, hfib⟩

/-- **Tag 0GDX over a base `B` carrying both `S` and `T`.** The whole of Tag 0GDX, with the
source's "`T` is of finite type over `Spec ℤ`" replaced by "`T` is locally of finite
presentation over `B`" for a scheme `B` which also receives `S`, and over which the morphism
`Spec 𝒪^∧_{S, s} ⟶ T` attached to `σ` is compatible with the completion map
`Spec 𝒪^∧_{S, s} ⟶ S`. That compatibility is what lets `σ` descend to a finite stage of the
presentation of `Spec 𝒪^∧_{S, s}`, and the conclusion carries in return the resulting
factorisation `τ ≫ hTB = V.toBase ≫ bS` of `τ` over `B`.

For `B` terminal this is Tag 0GDX, with the compatibility automatic; for `B = S` and
`bS = 𝟙 S` it is the setting of Tag 0CAW, where the compatibility says exactly that `σ` is an
`𝒪_{S, s}`-algebra map. -/
private theorem exists_common_elementaryEtaleNeighborhood_over_base
    {X S Y T B : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsLocallyNoetherian T]
    (bS : S ⟶ B) (hTB : T ⟶ B) [LocallyOfFinitePresentation hTB]
    {x : X} {s : S} {y : Y} {t : T} (hx : p x = s)
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (hβB : relativeBaseChangeMorphism s σ ≫ hTB = specCompletedStalkTo S s ≫ bS)
    (yσ : (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hyσY : pullback.fst q (relativeBaseChangeMorphism s σ) yσ = y)
    (hyσZ : pullback.snd q (relativeBaseChangeMorphism s σ) yσ =
      specCompletedStalkPoint S s)
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion
        (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (p.stalkHomAt hx)) =
      (algebraMap ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)
          (AdicCompletion
            (maximalIdeal
              ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))).comp
        (((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσZ).comp
          ((specCompletedStalkTo S s).stalkHomAt
            (specCompletedStalkTo_specCompletedStalkPoint S s)))) :
    ∃ (V : EtaleNeighborhood S s) (τ : V.scheme ⟶ T) (hτ : τ V.point = t)
      (yτ : (pullback q τ : Scheme.{u}))
      (hyτY : pullback.fst q τ yτ = y) (hyτV : pullback.snd q τ yτ = V.point)
      (W : EtaleNeighborhood X x) (g : W.scheme ⟶ pullback q τ)
      (hgPoint : g W.point = yτ) (_ : Etale g),
      V.IsElementary ∧ W.IsElementary ∧ τ ≫ hTB = V.toBase ≫ bS ∧
        IsIso (((pullback q τ).residueFieldCongr hgPoint).inv ≫
          g.residueFieldMap W.point) ∧
        g ≫ pullback.snd q τ ≫ V.toBase = W.toBase ≫ p ∧
        (∀ b : T.presheaf.stalk t,
          V.completionMap (σ b) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ b) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) ∧
        (∀ (α : X.presheaf.stalk x)
            (b : Y.presheaf.stalk y),
            AdicCompletion.evalₐ (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
                (φ (algebraMap (X.presheaf.stalk x)
                  (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
                    (X.presheaf.stalk x)) α)) =
              Ideal.Quotient.mk (maximalIdeal
                  ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
                ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b) →
            Ideal.Quotient.mk (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N)
                (W.stalkHom α) =
              Ideal.Quotient.mk (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N)
                (g.stalkHomAt hgPoint ((pullback.fst q τ).stalkHomAt hyτY b))) ∧
        ∃ (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
            V.scheme.residueField V.point)
          (eFiber : (pullback.snd q (relativeBaseChangeMorphism s σ)).fiber
              (specCompletedStalkPoint S s) ≅
            (pullback.snd q τ).fiber V.point),
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              specCompletedStalkTo S s) ∧
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τ =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              relativeBaseChangeMorphism s σ) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberι V.point ≫ pullback.fst q τ =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberι
                (specCompletedStalkPoint S s) ≫
              pullback.fst q (relativeBaseChangeMorphism s σ)) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberToSpecResidueField V.point =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberToSpecResidueField
                (specCompletedStalkPoint S s) ≫ Spec.map eBase.inv) ∧
          (eFiber.hom (((pullback.snd q (relativeBaseChangeMorphism s σ)).fiberHomeo
              (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩) =
            ((pullback.snd q τ).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  classical
  have := hσ
  have : IsLocalHom (CommRingCat.ofHom σ).hom := inferInstanceAs (IsLocalHom σ)
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have hGhat := completion_isGRing (S.presheaf.stalk s) hG
  have : IsNoetherianRing (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)) := hGhat.1
  have : IsLocallyNoetherian (specCompletedStalk S s) := inferInstance
  -- transport `φ` to the base change of `X` along `Spec 𝒪^∧_{S, s} ⟶ S`
  obtain ⟨xσ, hxσX, hxσZ, hxσres, Φ, hΦ, hΦφ⟩ :=
    exists_point_and_ringEquiv_pullback_completedStalk p hx hG
      (pullback.snd q (relativeBaseChangeMorphism s σ)) yσ hyσZ φ hφ
  -- Tag 0CAV over `Spec 𝒪^∧_{S, s}`
  have hGz : IsGRing ((specCompletedStalk S s).presheaf.stalk
      (specCompletedStalkPoint S s)) :=
    isGRing_of_ringEquiv (stalkClosedPointIso (CommRingCat.of
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)))).symm.commRingCatIsoToRingEquiv hGhat
  obtain ⟨U, qU, hqUEt, hqU, hUel, hqUalong, hqUBase, hUcong⟩ :=
    exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv_at
      (pullback.snd p (specCompletedStalkTo S s))
      (pullback.snd q (relativeBaseChangeMorphism s σ)) xσ yσ hxσZ hyσZ hGz N hN Φ hΦ
  have hUres : IsIso (U.toBase.residueFieldMap U.point) :=
    (EtaleNeighborhood.isElementary_iff U).mp hUel
  have hqUres : IsIso (qU.residueFieldMap U.point) :=
    (EtaleNeighborhood.isElementary_iff (U.along qU hqUEt hqU)).mp hqUalong
  have hfUres : IsIso ((U.toBase ≫ pullback.fst p (specCompletedStalkTo S s)).residueFieldMap
      U.point) := by
    have hr1 : IsIso ((pullback.fst p (specCompletedStalkTo S s)).residueFieldMap
        (U.toBase U.point)) := by rwa [U.map_point]
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hr1 hUres
  have hUX : (U.toBase ≫ pullback.fst p (specCompletedStalkTo S s)) U.point = x := by
    change pullback.fst p (specCompletedStalkTo S s) (U.toBase U.point) = x
    rw [U.map_point]
    exact hxσX
  have hUY : (qU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)) U.point = y := by
    change pullback.fst q (relativeBaseChangeMorphism s σ) (qU U.point) = y
    rw [hqU]
    exact hyσY
  -- the Noetherian local rings in play
  have : IsLocallyNoetherian (pullback q (relativeBaseChangeMorphism s σ)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd q (relativeBaseChangeMorphism s σ))
  have : IsLocallyNoetherian (pullback p (specCompletedStalkTo S s)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (specCompletedStalkTo S s))
  have : IsLocallyNoetherian U.scheme := LocallyOfFiniteType.isLocallyNoetherian U.toBase
  have : IsNoetherianRing
    ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) := inferInstance
  have : IsNoetherianRing
    ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) := inferInstance
  have : IsNoetherianRing (U.scheme.presheaf.stalk U.point) := inferInstance
  have : IsLocalHom (Φ : AdicCompletion (maximalIdeal
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) →+*
      AdicCompletion (maximalIdeal
        ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
        ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)) :=
    ⟨(isLocalHom_equiv Φ).map_nonunit⟩
  -- the congruence of Tag 0CAV in `𝒪_{U, u}`, which is what the construction consumes
  have hdiffU : ∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y),
      AdicCompletion.evalₐ (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
          (φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) α)) =
        Ideal.Quotient.mk (maximalIdeal
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
          ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b) →
      (U.toBase ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α -
          (qU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hUY b ∈
        maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N := by
    intro α b hP
    set ω := algebraMap
      ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)
      (AdicCompletion (maximalIdeal
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
      ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b) with hωdef
    -- `φ` agrees with `ω` modulo `𝔪 ^ N`, hence so do their images under `Φ`
    have hPω : AdicCompletion.evalₐ (maximalIdeal
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
        (φ (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) α) -
          ω) = 0 := by
      rw [map_sub, hP, hωdef, evalₐ_algebraMap, sub_self]
    have hΦeq : AdicCompletion.evalₐ (maximalIdeal
          ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)) N
          (Φ (φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) α))) =
        AdicCompletion.evalₐ (maximalIdeal
          ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)) N (Φ ω) := by
      have h0 := evalₐ_map_eq_zero_of_isLocalHom N
        (Φ : AdicCompletion (maximalIdeal
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) →+*
          AdicCompletion (maximalIdeal
            ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ))
            ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ)) hPω
      rw [map_sub, map_sub, sub_eq_zero] at h0
      exact h0
    -- the congruence in the local ring of `U`
    have hXside : Ideal.Quotient.mk (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N)
          ((U.toBase ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α) =
        AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
          (U.completionMap (Φ (φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x)) α)))) := by
      rw [hΦφ α, EtaleNeighborhood.completionMap, completionMapAt_algebraMap,
        evalₐ_algebraMap]
      exact congrArg _ (RingHom.congr_fun
        (Scheme.Hom.stalkHomAt_comp U.toBase
          (pullback.fst p (specCompletedStalkTo S s)) U.map_point hxσX) α)
    have hYside : Ideal.Quotient.mk (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N)
          ((qU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hUY b) =
        AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
          ((U.along qU hqUEt hqU).completionMap ω) := by
      have h1 : (U.along qU hqUEt hqU).completionMap ω =
          algebraMap (U.scheme.presheaf.stalk U.point)
            (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
              (U.scheme.presheaf.stalk U.point))
            (qU.stalkHomAt hqU
              ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b)) :=
        completionMapAt_algebraMap qU hqU _
      rw [h1, evalₐ_algebraMap]
      exact congrArg _ (RingHom.congr_fun
        (Scheme.Hom.stalkHomAt_comp qU
          (pullback.fst q (relativeBaseChangeMorphism s σ)) hqU hyσY) b)
    have hmid : AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
          (U.completionMap (Φ ω)) =
        AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
          ((U.along qU hqUEt hqU).completionMap ω) := by
      have h0 := (evalₐ_eq_zero_iff_mem_map_pow
        (maximalIdeal (U.scheme.presheaf.stalk U.point)).fg_of_isNoetherianRing N _).mpr
        (hUcong ω)
      have h1 : AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
            (U.completionMap (Φ ω)) -
          AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
            ((U.along qU hqUEt hqU).completionMap ω) = 0 := by
        have h2 := map_sub
          (AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N)
          (U.completionMap (Φ ω)) ((U.along qU hqUEt hqU).completionMap ω)
        rw [← h2]
        exact h0
      exact sub_eq_zero.mp h1
    have hstep : AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
          (U.completionMap (Φ (φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x)) α)))) =
        AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
          (U.completionMap (Φ ω)) := by
      rw [EtaleNeighborhood.completionMap, evalₐ_completionMapAt, evalₐ_completionMapAt,
        hΦeq]
    have hdiffU : (U.toBase ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α -
        (qU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hUY b ∈
          maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
        (hXside.trans ((hstep.trans hmid).trans hYside.symm))
    exact hdiffU
  obtain ⟨V, τV, hτV, yτ, hyτY, hyτV, Wsch, w, pW, hpW, g, hgPoint, hgEt, hVel, hτVB, hresg,
    hover, hXcond, hc3, hc5, hfib⟩ :=
    exists_approximationDiagram_over_base_of_span p q bS hTB hG N hN σ hσ hβB xσ hxσX
      hxσZ yσ hyσY hyσZ U.scheme U.point U.toBase U.map_point qU hqUEt hqU hqUres hqUBase
      (fun α b => AdicCompletion.evalₐ (maximalIdeal
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
        (φ (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) α)) =
      Ideal.Quotient.mk (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
        ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b)) hUX hUY hdiffU
  obtain ⟨hpWet, hpWres⟩ := hXcond inferInstance hfUres
  have := hpWet
  refine ⟨V, τV, hτV, yτ, hyτY, hyτV,
    { scheme := Wsch, point := w, toBase := pW, map_point := hpW }, g, hgPoint, hgEt, hVel,
    ?_, hτVB, hresg, hover, hc3, hc5, hfib⟩
  rw [EtaleNeighborhood.isElementary_iff]
  exact hpWres

/-- **Stacks Project, Tag 0GDX.** Let `S` be a locally Noetherian scheme, let `s ∈ S` have a
G-ring local ring, let `T` be locally of finite type over `Spec ℤ`, let `p : X ⟶ S` and
`q : Y ⟶ T` be locally of finite type, let `x ∈ X` lie over `s` and `y ∈ Y` over `t ∈ T`, and
let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local homomorphism. Write
`Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` and let `y_σ ∈ Y_σ` lie over `y` and over the closed point.
An isomorphism `φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y_σ, y_σ}` of `𝒪_{S, s}`-algebras is then induced, after
elementary étale changes, by a morphism of schemes: there are an elementary étale neighbourhood
`(V, v)` of `(S, s)`, a morphism `τ : V ⟶ T` with `τ v = t`, and an elementary étale
neighbourhood `(W, w)` of `(X, x)` which is simultaneously an elementary étale neighbourhood of
`(Y ×_{T, τ} V, y_τ)`, where `y_τ` corresponds to `y_σ` under the identification of the closed
fibres `(Y_σ)_s = (Y ×_T V)_v`.

The identification of the closed fibres is given explicitly: an isomorphism `e` of the residue
fields of the two bases compatible with their maps to `S` and to `T`, and an isomorphism of the
scheme-theoretic fibres compatible with the two maps to `Y` and with `e`, carrying the point
above `y_σ` to the point above `y_τ`. -/
@[stacks 0GDX "What is proved is STRONGER than the source in two respects, both inherited from \
the first stage of Tag 0CAW which replaces the étale slice of Tag 057G here: the pair `(V, τ)` \
satisfies in addition the congruence that Tag 0CAW records as its clause (3), namely that the \
square relating `σ` to `τ^♯_v` commutes modulo `𝔪_v ^ N` for the given `N ≥ 1`; and the \
source's `T` of finite type over `Spec ℤ` is weakened to LOCALLY of finite type"]
theorem exists_common_elementaryEtaleNeighborhood_absoluteApproximation
    {X S Y T : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    {x : X} {s : S} {y : Y} {t : T} (hx : p x = s)
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (yσ : (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hyσY : pullback.fst q (relativeBaseChangeMorphism s σ) yσ = y)
    (hyσZ : pullback.snd q (relativeBaseChangeMorphism s σ) yσ =
      specCompletedStalkPoint S s)
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion
        (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (p.stalkHomAt hx)) =
      (algebraMap ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)
          (AdicCompletion
            (maximalIdeal
              ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))).comp
        (((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσZ).comp
          ((specCompletedStalkTo S s).stalkHomAt
            (specCompletedStalkTo_specCompletedStalkPoint S s)))) :
    ∃ (V : EtaleNeighborhood S s) (τ : V.scheme ⟶ T) (hτ : τ V.point = t)
      (yτ : (pullback q τ : Scheme.{u}))
      (_ : pullback.fst q τ yτ = y) (hyτV : pullback.snd q τ yτ = V.point)
      (W : EtaleNeighborhood X x) (g : W.scheme ⟶ pullback q τ)
      (hgPoint : g W.point = yτ) (_ : Etale g),
      V.IsElementary ∧ W.IsElementary ∧
        IsIso (((pullback q τ).residueFieldCongr hgPoint).inv ≫
          g.residueFieldMap W.point) ∧
        g ≫ pullback.snd q τ ≫ V.toBase = W.toBase ≫ p ∧
        (∀ b : T.presheaf.stalk t,
          V.completionMap (σ b) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ b) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) ∧
        ∃ (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
            V.scheme.residueField V.point)
          (eFiber : (pullback.snd q (relativeBaseChangeMorphism s σ)).fiber
              (specCompletedStalkPoint S s) ≅
            (pullback.snd q τ).fiber V.point),
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              specCompletedStalkTo S s) ∧
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τ =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              relativeBaseChangeMorphism s σ) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberι V.point ≫ pullback.fst q τ =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberι
                (specCompletedStalkPoint S s) ≫
              pullback.fst q (relativeBaseChangeMorphism s σ)) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberToSpecResidueField V.point =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberToSpecResidueField
                (specCompletedStalkPoint S s) ≫ Spec.map eBase.inv) ∧
          (eFiber.hom (((pullback.snd q (relativeBaseChangeMorphism s σ)).fiberHomeo
              (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩) =
            ((pullback.snd q τ).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  have := hT
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := isLocallyNoetherian_terminal
  have hterm : terminal.from T = specULiftZIsTerminal.{u}.from T ≫
      (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).hom :=
    terminalIsTerminal.hom_ext _ _
  have : LocallyOfFiniteType (terminal.from T) := by rw [hterm]; infer_instance
  have : LocallyOfFinitePresentation (terminal.from T) := inferInstance
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (terminal.from T)
  obtain ⟨V, τ, hτ, yτ, hyτY, hyτV, W, g, hgPoint, hgEt, hVel, hWel, -, hres, hover, hcong, -,
    hfib⟩ :=
    exists_common_elementaryEtaleNeighborhood_over_base p q (terminal.from S)
      (terminal.from T) hx hG N hN σ hσ (terminalIsTerminal.hom_ext _ _) yσ hyσY hyσZ φ hφ
  exact ⟨V, τ, hτ, yτ, hyτY, hyτV, W, g, hgPoint, hgEt, hVel, hWel, hres, hover, hcong, hfib⟩

/-! ### Tag 0CB1: the approximating diagram with an étale leg -/

/-- **The diagram of Tag 0CB1 from an isomorphism of completions.** With the notation and
assumptions of Tag 0CAW — a locally Noetherian `S`, morphisms `p : X ⟶ S`, `q : Y ⟶ T` and
`h : T ⟶ S` locally of finite type, points `x ↦ s` and `y ↦ t ↦ s`, a G-ring `𝒪_{S, s}`, a
local `𝒪_{S, s}`-algebra map `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`, the base change
`Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` and a point `y_σ` of it over `y` and over the closed point —
assume moreover that `φ` induces an isomorphism `𝒪^∧_{X, x} ≅ 𝒪^∧_{Y_σ, y_σ}` of
`𝒪_{S, s}`-algebras on completions. Then for every `N ≥ 1` the diagram of Tag 0CAW can be
chosen with `f` étale: there are an elementary étale neighbourhood `(V, v)` of `(S, s)`, a
morphism `τ : V ⟶ T` over `S` with `τ v = t` whose square with `σ` commutes modulo `𝔪_v ^ N`, a
point `y_τ` of `Y ×_{T, τ} V` over `y` and `v` which corresponds to `y_σ` on the closed fibres,
an elementary étale neighbourhood `(W, w)` of `(Y ×_{T, τ} V, y_τ)`, a morphism `F : W ⟶ X`
over `S` carrying `w` to `x`, and an **étale** `f : W ⟶ X ×_S V` with `f ≫ pr₁ = F` and
`f ≫ pr₂ = W ⟶ Y ×_{T, τ} V ⟶ V`, so that `f w = (x, v)`.

Clause (5) of Tag 0CAW is the ring isomorphism
`θ : 𝒪_{Y_σ, y_σ}/𝔪_{y_σ} ^ N ≅ 𝒪_{Y ×_{T, τ} V, (y, v)}/𝔪_{(y, v)} ^ N`
which the conclusion exhibits, compatible with the two maps from `𝒪_{Y, y}` and with the two
maps from `𝒪_{S, s}` — the compatibilities which make `θ` the source's canonical identification
of the two base changes over `𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N` — together with the
commutativity of the source's square: `φ` read on `𝒪_{X, x}` through `θ` and then through the
elementary étale neighbourhood `W ⟶ Y ×_{T, τ} V` is `F^♯_w` modulo `𝔪_w ^ N`. No isomorphism
of the completions `𝒪^∧_{Y_σ, y_σ}` and `𝒪^∧_{Y ×_{T, τ} V, y_τ}` is asserted: only the
`𝔪 ^ N`-truncations are identified, and for a pair `(V, τ)` satisfying clauses (2) and (3)
alone the completions can be a cusp and a node.

The correspondence of `y_τ` with `y_σ` is recorded in addition, as in Tag 0GDX: an isomorphism
`eBase` of the residue fields of the two bases compatible with their maps to `S` and to `T`, and
an isomorphism `eFiber` of the scheme-theoretic closed fibres compatible with the two maps to
`Y` and with `eBase`, carrying the point above `y_σ` to the point above `y_τ`.

Here the isomorphism of completions is the input; Tag 0CB1 as stated, for a local
`𝒪_{S, s}`-algebra map `φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}` inducing an isomorphism on
completions, is `StacksDraft.ArtinApproximation.exists_etale_relativeMapApproximation`, which
is derived from this. -/
theorem exists_etale_relativeIsomorphismApproximation
    {X S Y T : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T) (h : T ⟶ S)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [LocallyOfFiniteType h]
    {x : X} {s : S} {y : Y} {t : T} (hx : p x = s) (hts : h t = s)
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (hσbase : σ.comp (h.stalkHomAt hts) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    (yσ : (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hyσY : pullback.fst q (relativeBaseChangeMorphism s σ) yσ = y)
    (hyσZ : pullback.snd q (relativeBaseChangeMorphism s σ) yσ =
      specCompletedStalkPoint S s)
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion
        (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (p.stalkHomAt hx)) =
      (algebraMap ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)
          (AdicCompletion
            (maximalIdeal
              ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))).comp
        (((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσZ).comp
          ((specCompletedStalkTo S s).stalkHomAt
            (specCompletedStalkTo_specCompletedStalkPoint S s)))) :
    ∃ (V : EtaleNeighborhood S s) (τ : V.scheme ⟶ T) (hτ : τ V.point = t)
      (yτ : (pullback q τ : Scheme.{u}))
      (hyτY : pullback.fst q τ yτ = y) (hyτV : pullback.snd q τ yτ = V.point)
      (W : EtaleNeighborhood (pullback q τ) yτ) (F : W.scheme ⟶ X) (hF : F W.point = x)
      (f : W.scheme ⟶ pullback p V.toBase),
      V.IsElementary ∧ W.IsElementary ∧ τ ≫ h = V.toBase ∧ Etale f ∧
        f ≫ pullback.fst p V.toBase = F ∧
        f ≫ pullback.snd p V.toBase = W.toBase ≫ pullback.snd q τ ∧
        F ≫ p = W.toBase ≫ pullback.snd q τ ≫ V.toBase ∧
        (∀ b : T.presheaf.stalk t,
          V.completionMap (σ b) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ b) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) ∧
        (∃ θ : ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ⧸
              (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N) ≃+*
            ((pullback q τ).presheaf.stalk yτ) ⧸
              (maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N),
          (∀ b : Y.presheaf.stalk y,
            θ (Ideal.Quotient.mk (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
                ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b)) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N)
                ((pullback.fst q τ).stalkHomAt hyτY b)) ∧
          (∀ c : S.presheaf.stalk s,
            θ (Ideal.Quotient.mk (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
                ((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσZ
                  ((specCompletedStalkTo S s).stalkHomAt
                    (specCompletedStalkTo_specCompletedStalkPoint S s) c))) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N)
                ((pullback.snd q τ).stalkHomAt hyτV (V.stalkHom c))) ∧
          ∀ (α : X.presheaf.stalk x) (z : (pullback q τ).presheaf.stalk yτ),
            θ (AdicCompletion.evalₐ (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
                (φ (algebraMap (X.presheaf.stalk x)
                  (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
                    (X.presheaf.stalk x)) α))) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N) z →
            Ideal.Quotient.mk (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N)
                (W.stalkHom z) =
              Ideal.Quotient.mk (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N)
                (F.stalkHomAt hF α)) ∧
        ∃ (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
            V.scheme.residueField V.point)
          (eFiber : (pullback.snd q (relativeBaseChangeMorphism s σ)).fiber
              (specCompletedStalkPoint S s) ≅
            (pullback.snd q τ).fiber V.point),
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              specCompletedStalkTo S s) ∧
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τ =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              relativeBaseChangeMorphism s σ) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberι V.point ≫ pullback.fst q τ =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberι
                (specCompletedStalkPoint S s) ≫
              pullback.fst q (relativeBaseChangeMorphism s σ)) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberToSpecResidueField V.point =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberToSpecResidueField
                (specCompletedStalkPoint S s) ≫ Spec.map eBase.inv) ∧
          (eFiber.hom (((pullback.snd q (relativeBaseChangeMorphism s σ)).fiberHomeo
              (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩) =
            ((pullback.snd q τ).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  have := hσ
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
  have : LocallyOfFinitePresentation h := inferInstance
  obtain ⟨V, τ, hτ, yτ, hyτY, hyτV, W₀, g, hgPoint, hgEt, hVel, hW₀el, hτh, hres, hover,
    hcong, hcl5, hfib⟩ :=
    exists_common_elementaryEtaleNeighborhood_over_base p q (𝟙 S) h hx hG N hN σ hσ
      (by rw [Category.comp_id]; exact relativeBaseChangeMorphism_comp h hts σ hσbase)
      yσ hyσY hyσZ φ hφ
  have := hgEt
  have hcomm : W₀.toBase ≫ p = (g ≫ pullback.snd q τ) ≫ V.toBase := by
    rw [Category.assoc]
    exact hover.symm
  -- **Clause (5) of Tag 0CAW.** The three `𝔪 ^ N`-truncations of the completions in play are
  -- identified: through `φ`, through the elementary étale neighbourhood `W ⟶ X`, and through
  -- the elementary étale neighbourhood `W ⟶ Y ×_{T, τ} V`.
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian V.scheme := LocallyOfFiniteType.isLocallyNoetherian V.toBase
  have : IsLocallyNoetherian (pullback q τ) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q τ)
  have : IsLocallyNoetherian (pullback q (relativeBaseChangeMorphism s σ)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd q (relativeBaseChangeMorphism s σ))
  have : IsLocallyNoetherian W₀.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian W₀.toBase
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have : IsNoetherianRing
    ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) := inferInstance
  obtain ⟨εφ, hεφ⟩ := exists_ringEquiv_quotient_pow_of_adicCompletion_ringEquiv N φ
  obtain ⟨εF, -, hεFmk⟩ := exists_ringEquiv_quotient_pow_of_etale W₀.toBase W₀.map_point
    ((EtaleNeighborhood.isElementary_iff W₀).mp hW₀el) N
  have := hres
  have : IsIso (g.residueFieldMap W₀.point) :=
    IsIso.of_isIso_comp_left ((pullback q τ).residueFieldCongr hgPoint).inv _
  obtain ⟨εg, -, hεgmk⟩ := exists_ringEquiv_quotient_pow_of_etale g hgPoint inferInstance N
  -- the three identifications, read on the images of the uncompleted local rings
  have hεφmk : ∀ α : X.presheaf.stalk x,
      εφ (Ideal.Quotient.mk (maximalIdeal (X.presheaf.stalk x) ^ N) α) =
        AdicCompletion.evalₐ (maximalIdeal
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
          (φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) α)) :=
    fun α => (congrArg εφ (evalₐ_algebraMap (maximalIdeal (X.presheaf.stalk x)) N α)).symm.trans
      (hεφ _)
  -- the map from `𝒪_{S, s}` to `𝒪_{W, w}` through `X` and through `Y ×_{T, τ} V` agree
  have hbaseW : ∀ c : S.presheaf.stalk s,
      W₀.stalkHom (p.stalkHomAt hx c) =
        g.stalkHomAt hgPoint ((pullback.snd q τ).stalkHomAt hyτV (V.stalkHom c)) := by
    intro c
    have hVpt : (pullback.snd q τ ≫ V.toBase) yτ = s := by
      change V.toBase (pullback.snd q τ yτ) = s
      rw [hyτV]
      exact V.map_point
    have h := RingHom.congr_fun
      (stalkHomAt_comp_eq_of_comp_eq hover.symm W₀.map_point hx hgPoint hVpt) c
    rw [Scheme.Hom.stalkHomAt_comp (pullback.snd q τ) V.toBase hyτV V.map_point] at h
    exact h
  refine ⟨V, τ, hτ, yτ, hyτY, hyτV, W₀.along g hgEt hgPoint, W₀.toBase, W₀.map_point,
    pullback.lift W₀.toBase (g ≫ pullback.snd q τ) hcomm, hVel, hres,
    hτh.trans (Category.comp_id _),
    @etale_of_etale_over _ _ X _ W₀.toBase (pullback.fst p V.toBase)
      (pullback.lift_fst _ _ hcomm) W₀.etale_toBase inferInstance,
    pullback.lift_fst _ _ hcomm, pullback.lift_snd _ _ hcomm, hover.symm, hcong,
    ⟨εφ.symm.trans (εF.trans εg.symm), ?_, ?_, ?_⟩, hfib⟩
  · -- `θ` is compatible with the two maps from `𝒪_{Y, y}`
    intro b
    obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (εφ.symm
      (Ideal.Quotient.mk (maximalIdeal
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
        ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b)))
    have hP : AdicCompletion.evalₐ (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
          (φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) α)) =
        Ideal.Quotient.mk (maximalIdeal
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
          ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b) := by
      rw [← hεφmk α, hα]
      exact εφ.apply_symm_apply _
    change εg.symm (εF (εφ.symm (Ideal.Quotient.mk _ _))) = _
    rw [← hα, hεFmk, hcl5 α b hP, ← hεgmk]
    exact εg.symm_apply_apply _
  · -- `θ` is compatible with the two maps from `𝒪_{S, s}`
    intro c
    have hPc : εφ (Ideal.Quotient.mk (maximalIdeal (X.presheaf.stalk x) ^ N)
          (p.stalkHomAt hx c)) =
        Ideal.Quotient.mk (maximalIdeal
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
          ((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσZ
            ((specCompletedStalkTo S s).stalkHomAt
              (specCompletedStalkTo_specCompletedStalkPoint S s) c)) := by
      rw [hεφmk, show φ (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
          (p.stalkHomAt hx c)) = algebraMap _ _
            ((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσZ
              ((specCompletedStalkTo S s).stalkHomAt
                (specCompletedStalkTo_specCompletedStalkPoint S s) c)) from
          RingHom.congr_fun hφ c, evalₐ_algebraMap]
    change εg.symm (εF (εφ.symm (Ideal.Quotient.mk _ _))) = _
    rw [← hPc, εφ.symm_apply_apply, hεFmk, hbaseW c, ← hεgmk]
    exact εg.symm_apply_apply _
  · -- clause (5): the square of Tag 0CAW commutes
    intro α z hz
    have h1 : εg.symm (εF (εφ.symm (AdicCompletion.evalₐ (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
          (φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x)) α))))) =
        εg.symm (Ideal.Quotient.mk (maximalIdeal
          (W₀.scheme.presheaf.stalk W₀.point) ^ N) (W₀.stalkHom α)) := by
      rw [← hεφmk α, εφ.symm_apply_apply, hεFmk]
    rw [show εφ.symm.trans (εF.trans εg.symm) (AdicCompletion.evalₐ (maximalIdeal
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
        (φ (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) α))) =
      εg.symm (Ideal.Quotient.mk (maximalIdeal
        (W₀.scheme.presheaf.stalk W₀.point) ^ N) (W₀.stalkHom α)) from h1] at hz
    have h2 := congrArg εg hz
    rw [εg.apply_symm_apply, hεgmk] at h2
    exact h2.symm

end StacksDraft.ArtinApproximation

end
