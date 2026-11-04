module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01LocalBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFieldFibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineNoetherianEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreProperties

/-!
# The locus `k = H⁰(X_k, 𝒪_{X_k})` of a family of curves is open

For a family of curves `X ⟶ S` (Stacks 0D4Z) this file proves local degree-zero cohomology and
base change, `AlgebraicGeometry.CurveFamily.HasLocalH0BaseChange`: if `k = H⁰(X_k, 𝒪_{X_k})` at a
field-valued point `Spec k ⟶ S`, there is an open neighbourhood `Ω` of its point such that
`Γ(T, 𝒪_T) = Γ(X_T, 𝒪_{X_T})` for every `T ⟶ S` with image in `Ω`. Consequently the fibrewise
condition `k = H⁰` and the condition `Curves^{h0,1}` of Stacks 0E6I satisfy condition (o) of
Stacks 0E0E.

The proof works over an affine open `Spec A ⊆ S` around the point. The restriction `X_A` of the
family is a proper flat finitely presented algebraic space over `Spec A`, and the fibre of `X` over
a field-valued point factoring through `Spec A` is the base change of `X_A`. The open locus of
`A = H⁰` near the point,
`AlgebraicGeometry.Space.exists_away_bijective_algebraMap_globalFunctions_relocalizeRestrict`,
gives a principal open `D(h) ∋` the point, over whose field-valued points `k = H⁰` holds; `Ω` is
its image in `S`. For `T ⟶ S` with image in `Ω`, the base change `X_T` then has `k = H⁰` on all
its fibres over fields, so `f_*𝒪 = 𝒪` for it (Stacks 0E6B (a),
`AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres`).

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isOpen_forall_isH0BijectiveAt`: the set of points where
  `k = H⁰` holds contains an open neighbourhood of each of its points.
* `AlgebraicGeometry.CurveFamily.hasLocalH0BaseChange`: local degree-zero cohomology and base
  change for every family of curves.
* `AlgebraicGeometry.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres`: condition (o)
  for the fibrewise condition `k = H⁰(X_k, 𝒪_{X_k})`.
* `AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily`: condition (o) for `Curves^{h0,1}`.

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

/-- A field-valued point of `Spec R` lies in the principal open `D(h)` exactly when `h` does not
vanish in the field. -/
theorem Spec.map_closedPoint_mem_basicOpen_iff {R : CommRingCat.{u}} {k : Type u} [Field k]
    (φ : R ⟶ CommRingCat.of k) (h : R) :
    (show PrimeSpectrum R from Spec.map φ (IsLocalRing.closedPoint k)) ∈
      PrimeSpectrum.basicOpen h ↔ φ h ≠ 0 := by
  change h ∉ Ideal.comap φ.hom (IsLocalRing.maximalIdeal k) ↔ _
  rw [Ideal.mem_comap, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} (X : CurveFamily B hZ)
  (W : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).affineOpens)

/-- The structure morphism `Spec Γ(S, W) ⟶ S ⟶ Spec ℤ` of an affine open `W` of the base, as a
morphism of the site. -/
abbrev affineOpenToBase :
    B.obj (Space.contains_spec_affineOpen B integerBase hZ X.base W) ⟶ B.obj hZ :=
  ObjectProperty.homMk (W.2.fromSpec ≫ B.inclusion.map X.base.hom)

/-- The restriction `X_W` of a family of curves to an affine open `W = Spec A` of its base, an
algebraic space over `Spec A`. -/
abbrev restrictAffineOpen :
    (BigFppfOver B (Spec Γ((BigFppfOver.toScheme B integerBase hZ).obj X.base, W.1))
      (Space.contains_spec_affineOpen B integerBase hZ X.base W))ᵒᵖ ⥤ Type u :=
  Space.restrictedFibre B integerBase hZ X.toBase.hom
    (Space.contains_spec_affineOpen B integerBase hZ X.base W) (affineOpenToBase X W)
    (Space.affineOpenSpecSiteHom B integerBase hZ X.base W)

/-- The restriction `X_W` of a family of curves to an affine open `W` of its base is an algebraic
space over `Spec Γ(S, W)`. -/
theorem isAlgebraicSpace_restrictAffineOpen :
    IsAlgebraicSpace B _ (Space.contains_spec_affineOpen B integerBase hZ X.base W)
      (restrictAffineOpen X W) :=
  Space.isAlgebraicSpace_restrictedFibre B integerBase hZ X.toBase.hom X.total.2
    (schemeSpace X.base).2 _ _ _

/-- **The fibre over a field-valued point factoring through an affine open is a fibre of the
restriction.** -/
theorem isH0BijectiveAt_mk_iff {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (t : B.obj hk ⟶ B.obj hZ)
    (m : B.obj hk ⟶ B.obj (Space.contains_spec_affineOpen B integerBase hZ X.base W))
    (ht : m ≫ affineOpenToBase X W = t)
    (val : (Over.mk t : BigFppfOver B integerBase hZ) ⟶ X.base)
    (hval : val = Over.homMk m ht ≫ Space.affineOpenSpecSiteHom B integerBase hZ X.base W) :
    X.IsH0BijectiveAt { carrier := k, contained := hk, toBase := t.hom, value := val } ↔
      Function.Bijective (algebraMap k (Space.globalFunctions B (Spec (.of k)) hk
        ((OverShriek.relocalizeRestrict m).obj (restrictAffineOpen X W)))) := by
  subst hval ht
  have hF := Space.isAlgebraicSpace_restrictedFibre B integerBase hZ X.toBase.hom X.total.2
    (schemeSpace X.base).2 hk (m ≫ affineOpenToBase X W)
    ((yoneda.obj X.base).map (Over.homMk m rfl).op
      (Space.affineOpenSpecSiteHom B integerBase hZ X.base W))
  have hG := isAlgebraicSpace_relocalizeRestrict B (Spec (.of k)) _ hk
    (Space.contains_spec_affineOpen B integerBase hZ X.base W) m _
    (isAlgebraicSpace_restrictAffineOpen X W)
  obtain ⟨e⟩ := Space.nonempty_restrictedFibre_iso_relocalizeRestrict B integerBase hZ
    X.toBase.hom (Space.contains_spec_affineOpen B integerBase hZ X.base W) hk
    (affineOpenToBase X W) m (Space.affineOpenSpecSiteHom B integerBase hZ X.base W)
  refine Iff.trans ?_ (Space.bijective_algebraMap_globalFunctions_congr B hF hG e)
  exact (Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff B integerBase hZ
    X.toBase.hom _ X.total.2 (schemeSpace X.base).2).symm

/-- **A field-valued point whose point lies in an affine open factors through it**, and its fibre
is then a fibre of the restriction of the family to the affine open. -/
theorem exists_factor_isH0BijectiveAt_iff
    (q : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hq : Space.schemePoint B integerBase hZ X.base q ∈ (W.1 : Set _)) :
    ∃ m : B.obj q.contained ⟶ B.obj (Space.contains_spec_affineOpen B integerBase hZ X.base W),
      m.hom ≫ W.2.fromSpec = (BigFppfOver.toScheme B integerBase hZ).map q.value ∧
      (X.IsH0BijectiveAt q ↔ Function.Bijective (algebraMap q.carrier
        (Space.globalFunctions B (Spec (.of q.carrier)) q.contained
          ((OverShriek.relocalizeRestrict m).obj (restrictAffineOpen X W))))) := by
  rcases q with ⟨k, hk, t, val⟩
  have := W.2.isOpenImmersion_fromSpec
  let σ : Spec (.of k) ⟶ (BigFppfOver.toScheme B integerBase hZ).obj X.base :=
    (BigFppfOver.toScheme B integerBase hZ).map val
  have hσ : Set.range σ ⊆ Set.range W.2.fromSpec := by
    rintro _ ⟨y, rfl⟩
    have : Subsingleton (Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact W.2.range_fromSpec.symm.subset hq
  let m' := IsOpenImmersion.lift W.2.fromSpec σ hσ
  have hm' : m' ≫ W.2.fromSpec = σ := IsOpenImmersion.lift_fac W.2.fromSpec σ hσ
  let m : B.obj hk ⟶ B.obj (Space.contains_spec_affineOpen B integerBase hZ X.base W) :=
    ObjectProperty.homMk m'
  have ht : m ≫ affineOpenToBase X W = ⟨t⟩ := by
    refine ObjectProperty.hom_ext _ ?_
    change m' ≫ W.2.fromSpec ≫ B.inclusion.map X.base.hom = t
    rw [← Category.assoc, hm']
    exact (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w val))
  have hval : val = Over.homMk m ht ≫ Space.affineOpenSpecSiteHom B integerBase hZ X.base W :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hm'.symm)
  exact ⟨m, hm', isH0BijectiveAt_mk_iff X W hk ⟨t⟩ m ht val hval⟩

variable {X} in
/-- **The locus `k = H⁰` is a neighbourhood of each of its points.** If `k = H⁰(X_k, 𝒪_{X_k})` at
a field-valued point `p` of the base, there is an open set `Ω` of points of the base containing
the point of `p` such that `k' = H⁰` at every field-valued point whose point lies in `Ω`. -/
theorem exists_isOpen_forall_isH0BijectiveAt
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hp : X.IsH0BijectiveAt p) :
    ∃ Ω : Set (Space.points B integerBase hZ (schemeSpace X.base).obj),
      IsOpen Ω ∧ p.class B integerBase hZ _ ∈ Ω ∧
        ∀ q : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
          q.class B integerBase hZ _ ∈ Ω → X.IsH0BijectiveAt q := by
  let Xs := (BigFppfOver.toScheme B integerBase hZ).obj X.base
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Scheme.isBasis_affineOpens Xs))
    (show Space.schemePoint B integerBase hZ X.base p ∈ (⊤ : Xs.Opens) from trivial)
  let W : Xs.affineOpens := ⟨U, hU⟩
  let hA := Space.contains_spec_affineOpen B integerBase hZ X.base W
  have := W.2.isOpenImmersion_fromSpec
  let fA := (Space.isTerminal_yoneda_obj_base B _ hA).from (restrictAffineOpen X W)
  obtain ⟨mp, hmp, hpiff⟩ := exists_factor_isH0BijectiveAt_iff X W p hxU
  let : Algebra Γ(Xs, U) p.carrier := (Spec.preimage mp.hom).hom.toAlgebra
  obtain ⟨h, hh, hnear⟩ :=
    Space.exists_away_bijective_algebraMap_globalFunctions_relocalizeRestrict
      (isAlgebraicSpace_restrictAffineOpen X W) fA
      (Space.isProper_restrictedFibre B integerBase hZ X.toBase.hom hA _ _ X.total.2
        (schemeSpace X.base).2 X.proper)
      (Space.isFlat_restrictedFibre B integerBase hZ X.toBase.hom hA _ _ X.total.2
        (schemeSpace X.base).2 X.flat)
      (Space.isFinitePresentation_restrictedFibre B integerBase hZ X.toBase.hom hA _ _ X.total.2
        (schemeSpace X.base).2 X.finitePresentation)
      p.carrier p.contained mp (Spec.map_preimage mp.hom).symm (hpiff.1 hp)
  refine ⟨Space.pointsToScheme B integerBase hZ X.base ⁻¹'
    (W.2.fromSpec '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum Γ(Xs, U)))), ?_, ?_, ?_⟩
  · refine (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B integerBase hZ X.base _).2 ?_
    convert W.2.fromSpec.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen h).isOpen using 1
    exact Set.image_preimage_eq _ (Space.surjective_pointsToScheme B integerBase hZ X.base)
  · refine ⟨mp.hom (IsLocalRing.closedPoint p.carrier), ?_, ?_⟩
    · rw [← Spec.map_preimage mp.hom]
      exact (Spec.map_closedPoint_mem_basicOpen_iff _ h).2 hh
    · exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        (congrArg (fun φ : Spec (.of p.carrier) ⟶ Xs => φ (IsLocalRing.closedPoint p.carrier)) hmp)
  · rintro q ⟨y, hy, hyq⟩
    have hxq : Space.schemePoint B integerBase hZ X.base q ∈ (W.1 : Set Xs) := by
      rw [← W.2.range_fromSpec]
      exact ⟨y, hyq⟩
    obtain ⟨mq, hmq, hqiff⟩ := exists_factor_isH0BijectiveAt_iff X W q hxq
    let : Algebra Γ(Xs, U) q.carrier := (Spec.preimage mq.hom).hom.toAlgebra
    refine hqiff.2 (hnear q.carrier q.contained mq (Spec.map_preimage mq.hom).symm ?_)
    refine isUnit_iff_ne_zero.2 ((Spec.map_closedPoint_mem_basicOpen_iff _ h).1 ?_)
    have hy' : mq.hom (IsLocalRing.closedPoint q.carrier) = y :=
      W.2.fromSpec.isOpenEmbedding.injective <| ((Scheme.Hom.comp_apply _ _ _).symm.trans
        (congrArg (fun φ : Spec (.of q.carrier) ⟶ Xs => φ (IsLocalRing.closedPoint q.carrier))
          hmq)).trans hyq.symm
    rwa [Spec.map_preimage, hy']

/-- A morphism of algebraic spaces whose base change along the identity induces a bijection on
global functions induces one itself. -/
theorem bijective_globalFunctionsMap_of_fiberProduct_id
    {F G : AlgebraicSpaces B integerBase hZ} (f : F ⟶ G)
    (h : Function.Bijective (Space.globalFunctionsMap B integerBase hZ
      (ObjectProperty.homMk (pullback.snd f.hom (𝟙 G.obj)) :
        AlgebraicSpaces.fiberProduct B integerBase hZ f (𝟙 G) ⟶ G))) :
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ f) := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ f (𝟙 G)
  have sq' : IsPullback (𝟙 F) f f (𝟙 G) := IsPullback.of_id_fst
  let e := sq.isoIsPullback _ _ sq'
  have h' : Function.Bijective (Space.globalFunctionsMap B integerBase hZ (e.hom ≫ f)) := by
    rwa [IsPullback.isoIsPullback_hom_snd _ _ sq sq']
  rw [Space.globalFunctionsMap_comp, RingHom.coe_comp] at h'
  exact ((Space.globalFunctionsMapEquiv B integerBase hZ e).bijective.of_comp_iff' _).1 h'

/-- **Local degree-zero cohomology and base change for a family of curves.** -/
theorem hasLocalH0BaseChange : X.HasLocalH0BaseChange := by
  intro p hp
  obtain ⟨Ω, hΩ, hpΩ, hq⟩ := exists_isOpen_forall_isH0BijectiveAt p hp
  refine ⟨Ω, hΩ, hpΩ, fun T t ht => ?_⟩
  have hF : HasBijectiveGlobalFunctionsOnFieldFibres B hZ (X.baseChange t) := fun q =>
    (isH0BijectiveAt_iff_of_hom (X.baseChangeHom t) q).2
      (hq _ (ht ⟨_, Space.pointsMap_class B integerBase hZ _ _ q⟩))
  exact bijective_globalFunctionsMap_of_fiberProduct_id (X.baseChange t).toBase
    (hasUniversallyBijectiveGlobalFunctions_of_fieldFibres _ hF (schemeSpace T) (𝟙 _))

end CurveFamily

/-- **Condition (o) of Stacks 0E0E for the fibrewise condition `k = H⁰(X_k, 𝒪_{X_k})`.** -/
theorem isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres
    {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} :
    IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ) :=
  isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of_hasLocalH0BaseChange
    CurveFamily.hasLocalH0BaseChange

/-- **Condition (o) of Stacks 0E0E for `Curves^{h0,1}` (Stacks 0E6I)**: the families of curves
with `f_*𝒪_X = 𝒪_S` universally form an open substack of `Curves`. -/
theorem isOpenCurvesLocus_isH01CurveFamily {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} :
    IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ) :=
  isOpenCurvesLocus_isH01CurveFamily_of_hasLocalH0BaseChange CurveFamily.hasLocalH0BaseChange
    fun _ hX => CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres _ hX

end AlgebraicGeometry

end
