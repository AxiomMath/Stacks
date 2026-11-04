module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Reduction of the separably closed case of proper base change to the algebraically closed case

Stacks Project Tag 0A5E says that for a proper scheme of dimension at most one over a separably
closed field, extending the separably closed ground field does not change the étale cohomology
of a torsion abelian sheaf. Tag 03SC part (7) is the same statement for an extension of
*algebraically* closed fields.

The two tags cite each other: the proof of 03SC given in the Stacks Project is "algebraically
closed implies separably closed, so apply 0A5E", and the proof of 0A5E given there passes to
algebraic closures and applies 03SC. The second direction is the real one — it applies 03SC to a
*different* scheme over a *different* pair of fields, namely to `X ×_k \bar k` over
`\bar k ⊆ \bar{k'}` — whereas the first applies 0A5E to the same scheme over the same pair of
fields and so cannot be the base case. This file carries that real direction.

## Main definitions

* `Stacks.EtaleCohomology.ProperBaseChangeOverAlgClosed` is the algebraically closed case of
  proper base change, stated through `Stacks.EtaleCohomology.IsBijectiveOnExt` so that it does
  not mention a choice of `HasExt` universe.

## Main results

* `Stacks.EtaleCohomology.properBaseChangeOverAlgClosed_iff`: the `Ext` form of the
  algebraically closed case is equivalent, in any `HasExt` universe, to bijectivity of the
  restriction map on étale cohomology, i.e. to Tag 03SC part (7) as stated.
* `Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of`:
  Tag 0A5E, given the algebraically closed case.

## Implementation notes

**Nothing here carries `@[stacks 0A5E]`.** The single mathematical input,
`ProperBaseChangeOverAlgClosed`, is Tag 03SC part (7), the main theorem of the source's section
on the cohomology of curves; it is genuinely missing from this library and from Mathlib, and is
carried as a hypothesis rather than assumed by an unproved placeholder. It is not derivable from
Tag 0A5E: the source's proof of Tag 03SC in that direction is the observation that an
algebraically closed field is separably closed, which applies Tag 0A5E to the *same* scheme over
the *same* pair of fields and so is circular. The real direction is the one carried here, which
applies Tag 03SC to a different scheme over a different pair of fields. Closing Tag 03SC part
(7) needs the dévissage of a torsion sheaf into constructible `ℓ`-torsion pieces, extension by
zero along an open immersion, and the cohomology of a smooth curve over an algebraically closed
field by way of Tsen's theorem.

Topological invariance of the small étale site is *not* an input. What the argument needs of a
universal homeomorphism `g` is that `Stacks.EtaleCohomology.smallEtaleBaseChange g` exhibits a
dense subsite, which is Tag 03SI part (1) and is proved outright by
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism` on the strength of property
(C), Tag 04DW. Essential surjectivity — the remaining and hard content of Tag 04DZ — is never
used: the only place it entered was the transport of the torsion condition along an inverse
image, and `Stacks.EtaleCohomology.torsionSheafProperty_inverseImage_of_isDenseSubsite` performs
that transport from cover-density alone.

The reduction itself is the argument of the source. Write `K = \bar k` and `L = \bar{k'}`,
chosen compatibly, and put `X₀ = X ×_k K`. Since `k` is separably closed, `K/k` is purely
inseparable, so `X₀ → X` is a universal homeomorphism; likewise `L/k'` is purely inseparable, so
`X ×_k L → X ×_k k'` is one. The square of the four scalar extensions commutes, so the two
composite inverse images from `X` to `X ×_k L` are isomorphic. Topological invariance makes the
two universal-homeomorphism legs bijective on `Ext`, and the algebraically closed case makes the
leg from `X₀` to `X ×_k L` bijective; cancelling gives the remaining leg, which is the one over
`k ⊆ k'`.

Dimension is preserved along the first leg because a universal homeomorphism is in particular a
homeomorphism.

Sheafification is no longer a hypothesis. The two intermediate schemes `X ×_k \bar k` and
`X ×_k \bar{k'}` are built inside the proof, so an instance for them could not be named in the
statement; it is now supplied uniformly by
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`, which holds for every scheme and
every coefficient universe of the form `max (u + 1) v`. Consequently
`etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of` has exactly one non-instance
hypothesis left, namely `ProperBaseChangeOverAlgClosed`.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 0A5E](https://stacks.math.columbia.edu/tag/0A5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- Proper base change over algebraically closed fields, Stacks Project Tag 03SC part (7): for
an extension of algebraically closed fields, scalar extension of a proper scheme of dimension at
most one preserves the étale cohomology of every torsion abelian sheaf. Stated through
`IsBijectiveOnExt`, which is bijectivity of the restriction map on étale cohomology by
`properBaseChangeOverAlgClosed_iff` and mentions no `HasExt` universe. -/
def ProperBaseChangeOverAlgClosed : Prop :=
  ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f], topologicalKrullDim X ≤ 1 →
    ∀ (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}),
      Stacks.Torsion.torsionSheafProperty.{max (u + 1) v} (smallEtaleTopology X) F →
      ∀ q : ℕ, IsBijectiveOnExt
        (etaleAbelianInverseImage.{u, v} (scalarExtensionFst k k' f))
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q

/-- The `Ext` form of the algebraically closed case of proper base change is bijectivity of the
restriction map on étale cohomology, in any `HasExt` universe. -/
theorem properBaseChangeOverAlgClosed_iff
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (smallEtaleTopology (scalarExtension k k' f))
      AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    IsBijectiveOnExt (etaleAbelianInverseImage.{u, v} (scalarExtensionFst k k' f))
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q ↔
      Function.Bijective
        (etaleCohomologyBaseChangeMap.{u, v, w} k k' f F q) :=
  ((etaleCohomologyRestrictionMap_bijective_iff.{u, v, w} (scalarExtensionFst k k' f) F q).trans
    (mapExt_bijective_iff_mapDerivedCategory _ _ _ _)).symm

/-- Inverse image along `g` is bijective on `Ext` out of the pulled-back constant sheaf `ℤ` exactly
when it is bijective on `Ext` out of the constant sheaf `ℤ` on the source of `g`. -/
private theorem isBijectiveOnExt_obj_iff_constant {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (p : Y ⟶ X)
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    IsBijectiveOnExt (etaleAbelianInverseImage.{u, v} g)
        ((etaleAbelianInverseImage.{u, v} p).obj
          ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)))) F q ↔
      IsBijectiveOnExt (etaleAbelianInverseImage.{u, v} g)
        ((constantSheaf (smallEtaleTopology Y) AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q :=
  isBijectiveOnExt_congr_obj _
    ((etaleAbelianInverseImageConstantIso.{u, v} p).app
      (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) (Iso.refl _) q

/-- **Stacks Project, Tag 0A5E**, given the algebraically closed case of proper base change
(Tag 03SC part (7)). For an extension of separably closed fields, scalar extension of a proper
scheme of dimension at most one preserves the étale cohomology of every torsion abelian sheaf in
every nonnegative degree. -/
theorem etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of
    (habc : ProperBaseChangeOverAlgClosed.{u, v})
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsSepClosed k] [IsSepClosed k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (smallEtaleTopology (scalarExtension k k' f))
      AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty.{max (u + 1) v} (smallEtaleTopology X) F)
    (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' f) F q) := by
  let K := AlgebraicClosure k
  let L := AlgebraicClosure k'
  let a : K →ₐ[k] L := IsAlgClosed.lift
  let : Algebra K L := a.toRingHom.toAlgebra
  have : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq (fun x => (a.commutes x).symm)
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let c := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let d := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let e := Spec.map (CommRingCat.ofHom (algebraMap k' L))
  have he : d ≫ b = e ≫ c := by
    dsimp [b, c, d, e]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq k K L).symm.trans
      (IsScalarTower.algebraMap_eq k k' L)
  let X₀ := pullback f b
  let f₀ : X₀ ⟶ Spec (.of K) := pullback.snd f b
  let p : X₀ ⟶ X := pullback.fst f b
  let Z := pullback f₀ d
  let r : Z ⟶ X₀ := pullback.fst f₀ d
  let z : Z ⟶ Spec (.of L) := pullback.snd f₀ d
  let X₁ := pullback f c
  let f₁ : X₁ ⟶ Spec (.of k') := pullback.snd f c
  let p₁ : X₁ ⟶ X := pullback.fst f c
  have houter : IsPullback (r ≫ p) z f (e ≫ c) := by
    rw [← he]
    exact (IsPullback.of_hasPullback f₀ d).paste_horiz (IsPullback.of_hasPullback f b)
  let t : Z ⟶ X₁ := pullback.lift (f := f) (g := c) (r ≫ p) (z ≫ e)
    (by simpa only [Category.assoc] using houter.w)
  have htp : t ≫ p₁ = r ≫ p := pullback.lift_fst _ _ _
  have htf : t ≫ f₁ = z ≫ e := pullback.lift_snd _ _ _
  have ht : IsPullback t z f₁ e := by
    apply IsPullback.of_right (h₁₂ := p₁) (h₂₂ := c)
    · simpa only [htp] using houter
    · exact htf
    · exact IsPullback.of_hasPullback f c
  have hp : UniversalHomeomorphism p :=
    scalarExtensionFst_universalHomeomorphism_of_isPurelyInseparable k K f
  have ht' : UniversalHomeomorphism t :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback ht.flip
      (specMap_universalHomeomorphism_of_isPurelyInseparable k' L).universally_isHomeomorph⟩
  have hpdim : topologicalKrullDim X₀ ≤ 1 := by
    have hhomeo : IsHomeomorph p :=
      hp.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
    exact (hhomeo.topologicalKrullDim_eq p).trans_le hdim
  let : (smallEtaleBaseChange p).IsDenseSubsite
      (smallEtaleTopology X) (smallEtaleTopology X₀) :=
    have := hp
    isDenseSubsite_of_universalHomeomorphism p
  let : (smallEtaleBaseChange t).IsDenseSubsite
      (smallEtaleTopology X₁) (smallEtaleTopology Z) :=
    have := ht'
    isDenseSubsite_of_universalHomeomorphism t
  let P := etaleAbelianInverseImage.{u, v} p
  let R := etaleAbelianInverseImage.{u, v} r
  let P₁ := etaleAbelianInverseImage.{u, v} p₁
  let T := etaleAbelianInverseImage.{u, v} t
  let I := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))
  have hP : IsBijectiveOnExt P I F q :=
    isBijectiveOnExt_etaleAbelianInverseImage_of_isDenseSubsite.{u, v} p F q
  have hR : IsBijectiveOnExt R (P.obj I) (P.obj F) q :=
    (isBijectiveOnExt_obj_iff_constant.{u, v} r p _ q).mpr
      (habc K L f₀ hpdim (P.obj F)
        (torsionSheafProperty_inverseImage_of_isDenseSubsite.{u, v} p F hF) q)
  have hT : IsBijectiveOnExt T (P₁.obj I) (P₁.obj F) q :=
    (isBijectiveOnExt_obj_iff_constant.{u, v} t p₁ _ q).mpr
      (isBijectiveOnExt_etaleAbelianInverseImage_of_isDenseSubsite.{u, v} t (P₁.obj F) q)
  have hcomp : IsBijectiveOnExt (P ⋙ R) I F q :=
    (isBijectiveOnExt_comp_iff P R I F q hR).mpr hP
  have hsquare : P ⋙ R ≅ P₁ ⋙ T :=
    (etaleAbelianInverseImageCompIso.{u, v} r p).symm ≪≫
      eqToIso (congrArg (fun g : Z ⟶ X => etaleAbelianInverseImage.{u, v} g) htp.symm) ≪≫
        etaleAbelianInverseImageCompIso.{u, v} t p₁
  exact (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w} p₁ F q).mpr
    ((isBijectiveOnExt_comp_iff P₁ T I F q hT).mp
      ((isBijectiveOnExt_congr hsquare I F q).mp hcomp))

end Stacks.EtaleCohomology

end
