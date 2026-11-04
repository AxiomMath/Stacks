module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcAmalgamation
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteLocalSections

/-!
# The étale refinement step, and the fpqc sheaf condition of Stacks 09XN

Let `S` be a scheme in a big étale site `B`, let `F` be a sheaf of sets on the small étale site
of `S` and let `π_S⁻¹F` be its inverse image along the projection from the big étale topos over
`S`. The uniqueness half of the fpqc sheaf condition for `π_S⁻¹F` is
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc`, and the existence
half was reduced in
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc_of_locallyRepresentable` to
the *local representability* of compatible families. This file discharges that hypothesis, so
the fpqc sheaf condition of Stacks 09XN becomes unconditional.

Local representability is the étale refinement step in the proof of Stacks 09XN: given an fpqc
covering `{p i : Z i ⟶ X}` and a compatible family `x i` of sections of `π_S⁻¹F`, one has to
produce a *big étale* covering `{v k : V k ⟶ X}` and sections `t k` of `π_S⁻¹F` over `V k`
agreeing with every `x i` on `V k ×_X Z i`.

The construction has three inputs, each already available.

* The local description of inverse-image sections,
  `AlgebraicGeometry.exists_locally_unit_section_smallEtale`: after restriction along a big
  étale covering sieve of `Z i`, the section `x i` becomes the restriction along some
  `h : Y ⟶ U` of a section of `F` over an object `U` of the small étale site of `S`.
* Base change along the structure morphism of `X`: `U` is étale over `S`, so `U ×_S X` is étale
  over `X`, and `Y` maps to it because it maps to `U` over `S` and to `X` through `Z i`. This
  produces a candidate `V` over `X` carrying a section which agrees with `x i` on `Y`, which is
  not yet enough: agreement is needed on all of `V ×_X Z j`.
* Descent of the equality loci (Stacks 09XN, step 4),
  `AlgebraicGeometry.existsUnique_preimage_eq_etaleInverseImageEqLocus`: the open loci of
  `U ×_S X` on which the candidate section agrees with
  the `x j` descend to a single open `W`, and `W` is the member of the refinement. Agreement on
  `W ×_X Z j` holds because `W ×_X Z j` lands in the equality locus; and the image of `Y`
  already lies in `W`, which makes the family `{W ⟶ X}` jointly surjective because the original
  fpqc covering and the covering sieves of the `Z i` are.

Joint surjectivity plus étaleness make `{W ⟶ X}` a big étale covering by
`AlgebraicGeometry.BigEtaleOver.generate_ofArrows_mem_topology`, which is exactly the remaining
clause.

## Main results

* `AlgebraicGeometry.exists_locally_represented_of_mem_fpqcPrecoverage` — the étale refinement
  step: every compatible family of sections of `π_S⁻¹F` on an fpqc covering is locally
  represented by sections over a jointly surjective big étale covering of the base.
* `AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc` — **Stacks 09XN, the fpqc
  sheaf condition**: the underlying presheaf of `π_S⁻¹F` is a sheaf for the fpqc topology on the
  big étale site over `S`. Unconditional.

## Implementation notes

Everything is phrased on the *presheaf* `π_S⁻¹F` on the big étale site over `S`, whose
restriction maps compose on the nose; no comparison of iterated inverse images on small étale
sites appears. The only place the small étale site of `S` is mentioned is the object `U`
produced by the local description of sections, and it is used solely through
`SmallEtale.inclusion`, which records that its structure morphism to `S` is étale.

Fibre products over `S` are the fibre products over the terminal object
`AlgebraicGeometry.BigEtaleOver.baseObj` of the big étale site over `S`, so they are instances
of `AlgebraicGeometry.BigEtaleOver.pairProduct` and need no separate construction; a morphism
to the terminal object is the structure morphism, which is
`AlgebraicGeometry.BigEtaleOver.toBaseObj_eq`.

The lift into a fibre product is re-proved here as
`AlgebraicGeometry.BigEtaleOver.pairLift` rather than reused: the corresponding declaration in
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcAmalgamation` is private
to that module.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Geometry

variable (B : BigEtaleSite.{u}) (S : B.Scheme)

/-! ### Fibre products over the base of the big étale site over `S` -/

/-- `S` itself, as an object of the big étale site over `S` through its identity. It is the
terminal object of that site, so fibre products over it are fibre products over `S`. -/
public def BigEtaleOver.baseObj : BigEtaleOver B S.obj S.property :=
  Over.mk (𝟙 (B.obj S.obj S.property))

/-- The structure morphism of an object of the big étale site over `S`, read as a morphism of
that site to `AlgebraicGeometry.BigEtaleOver.baseObj`. -/
public def BigEtaleOver.toBaseObj (Y : BigEtaleOver B S.obj S.property) :
    Y ⟶ BigEtaleOver.baseObj B S :=
  Over.homMk Y.hom (Category.comp_id _)

/-- `AlgebraicGeometry.BigEtaleOver.baseObj` is terminal: a morphism to it is the structure
morphism, because a morphism of schemes over `S` commutes with the structure morphisms and the
structure morphism of the base is the identity. -/
public theorem BigEtaleOver.toBaseObj_eq {Y : BigEtaleOver B S.obj S.property}
    (g : Y ⟶ BigEtaleOver.baseObj B S) : g = BigEtaleOver.toBaseObj B S Y :=
  Over.OverMorphism.ext ((Category.comp_id g.left).symm.trans (Over.w g))

/-- Composing with a structure morphism to the base gives the structure morphism to the base. -/
public theorem BigEtaleOver.comp_toBaseObj {Y Z : BigEtaleOver B S.obj S.property} (f : Y ⟶ Z) :
    f ≫ BigEtaleOver.toBaseObj B S Z = BigEtaleOver.toBaseObj B S Y :=
  BigEtaleOver.toBaseObj_eq B S _

/-- On points, a composite of morphisms of the big étale site over `S` acts as the composite of
the actions of its factors. -/
public theorem BigEtaleOver.inclusion_map_comp_apply
    {X Y Z : BigEtaleOver B S.obj S.property} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : B.inclusion.obj X.left) :
    B.inclusion.map (f ≫ g).left w = B.inclusion.map g.left (B.inclusion.map f.left w) := by
  rw [← Scheme.Hom.comp_apply]
  rfl

/-- The morphism into a fibre product over `X` determined by a pair of morphisms agreeing over
`X`.

This repeats a private declaration of
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcAmalgamation`, which is
not accessible from here. -/
public def BigEtaleOver.pairLift {X Y Z W : BigEtaleOver B S.obj S.property} (f : Y ⟶ X)
    (g : Z ⟶ X) (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    W ⟶ BigEtaleOver.pairProduct B S f g :=
  Over.homMk (Limits.pullback.lift a.left b.left (congrArg Over.Hom.left hab)) (by
    change Limits.pullback.lift a.left b.left (congrArg Over.Hom.left hab) ≫
      Limits.pullback.fst f.left g.left ≫ Y.hom = W.hom
    rw [← Category.assoc, Limits.pullback.lift_fst]
    exact Over.w a)

/-- The lift into a fibre product recovers its first component. -/
public theorem BigEtaleOver.pairLift_fst {X Y Z W : BigEtaleOver B S.obj S.property} (f : Y ⟶ X)
    (g : Z ⟶ X) (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    BigEtaleOver.pairLift B S f g a b hab ≫ BigEtaleOver.pairProductFst B S f g = a :=
  Over.OverMorphism.ext (Limits.pullback.lift_fst _ _ _)

/-- The lift into a fibre product recovers its second component. -/
public theorem BigEtaleOver.pairLift_snd {X Y Z W : BigEtaleOver B S.obj S.property} (f : Y ⟶ X)
    (g : Z ⟶ X) (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    BigEtaleOver.pairLift B S f g a b hab ≫ BigEtaleOver.pairProductSnd B S f g = b :=
  Over.OverMorphism.ext (Limits.pullback.lift_snd _ _ _)

/-- The fibre product `Y ×_S Z` of two objects of the big étale site over `S`, namely their
fibre product over the terminal object `AlgebraicGeometry.BigEtaleOver.baseObj`. -/
public def BigEtaleOver.baseProduct (Y Z : BigEtaleOver B S.obj S.property) :
    BigEtaleOver B S.obj S.property :=
  BigEtaleOver.pairProduct B S (BigEtaleOver.toBaseObj B S Y) (BigEtaleOver.toBaseObj B S Z)

/-- The first projection of `Y ×_S Z`. -/
public def BigEtaleOver.baseProductFst (Y Z : BigEtaleOver B S.obj S.property) :
    BigEtaleOver.baseProduct B S Y Z ⟶ Y :=
  BigEtaleOver.pairProductFst B S (BigEtaleOver.toBaseObj B S Y) (BigEtaleOver.toBaseObj B S Z)

/-- The second projection of `Y ×_S Z`. -/
public def BigEtaleOver.baseProductSnd (Y Z : BigEtaleOver B S.obj S.property) :
    BigEtaleOver.baseProduct B S Y Z ⟶ Z :=
  BigEtaleOver.pairProductSnd B S (BigEtaleOver.toBaseObj B S Y) (BigEtaleOver.toBaseObj B S Z)

/-- The morphism into `Y ×_S Z` determined by a pair of morphisms: no compatibility is needed,
because the base is terminal. -/
public def BigEtaleOver.baseProductLift {W Y Z : BigEtaleOver B S.obj S.property} (a : W ⟶ Y)
    (b : W ⟶ Z) : W ⟶ BigEtaleOver.baseProduct B S Y Z :=
  BigEtaleOver.pairLift B S _ _ a b
    ((BigEtaleOver.comp_toBaseObj B S a).trans (BigEtaleOver.comp_toBaseObj B S b).symm)

/-- The lift into `Y ×_S Z` recovers its first component. -/
public theorem BigEtaleOver.baseProductLift_fst {W Y Z : BigEtaleOver B S.obj S.property}
    (a : W ⟶ Y) (b : W ⟶ Z) :
    BigEtaleOver.baseProductLift B S a b ≫ BigEtaleOver.baseProductFst B S Y Z = a :=
  BigEtaleOver.pairLift_fst B S _ _ a b _

/-- The lift into `Y ×_S Z` recovers its second component. -/
public theorem BigEtaleOver.baseProductLift_snd {W Y Z : BigEtaleOver B S.obj S.property}
    (a : W ⟶ Y) (b : W ⟶ Z) :
    BigEtaleOver.baseProductLift B S a b ≫ BigEtaleOver.baseProductSnd B S Y Z = b :=
  BigEtaleOver.pairLift_snd B S _ _ a b _

/-- **Base change of an étale structure morphism.** If `Y` is étale over `S` then the second
projection `Y ×_S Z ⟶ Z` is étale, being the base change of the structure morphism of `Y` along
the structure morphism of `Z`. -/
public theorem BigEtaleOver.etale_baseProductSnd_left (Y Z : BigEtaleOver B S.obj S.property)
    (hY : Etale (B.inclusion.map Y.hom)) :
    Etale (B.inclusion.map (BigEtaleOver.baseProductSnd B S Y Z).left) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback Y.hom Z.hom).map B.inclusion) hY

/-- The inclusion of an open subscheme of an object of the big étale site over `S` is étale,
being an open immersion. -/
public theorem BigEtaleOver.etale_openObjι_left {X : BigEtaleOver B S.obj S.property}
    (V : (B.inclusion.obj X.left).Opens) :
    Etale (B.inclusion.map (BigEtaleOver.openObjι B S V).left) :=
  (inferInstance : Etale V.ι)

/-- **An fpqc covering stays an fpqc covering after base change.** The family of first
projections of the fibre products `W ×_X Z i` is an fpqc covering of `W` as soon as
`{Z i ⟶ X}` is an fpqc covering of `X`. -/
public theorem BigEtaleOver.pairProductFst_mem_fpqcPrecoverage_comap
    {X : BigEtaleOver B S.obj S.property} {I : Type*}
    (Z : I → BigEtaleOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) X)
    {W : BigEtaleOver B S.obj S.property} (q : W ⟶ X) :
    Presieve.ofArrows (fun i => BigEtaleOver.pairProduct B S q (p i))
        (fun i => BigEtaleOver.pairProductFst B S q (p i)) ∈
      Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) W := by
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hp ⊢
  exact Precoverage.mem_coverings_of_isPullback _ hp _ _
    (fun i => (BigEtaleOver.toScheme B S.obj S.property).map
      (BigEtaleOver.pairProductSnd B S q (p i)))
    fun i => (IsPullback.of_hasPullback q.left (p i).left).map B.inclusion

end Geometry

/-! ### The étale refinement step -/

section Refinement

variable (B : BigEtaleSite.{u}) (S : B.Scheme)
  (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))

/-- The section of `π_S⁻¹F` over an object `U` of the small étale site of `S` attached to a
section of `F` over `U` by the adjunction unit of the projection `π_S`. -/
public def etaleUnitSection (U : SmallEtale B S.obj S.property) (t : F.obj.obj (op U)) :
    (etaleInverseImagePresheaf B S F).obj
      (op ((SmallEtale.inclusion B S.obj S.property).obj U)) :=
  Functor.unitSection (SmallEtale.inclusion B S.obj S.property)
    (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property)
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).adj F U t

/-- Restricted along a big étale covering sieve, a section of `π_S⁻¹F` is the restriction of a
section coming from the small étale site of `S`.

This is `AlgebraicGeometry.exists_locally_unit_section_smallEtale` with the unit section named
by `AlgebraicGeometry.etaleUnitSection`. -/
public theorem exists_locally_etaleUnitSection (X : BigEtaleOver B S.obj S.property)
    (s : (etaleInverseImagePresheaf B S F).obj (op X)) :
    ∃ R : Sieve X, R ∈ BigEtaleOver.topology B S.obj S.property X ∧
      ∀ ⦃Y : BigEtaleOver B S.obj S.property⦄ (k : Y ⟶ X), R k →
        ∃ (U : SmallEtale B S.obj S.property)
          (h : Y ⟶ (SmallEtale.inclusion B S.obj S.property).obj U) (t : F.obj.obj (op U)),
          (etaleInverseImagePresheaf B S F).map k.op s =
            (etaleInverseImagePresheaf B S F).map h.op (etaleUnitSection B S F U t) :=
  exists_locally_unit_section_smallEtale B S.obj S.property F X s

/-- Two sections pulled back to a fibre product agree along a lift exactly when their pullbacks
along the components of the lift agree. -/
private theorem map_pairLift_eq_iff {X Y Z W : BigEtaleOver B S.obj S.property} (f : Y ⟶ X)
    (g : Z ⟶ X) (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g)
    (s : (etaleInverseImagePresheaf B S F).obj (op Z))
    (t : (etaleInverseImagePresheaf B S F).obj (op Y)) :
    (etaleInverseImagePresheaf B S F).map (BigEtaleOver.pairLift B S f g a b hab).op
        ((etaleInverseImagePresheaf B S F).map (BigEtaleOver.pairProductSnd B S f g).op s) =
      (etaleInverseImagePresheaf B S F).map (BigEtaleOver.pairLift B S f g a b hab).op
        ((etaleInverseImagePresheaf B S F).map (BigEtaleOver.pairProductFst B S f g).op t) ↔
    (etaleInverseImagePresheaf B S F).map b.op s =
      (etaleInverseImagePresheaf B S F).map a.op t := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    BigEtaleOver.pairLift_fst, BigEtaleOver.pairLift_snd]

/-- **One member of the étale refinement.** Suppose a section `x i` of `π_S⁻¹F` over a member
`Z i` of an fpqc covering of `X` becomes, after restriction along `k : Y ⟶ Z i`, the
restriction along `h : Y ⟶ U` of a section coming from an object `U` of the small étale site of
`S`. Then there is an object `V` of the big étale site over `S`, an *étale* morphism
`v : V ⟶ X` whose image contains the image of `Y`, and a section `s` of `π_S⁻¹F` over `V`
agreeing with every member `x j` of the family on `V ×_X Z j`.

`V` is an open subscheme of `U ×_S X`: the section coming from `U` and the family `x j` agree
on an open of `(U ×_S X) ×_X Z j` by Stacks 09XM, these opens descend along the fpqc covering
to an open `V` of `U ×_S X` by Stacks 03N0
(`AlgebraicGeometry.existsUnique_preimage_eq_etaleInverseImageEqLocus`), and the image of `Y`
lies in `V` because `Y` maps to `(U ×_S X) ×_X Z i` compatibly with both sections. -/
public theorem exists_etale_refinement_member {X : BigEtaleOver B S.obj S.property}
    {I : Type (u + 1)} (Z : I → BigEtaleOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) X)
    (x : ∀ i, (etaleInverseImagePresheaf B S F).obj (op (Z i)))
    (hx : Presieve.Arrows.Compatible (etaleInverseImagePresheaf B S F) p x)
    {Y : BigEtaleOver B S.obj S.property} {i : I} (k : Y ⟶ Z i)
    (U : SmallEtale B S.obj S.property)
    (h : Y ⟶ (SmallEtale.inclusion B S.obj S.property).obj U) (t : F.obj.obj (op U))
    (hkt : (etaleInverseImagePresheaf B S F).map k.op (x i) =
      (etaleInverseImagePresheaf B S F).map h.op (etaleUnitSection B S F U t)) :
    ∃ (V : BigEtaleOver B S.obj S.property) (v : V ⟶ X)
      (s : (etaleInverseImagePresheaf B S F).obj (op V)),
      Etale (B.inclusion.map v.left) ∧
        (∀ w : B.inclusion.obj Y.left,
          B.inclusion.map (k ≫ p i).left w ∈ Set.range (B.inclusion.map v.left)) ∧
        ∀ j, (etaleInverseImagePresheaf B S F).map
              (BigEtaleOver.pairProductFst B S v (p j)).op s =
          (etaleInverseImagePresheaf B S F).map
            (BigEtaleOver.pairProductSnd B S v (p j)).op (x j) := by
  -- The candidate `U ×_S X`, its projection to `X`, and the section it carries.
  set VF := BigEtaleOver.baseProduct B S
    ((SmallEtale.inclusion B S.obj S.property).obj U) X
  set qF := BigEtaleOver.baseProductSnd B S
    ((SmallEtale.inclusion B S.obj S.property).obj U) X
  set tF := (etaleInverseImagePresheaf B S F).map
    (BigEtaleOver.baseProductFst B S
      ((SmallEtale.inclusion B S.obj S.property).obj U) X).op
    (etaleUnitSection B S F U t) with htF
  -- `Y` maps to the candidate, and the candidate's section agrees there with `x i`.
  set a := BigEtaleOver.baseProductLift B S h (k ≫ p i)
  have haq : a ≫ qF = k ≫ p i := BigEtaleOver.baseProductLift_snd B S h (k ≫ p i)
  have hkey : (etaleInverseImagePresheaf B S F).map a.op tF =
      (etaleInverseImagePresheaf B S F).map k.op (x i) := by
    rw [htF, ← Functor.map_comp_apply, ← op_comp,
      BigEtaleOver.baseProductLift_fst B S h (k ≫ p i), hkt]
  -- The base change of the fpqc covering to the candidate, and the restricted family.
  have hpF : Presieve.ofArrows (fun j => BigEtaleOver.pairProduct B S qF (p j))
      (fun j => BigEtaleOver.pairProductFst B S qF (p j)) ∈
      Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) VF :=
    BigEtaleOver.pairProductFst_mem_fpqcPrecoverage_comap B S Z p hp qF
  have hxF : Presieve.Arrows.Compatible (etaleInverseImagePresheaf B S F)
      (fun j => BigEtaleOver.pairProductFst B S qF (p j))
      (fun j => (etaleInverseImagePresheaf B S F).map
        (BigEtaleOver.pairProductSnd B S qF (p j)).op (x j)) := by
    intro j₁ j₂ W g₁ g₂ hg
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    refine hx j₁ j₂ W _ _ ?_
    rw [Category.assoc, Category.assoc, ← BigEtaleOver.pairProduct_condition,
      ← BigEtaleOver.pairProduct_condition, ← Category.assoc, ← Category.assoc, hg]
  -- Stacks 03N0 descends the equality loci to an open of the candidate.
  obtain ⟨W, hW, -⟩ := existsUnique_preimage_eq_etaleInverseImageEqLocus B S F
    (fun j => BigEtaleOver.pairProduct B S qF (p j))
    (fun j => BigEtaleOver.pairProductFst B S qF (p j)) hpF
    (fun j => (etaleInverseImagePresheaf B S F).map
      (BigEtaleOver.pairProductSnd B S qF (p j)).op (x j)) hxF tF
  refine ⟨BigEtaleOver.openObj B S W, BigEtaleOver.openObjι B S W ≫ qF,
    (etaleInverseImagePresheaf B S F).map (BigEtaleOver.openObjι B S W).op tF, ?_, ?_, ?_⟩
  · -- The member is étale over `X`: an open immersion followed by a base change of `U ⟶ S`.
    have h₁ : Etale (B.inclusion.map (BigEtaleOver.openObjι B S W).left) :=
      BigEtaleOver.etale_openObjι_left B S W
    have h₂ : Etale (B.inclusion.map qF.left) :=
      BigEtaleOver.etale_baseProductSnd_left B S _ X U.property
    rw [show (BigEtaleOver.openObjι B S W ≫ qF).left =
      (BigEtaleOver.openObjι B S W).left ≫ qF.left from rfl, B.inclusion.map_comp]
    infer_instance
  · -- The image of `Y` lies in the member.
    intro w
    have heq := (map_pairLift_eq_iff B S F qF (p i) a k haq (x i) tF).mpr hkey.symm
    have hmem := (forall_mem_etaleInverseImageEqLocus_iff B S F _ _
      (BigEtaleOver.pairLift B S qF (p i) a k haq)).mpr heq w
    rw [← hW i, Scheme.Hom.mem_preimage, ← BigEtaleOver.inclusion_map_comp_apply,
      BigEtaleOver.pairLift_fst] at hmem
    refine ⟨⟨B.inclusion.map a.left w, hmem⟩,
      (BigEtaleOver.inclusion_map_comp_apply B S (BigEtaleOver.openObjι B S W) qF
        ⟨B.inclusion.map a.left w, hmem⟩).trans ?_⟩
    exact (BigEtaleOver.inclusion_map_comp_apply B S a qF w).symm.trans
      (congrArg (fun m : Y ⟶ X => B.inclusion.map m.left w) haq)
  · -- The member's section agrees with the whole family.
    intro j
    have hcond : (BigEtaleOver.pairProductFst B S (BigEtaleOver.openObjι B S W ≫ qF) (p j) ≫
          BigEtaleOver.openObjι B S W) ≫ qF =
        BigEtaleOver.pairProductSnd B S (BigEtaleOver.openObjι B S W ≫ qF) (p j) ≫ p j :=
      (Category.assoc _ _ _).trans
        (BigEtaleOver.pairProduct_condition B S (BigEtaleOver.openObjι B S W ≫ qF) (p j))
    have hmem : ∀ q, B.inclusion.map
        (BigEtaleOver.pairLift B S qF (p j) _ _ hcond).left q ∈
        etaleInverseImageEqLocus B S F (BigEtaleOver.pairProduct B S qF (p j))
          ((etaleInverseImagePresheaf B S F).map
            (BigEtaleOver.pairProductSnd B S qF (p j)).op (x j))
          ((etaleInverseImagePresheaf B S F).map
            (BigEtaleOver.pairProductFst B S qF (p j)).op tF) := by
      intro q
      rw [← hW j, Scheme.Hom.mem_preimage, ← BigEtaleOver.inclusion_map_comp_apply,
        BigEtaleOver.pairLift_fst, BigEtaleOver.inclusion_map_comp_apply,
        BigEtaleOver.openObjι_apply]
      exact (_ : (B.inclusion.obj (BigEtaleOver.openObj B S W).left)).property
    have hagree := (forall_mem_etaleInverseImageEqLocus_iff B S F _ _
      (BigEtaleOver.pairLift B S qF (p j) _ _ hcond)).mp hmem
    rw [map_pairLift_eq_iff, op_comp, Functor.map_comp_apply] at hagree
    exact hagree.symm

/-- **Stacks 09XN, the étale refinement step.** Every compatible family of sections of `π_S⁻¹F`
on an fpqc covering `{p i : Z i ⟶ X}` is *locally represented*: there are a family
`{v k : V k ⟶ X}` generating a covering sieve of the big étale topology and jointly surjective
on points, and sections `t k` of `π_S⁻¹F` over `V k`, such that `t k` agrees with every `x i` on
the fibre product `V k ×_X Z i`.

The members are produced one at a time by
`AlgebraicGeometry.exists_etale_refinement_member`, indexed by the arrows of the big étale
covering sieves along which the sections `x i` come from the small étale site of `S`
(`AlgebraicGeometry.exists_locally_etaleUnitSection`). Joint surjectivity holds because an fpqc
covering is jointly surjective and so is each of those covering sieves
(`AlgebraicGeometry.BigEtaleOver.exists_mem_arrows_mem_range`), and each member's image
contains the image of the arrow it was built from; étaleness of the members then makes the
family a big étale covering by
`AlgebraicGeometry.BigEtaleOver.generate_ofArrows_mem_topology`. -/
public theorem exists_locally_represented_of_mem_fpqcPrecoverage
    (X : BigEtaleOver B S.obj S.property) (I : Type (u + 1))
    (Z : I → BigEtaleOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) X)
    (x : ∀ i, (etaleInverseImagePresheaf B S F).obj (op (Z i)))
    (hx : Presieve.Arrows.Compatible (etaleInverseImagePresheaf B S F) p x) :
    ∃ (K : Type (u + 1)) (V : K → BigEtaleOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
      (t : ∀ k, (etaleInverseImagePresheaf B S F).obj (op (V k))),
      Sieve.generate (Presieve.ofArrows V v) ∈
          BigEtaleOver.topology B S.obj S.property X ∧
        (∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left)) ∧
        ∀ k i, (etaleInverseImagePresheaf B S F).map
              (BigEtaleOver.pairProductFst B S (v k) (p i)).op (t k) =
          (etaleInverseImagePresheaf B S F).map
            (BigEtaleOver.pairProductSnd B S (v k) (p i)).op (x i) := by
  classical
  -- Each `x i` comes from the small étale site of `S` along a big étale covering sieve of `Z i`.
  choose R hRmem hRdata using fun i => exists_locally_etaleUnitSection B S F (Z i) (x i)
  -- One member of the refinement for each arrow of each of those sieves.
  choose U hU t hUt using fun κ : Σ (i : I) (Y : BigEtaleOver B S.obj S.property),
    {k : Y ⟶ Z i // (R i).arrows k} => hRdata κ.1 κ.2.2.1 κ.2.2.2
  choose V v s hetale hrange hagree using fun κ : Σ (i : I)
    (Y : BigEtaleOver B S.obj S.property), {k : Y ⟶ Z i // (R i).arrows k} =>
    exists_etale_refinement_member B S F Z p hp x hx κ.2.2.1 (U κ) (hU κ) (t κ) (hUt κ)
  -- The members are jointly surjective: the fpqc covering and the sieves are.
  have hpS := hp
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hpS
  have hsurj : ∀ y : B.inclusion.obj X.left,
      ∃ κ, y ∈ Set.range (B.inclusion.map (v κ).left) := by
    intro y
    obtain ⟨i, z, hz⟩ := fpqc_jointly_surjective _ hpS y
    obtain ⟨Y, k, hk, w, hw⟩ :=
      BigEtaleOver.exists_mem_arrows_mem_range B S.obj S.property (hRmem i) z
    obtain ⟨y', hy'⟩ := hrange ⟨i, Y, ⟨k, hk⟩⟩ w
    refine ⟨⟨i, Y, ⟨k, hk⟩⟩, y', hy'.trans ?_⟩
    rwa [BigEtaleOver.inclusion_map_comp_apply, hw]
  exact ⟨_, V, v, s,
    BigEtaleOver.generate_ofArrows_mem_topology B S.obj S.property V v hetale hsurj,
    hsurj, hagree⟩

end Refinement

/-! ### The fpqc sheaf condition -/

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09XN, the fpqc sheaf condition.** Let `S` be a scheme in a big étale site `B`, let
`F` be a sheaf of sets on the small étale site of `S` and let `π_S` be the projection from the
big étale topos over `S` to the small étale topos of `S`. Then the presheaf underlying
`π_S⁻¹F` — by the sections formula, `X ↦ Γ(X_ét, f_X⁻¹F)` — is a sheaf for the fpqc topology on
the big étale site over `S`.

The uniqueness half is
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc` and the existence
half is `AlgebraicGeometry.exists_isAmalgamation_of_locallyRepresentable`, whose local
representability hypothesis is the étale refinement step
`AlgebraicGeometry.exists_locally_represented_of_mem_fpqcPrecoverage`.

This declaration carries no `@[stacks 09XN "fpqc_sheaf"]` attribute. That sub-label covers two
statements, the big étale one proved here and the big Zariski one, as the sibling sub-label
`"pullback_formula"` is carried by both site variants. The Zariski statement needs the Zariski
mirror of the amalgamation machinery used here and is not proved, so tagging this declaration
alone would report the sub-label as covered when half of it is missing. -/
public theorem bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S hS)).toGrothendieck)
      ((bigEtaleToSmallEtaleMorphism B S hS).inverseImage.obj F).obj :=
  bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc_of_locallyRepresentable B S hS F
    fun X I Z p hp y hy =>
      exists_locally_represented_of_mem_fpqcPrecoverage B (B.obj S hS) F X I Z p hp y hy

end AlgebraicGeometry

end
