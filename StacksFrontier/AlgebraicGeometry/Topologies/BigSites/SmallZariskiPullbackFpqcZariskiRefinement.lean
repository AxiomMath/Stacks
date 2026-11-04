module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiPullbackFpqcAmalgamation
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteLocalSections

/-!
# The Zariski refinement step, and the fpqc sheaf condition of Stacks 09XN

Let `S` be a scheme in a big Zariski site `B`, let `F` be a sheaf of sets on the small Zariski
site of `S` and let `π_S⁻¹F` be its inverse image along the projection from the big Zariski
topos over `S`. The uniqueness half of the fpqc sheaf condition for `π_S⁻¹F` is
`AlgebraicGeometry.smallZariskiProjection_inverseImage_isSeparatedFor_fpqc`, and the existence
half was reduced in
`AlgebraicGeometry.smallZariskiProjection_inverseImage_isSheaf_fpqc_of_locallyRepresentable` to
the *local representability* of compatible families. This file discharges that hypothesis, so
the fpqc sheaf condition of Stacks 09XN becomes unconditional for the big Zariski site.

Local representability is the Zariski refinement step in the proof of Stacks 09XN: given an
fpqc covering `{p i : Z i ⟶ X}` and a compatible family `x i` of sections of `π_S⁻¹F`, one has
to produce a *big Zariski* covering `{v k : V k ⟶ X}` and sections `t k` of `π_S⁻¹F` over
`V k` agreeing with every `x i` on `V k ×_X Z i`.

The construction has three inputs, each already available.

* The local description of inverse-image sections,
  `AlgebraicGeometry.exists_locally_unit_section_smallZariski`: after restriction along a big
  Zariski covering sieve of `Z i`, the section `x i` becomes the restriction along some
  `h : Y ⟶ U` of a section of `F` over an open subscheme `U` of `S`.
* Base change along the structure morphism of `X`: `U` is open in `S`, so `U ×_S X` is open in
  `X`, and `Y` maps to it because it maps to `U` over `S` and to `X` through `Z i`. This
  produces a candidate `V` over `X` carrying a section which agrees with `x i` on `Y`, which is
  not yet enough: agreement is needed on all of `V ×_X Z j`.
* Descent of the equality loci (Stacks 09XN, step 4),
  `AlgebraicGeometry.existsUnique_preimage_eq_zariskiInverseImageEqLocus`: the open loci of
  `U ×_S X` on which the candidate section agrees with the `x j` descend to a single open `W`,
  and `W` is the member of the refinement. Agreement on `W ×_X Z j` holds because `W ×_X Z j`
  lands in the equality locus; and the image of `Y` already lies in `W`, which makes the family
  `{W ⟶ X}` jointly surjective because the original fpqc covering and the covering sieves of
  the `Z i` are.

Joint surjectivity plus openness make `{W ⟶ X}` a big Zariski covering by
`AlgebraicGeometry.BigZariskiOver.generate_ofArrows_mem_topology`, which is exactly the
remaining clause.

## Main results

* `AlgebraicGeometry.exists_locally_represented_of_mem_fpqcPrecoverage_zariski` — the Zariski
  refinement step: every compatible family of sections of `π_S⁻¹F` on an fpqc covering is
  locally represented by sections over a jointly surjective big Zariski covering of the base.
* `AlgebraicGeometry.smallZariskiProjection_inverseImage_isSheaf_fpqc` — **Stacks 09XN, the
  fpqc sheaf condition**: the underlying presheaf of `π_S⁻¹F` is a sheaf for the fpqc topology
  on the big Zariski site over `S`. Unconditional.

## Implementation notes

Everything is phrased on the *presheaf* `π_S⁻¹F` on the big Zariski site over `S`, whose
restriction maps compose on the nose; no comparison of iterated inverse images on small Zariski
sites appears. The only place the small Zariski site of `S` is mentioned is the object `U`
produced by the local description of sections, and it is used solely through
`AlgebraicGeometry.SmallZariski.inclusion`, which records that its structure morphism to `S` is
an open immersion.

Fibre products over `S` are the fibre products over the terminal object
`AlgebraicGeometry.BigZariskiOver.baseObj` of the big Zariski site over `S`, so they are
instances of `AlgebraicGeometry.BigZariskiOver.pairProduct` and need no separate construction;
a morphism to the terminal object is the structure morphism, which is
`AlgebraicGeometry.BigZariskiOver.toBaseObj_eq`.

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

variable (B : BigZariskiSite.{u}) (S : B.Schemes)

/-! ### Fibre products over the base of the big Zariski site over `S` -/

/-- `S` itself, as an object of the big Zariski site over `S` through its identity. It is the
terminal object of that site, so fibre products over it are fibre products over `S`. -/
public def BigZariskiOver.baseObj : BigZariskiOver B S.obj S.property := Over.mk (𝟙 S)

/-- The structure morphism of an object of the big Zariski site over `S`, read as a morphism of
that site to `AlgebraicGeometry.BigZariskiOver.baseObj`. -/
public def BigZariskiOver.toBaseObj (Y : BigZariskiOver B S.obj S.property) :
    Y ⟶ BigZariskiOver.baseObj B S :=
  Over.homMk Y.hom (Category.comp_id _)

/-- `AlgebraicGeometry.BigZariskiOver.baseObj` is terminal: a morphism to it is the structure
morphism, because a morphism of schemes over `S` commutes with the structure morphisms and the
structure morphism of the base is the identity. -/
public theorem BigZariskiOver.toBaseObj_eq {Y : BigZariskiOver B S.obj S.property}
    (g : Y ⟶ BigZariskiOver.baseObj B S) : g = BigZariskiOver.toBaseObj B S Y :=
  Over.OverMorphism.ext ((Category.comp_id g.left).symm.trans (Over.w g))

/-- Composing with a structure morphism to the base gives the structure morphism to the
base. -/
public theorem BigZariskiOver.comp_toBaseObj {Y Z : BigZariskiOver B S.obj S.property}
    (f : Y ⟶ Z) : f ≫ BigZariskiOver.toBaseObj B S Z = BigZariskiOver.toBaseObj B S Y :=
  BigZariskiOver.toBaseObj_eq B S _

/-- The fibre product `Y ×_S Z` of two objects of the big Zariski site over `S`, namely their
fibre product over the terminal object `AlgebraicGeometry.BigZariskiOver.baseObj`. -/
public def BigZariskiOver.baseProduct (Y Z : BigZariskiOver B S.obj S.property) :
    BigZariskiOver B S.obj S.property :=
  BigZariskiOver.pairProduct B S (BigZariskiOver.toBaseObj B S Y)
    (BigZariskiOver.toBaseObj B S Z)

/-- The first projection of `Y ×_S Z`. -/
public def BigZariskiOver.baseProductFst (Y Z : BigZariskiOver B S.obj S.property) :
    BigZariskiOver.baseProduct B S Y Z ⟶ Y :=
  BigZariskiOver.pairProductFst B S (BigZariskiOver.toBaseObj B S Y)
    (BigZariskiOver.toBaseObj B S Z)

/-- The second projection of `Y ×_S Z`. -/
public def BigZariskiOver.baseProductSnd (Y Z : BigZariskiOver B S.obj S.property) :
    BigZariskiOver.baseProduct B S Y Z ⟶ Z :=
  BigZariskiOver.pairProductSnd B S (BigZariskiOver.toBaseObj B S Y)
    (BigZariskiOver.toBaseObj B S Z)

/-- The morphism into `Y ×_S Z` determined by a pair of morphisms: no compatibility is needed,
because the base is terminal. -/
public def BigZariskiOver.baseProductLift {W Y Z : BigZariskiOver B S.obj S.property}
    (a : W ⟶ Y) (b : W ⟶ Z) : W ⟶ BigZariskiOver.baseProduct B S Y Z :=
  BigZariskiOver.pairLift B S _ _ a b
    ((BigZariskiOver.comp_toBaseObj B S a).trans (BigZariskiOver.comp_toBaseObj B S b).symm)

/-- The lift into `Y ×_S Z` recovers its first component. -/
public theorem BigZariskiOver.baseProductLift_fst {W Y Z : BigZariskiOver B S.obj S.property}
    (a : W ⟶ Y) (b : W ⟶ Z) :
    BigZariskiOver.baseProductLift B S a b ≫ BigZariskiOver.baseProductFst B S Y Z = a :=
  BigZariskiOver.pairLift_fst B S _ _ a b _

/-- The lift into `Y ×_S Z` recovers its second component. -/
public theorem BigZariskiOver.baseProductLift_snd {W Y Z : BigZariskiOver B S.obj S.property}
    (a : W ⟶ Y) (b : W ⟶ Z) :
    BigZariskiOver.baseProductLift B S a b ≫ BigZariskiOver.baseProductSnd B S Y Z = b :=
  BigZariskiOver.pairLift_snd B S _ _ a b _

/-- **Base change of an open structure morphism.** If `Y` is open in `S` then the second
projection `Y ×_S Z ⟶ Z` is an open immersion, being the base change of the structure morphism
of `Y` along the structure morphism of `Z`. -/
public theorem BigZariskiOver.isOpenImmersion_baseProductSnd_left
    (Y Z : BigZariskiOver B S.obj S.property)
    (hY : IsOpenImmersion (B.inclusion.map Y.hom)) :
    IsOpenImmersion (B.inclusion.map (BigZariskiOver.baseProductSnd B S Y Z).left) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback Y.hom Z.hom).map B.inclusion) hY

/-- The inclusion of an open subscheme of an object of the big Zariski site over `S` is an open
immersion. -/
public theorem BigZariskiOver.isOpenImmersion_openObjι_left
    {X : BigZariskiOver B S.obj S.property} (V : (B.inclusion.obj X.left).Opens) :
    IsOpenImmersion (B.inclusion.map (BigZariskiOver.openObjι B S V).left) :=
  (inferInstance : IsOpenImmersion V.ι)

/-- **An fpqc covering stays an fpqc covering after base change.** The family of first
projections of the fibre products `W ×_X Z i` is an fpqc covering of `W` as soon as
`{Z i ⟶ X}` is an fpqc covering of `X`. -/
public theorem BigZariskiOver.pairProductFst_mem_fpqcPrecoverage_comap
    {X : BigZariskiOver B S.obj S.property} {I : Type*}
    (Z : I → BigZariskiOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X)
    {W : BigZariskiOver B S.obj S.property} (q : W ⟶ X) :
    Presieve.ofArrows (fun i => BigZariskiOver.pairProduct B S q (p i))
        (fun i => BigZariskiOver.pairProductFst B S q (p i)) ∈
      Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) W := by
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hp ⊢
  exact Precoverage.mem_coverings_of_isPullback _ hp _ _
    (fun i => (BigZariskiOver.toScheme B S.obj S.property).map
      (BigZariskiOver.pairProductSnd B S q (p i)))
    fun i => (IsPullback.of_hasPullback q.left (p i).left).map B.inclusion

end Geometry

/-! ### The Zariski refinement step -/

section Refinement

variable (B : BigZariskiSite.{u}) (S : B.Schemes)
  (F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)))

/-- The section of `π_S⁻¹F` over an open subscheme `U` of `S` attached to a section of `F` over
`U` by the adjunction unit of the projection `π_S`. -/
public def zariskiUnitSection (U : SmallZariski B S.obj S.property) (t : F.obj.obj (op U)) :
    (zariskiInverseImagePresheaf B S F).obj
      (op ((SmallZariski.inclusion B S.obj S.property).obj U)) :=
  Functor.unitSection (SmallZariski.inclusion B S.obj S.property)
    (SmallZariski.topology B S.obj S.property) (BigZariskiOver.topology B S.obj S.property)
    (smallZariskiProjection B S).adj F U t

/-- Restricted along a big Zariski covering sieve, a section of `π_S⁻¹F` is the restriction of a
section coming from the small Zariski site of `S`.

This is `AlgebraicGeometry.exists_locally_unit_section_smallZariski` with the unit section named
by `AlgebraicGeometry.zariskiUnitSection`. -/
public theorem exists_locally_zariskiUnitSection (X : BigZariskiOver B S.obj S.property)
    (s : (zariskiInverseImagePresheaf B S F).obj (op X)) :
    ∃ R : Sieve X, R ∈ BigZariskiOver.topology B S.obj S.property X ∧
      ∀ ⦃Y : BigZariskiOver B S.obj S.property⦄ (k : Y ⟶ X), R k →
        ∃ (U : SmallZariski B S.obj S.property)
          (h : Y ⟶ (SmallZariski.inclusion B S.obj S.property).obj U) (t : F.obj.obj (op U)),
          (zariskiInverseImagePresheaf B S F).map k.op s =
            (zariskiInverseImagePresheaf B S F).map h.op (zariskiUnitSection B S F U t) :=
  exists_locally_unit_section_smallZariski B S F X s

/-- Restricting a compatible family along the second projections of the fibre products
`W ×_X Z i` gives a family compatible along the first projections. -/
public theorem compatible_map_pairProductSnd {X : BigZariskiOver B S.obj S.property} {I : Type*}
    (Z : I → BigZariskiOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (x : ∀ i, (zariskiInverseImagePresheaf B S F).obj (op (Z i)))
    (hx : Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) p x)
    {W : BigZariskiOver B S.obj S.property} (q : W ⟶ X) :
    Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F)
      (fun i => BigZariskiOver.pairProductFst B S q (p i))
      (fun i => (zariskiInverseImagePresheaf B S F).map
        (BigZariskiOver.pairProductSnd B S q (p i)).op (x i)) := by
  intro j₁ j₂ T g₁ g₂ hg
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine hx j₁ j₂ T _ _ ?_
  rw [Category.assoc, Category.assoc, ← BigZariskiOver.pairProduct_condition,
    ← BigZariskiOver.pairProduct_condition, ← Category.assoc, ← Category.assoc, hg]

/-- A lift into `V ×_X Z` lies in the locus where the pullbacks of `z` and `t` agree exactly when
the two components of the lift carry `t` and `z` to the same section. -/
private theorem forall_mem_eqLocus_pairLift_iff
    {X V Z Y : BigZariskiOver B S.obj S.property} (q : V ⟶ X) (r : Z ⟶ X)
    (z : (zariskiInverseImagePresheaf B S F).obj (op Z))
    (t : (zariskiInverseImagePresheaf B S F).obj (op V))
    (a : Y ⟶ V) (k : Y ⟶ Z) (haq : a ≫ q = k ≫ r) :
    (∀ y, B.inclusion.map (BigZariskiOver.pairLift B S q r a k haq).left y ∈
      zariskiInverseImageEqLocus B S F (BigZariskiOver.pairProduct B S q r)
        ((zariskiInverseImagePresheaf B S F).map (BigZariskiOver.pairProductSnd B S q r).op z)
        ((zariskiInverseImagePresheaf B S F).map
          (BigZariskiOver.pairProductFst B S q r).op t)) ↔
      (zariskiInverseImagePresheaf B S F).map a.op t =
        (zariskiInverseImagePresheaf B S F).map k.op z :=
  (forall_mem_zariskiInverseImageEqLocus_iff B S F _ _
    (BigZariskiOver.pairLift B S q r a k haq)).trans
    (by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
        BigZariskiOver.pairLift_fst, BigZariskiOver.pairLift_snd]
      exact eq_comm)

/-- If the preimage of an open `W` of `V` in `V ×_X Z` is the locus where a section `t` over `V`
and a section `z` over `Z` agree, then `t` restricted to `W` agrees with `z` on `W ×_X Z`. -/
public theorem map_pairProductFst_openObjι_eq_of_preimage_eq
    {X V Z : BigZariskiOver B S.obj S.property} (q : V ⟶ X) (r : Z ⟶ X)
    (z : (zariskiInverseImagePresheaf B S F).obj (op Z))
    (t : (zariskiInverseImagePresheaf B S F).obj (op V)) (W : (B.inclusion.obj V.left).Opens)
    (hW : B.inclusion.map (BigZariskiOver.pairProductFst B S q r).left ⁻¹ᵁ W =
      zariskiInverseImageEqLocus B S F (BigZariskiOver.pairProduct B S q r)
        ((zariskiInverseImagePresheaf B S F).map (BigZariskiOver.pairProductSnd B S q r).op z)
        ((zariskiInverseImagePresheaf B S F).map (BigZariskiOver.pairProductFst B S q r).op t)) :
    (zariskiInverseImagePresheaf B S F).map
        (BigZariskiOver.pairProductFst B S (BigZariskiOver.openObjι B S W ≫ q) r).op
        ((zariskiInverseImagePresheaf B S F).map (BigZariskiOver.openObjι B S W).op t) =
      (zariskiInverseImagePresheaf B S F).map
        (BigZariskiOver.pairProductSnd B S (BigZariskiOver.openObjι B S W ≫ q) r).op z := by
  have hcond : (BigZariskiOver.pairProductFst B S (BigZariskiOver.openObjι B S W ≫ q) r ≫
        BigZariskiOver.openObjι B S W) ≫ q =
      BigZariskiOver.pairProductSnd B S (BigZariskiOver.openObjι B S W ≫ q) r ≫ r :=
    (Category.assoc _ _ _).trans
      (BigZariskiOver.pairProduct_condition B S (BigZariskiOver.openObjι B S W ≫ q) r)
  have hmem : ∀ y, B.inclusion.map (BigZariskiOver.pairLift B S q r _ _ hcond).left y ∈
      zariskiInverseImageEqLocus B S F (BigZariskiOver.pairProduct B S q r)
        ((zariskiInverseImagePresheaf B S F).map (BigZariskiOver.pairProductSnd B S q r).op z)
        ((zariskiInverseImagePresheaf B S F).map
          (BigZariskiOver.pairProductFst B S q r).op t) := by
    intro y
    rw [← hW, Scheme.Hom.mem_preimage, ← BigZariskiOver.inclusion_map_comp_apply,
      BigZariskiOver.pairLift_fst, BigZariskiOver.inclusion_map_comp_apply,
      BigZariskiOver.openObjι_apply]
    exact (_ : (B.inclusion.obj (BigZariskiOver.openObj B S W).left)).property
  have hagree := (forall_mem_eqLocus_pairLift_iff B S F q r z t _ _ hcond).mp hmem
  rwa [op_comp, Functor.map_comp_apply] at hagree

/-- If the preimage of an open `W` of `V` in `V ×_X Z` is the locus where a section `t` over `V`
and a section `z` over `Z` agree, then every `Y` mapping to `V` and `Z` compatibly with both
sections has its image in `X` inside the image of `W`. -/
public theorem mem_range_openObjι_comp_of_preimage_eq
    {X V Z Y : BigZariskiOver B S.obj S.property} (q : V ⟶ X) (r : Z ⟶ X)
    (z : (zariskiInverseImagePresheaf B S F).obj (op Z))
    (t : (zariskiInverseImagePresheaf B S F).obj (op V)) (W : (B.inclusion.obj V.left).Opens)
    (hW : B.inclusion.map (BigZariskiOver.pairProductFst B S q r).left ⁻¹ᵁ W =
      zariskiInverseImageEqLocus B S F (BigZariskiOver.pairProduct B S q r)
        ((zariskiInverseImagePresheaf B S F).map (BigZariskiOver.pairProductSnd B S q r).op z)
        ((zariskiInverseImagePresheaf B S F).map (BigZariskiOver.pairProductFst B S q r).op t))
    (a : Y ⟶ V) (k : Y ⟶ Z) (haq : a ≫ q = k ≫ r)
    (hkey : (zariskiInverseImagePresheaf B S F).map a.op t =
      (zariskiInverseImagePresheaf B S F).map k.op z)
    (w : B.inclusion.obj Y.left) :
    B.inclusion.map (k ≫ r).left w ∈
      Set.range (B.inclusion.map (BigZariskiOver.openObjι B S W ≫ q).left) := by
  have hmem := (forall_mem_eqLocus_pairLift_iff B S F q r z t a k haq).mpr hkey w
  rw [← hW, Scheme.Hom.mem_preimage, ← BigZariskiOver.inclusion_map_comp_apply,
    BigZariskiOver.pairLift_fst] at hmem
  refine ⟨⟨B.inclusion.map a.left w, hmem⟩,
    (BigZariskiOver.inclusion_map_comp_apply B S (BigZariskiOver.openObjι B S W) q
      ⟨B.inclusion.map a.left w, hmem⟩).trans ?_⟩
  exact (BigZariskiOver.inclusion_map_comp_apply B S a q w).symm.trans
    (congrArg (fun m : Y ⟶ X => B.inclusion.map m.left w) haq)

/-- **One member of the Zariski refinement.** Suppose a section `x i` of `π_S⁻¹F` over a member
`Z i` of an fpqc covering of `X` becomes, after restriction along `k : Y ⟶ Z i`, the restriction
along `h : Y ⟶ U` of a section coming from an open subscheme `U` of `S`. Then there is an object
`V` of the big Zariski site over `S`, an *open immersion* `v : V ⟶ X` whose image contains the
image of `Y`, and a section `s` of `π_S⁻¹F` over `V` agreeing with every member `x j` of the
family on `V ×_X Z j`.

`V` is an open subscheme of `U ×_S X`: the section coming from `U` and the family `x j` agree on
an open of `(U ×_S X) ×_X Z j` by Stacks 09XM, these opens descend along the fpqc covering to an
open `V` of `U ×_S X` by Stacks 03N0
(`AlgebraicGeometry.existsUnique_preimage_eq_zariskiInverseImageEqLocus`), and the image of `Y`
lies in `V` because `Y` maps to `(U ×_S X) ×_X Z i` compatibly with both sections. -/
public theorem exists_zariski_refinement_member {X : BigZariskiOver B S.obj S.property}
    {I : Type (u + 1)} (Z : I → BigZariskiOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X)
    (x : ∀ i, (zariskiInverseImagePresheaf B S F).obj (op (Z i)))
    (hx : Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) p x)
    {Y : BigZariskiOver B S.obj S.property} {i : I} (k : Y ⟶ Z i)
    (U : SmallZariski B S.obj S.property)
    (h : Y ⟶ (SmallZariski.inclusion B S.obj S.property).obj U) (t : F.obj.obj (op U))
    (hkt : (zariskiInverseImagePresheaf B S F).map k.op (x i) =
      (zariskiInverseImagePresheaf B S F).map h.op (zariskiUnitSection B S F U t)) :
    ∃ (V : BigZariskiOver B S.obj S.property) (v : V ⟶ X)
      (s : (zariskiInverseImagePresheaf B S F).obj (op V)),
      IsOpenImmersion (B.inclusion.map v.left) ∧
        (∀ w : B.inclusion.obj Y.left,
          B.inclusion.map (k ≫ p i).left w ∈ Set.range (B.inclusion.map v.left)) ∧
        ∀ j, (zariskiInverseImagePresheaf B S F).map
              (BigZariskiOver.pairProductFst B S v (p j)).op s =
          (zariskiInverseImagePresheaf B S F).map
            (BigZariskiOver.pairProductSnd B S v (p j)).op (x j) := by
  -- The candidate `U ×_S X`, its projection to `X`, and the section it carries.
  set VF := BigZariskiOver.baseProduct B S
    ((SmallZariski.inclusion B S.obj S.property).obj U) X
  set qF := BigZariskiOver.baseProductSnd B S
    ((SmallZariski.inclusion B S.obj S.property).obj U) X
  set tF := (zariskiInverseImagePresheaf B S F).map
    (BigZariskiOver.baseProductFst B S
      ((SmallZariski.inclusion B S.obj S.property).obj U) X).op
    (zariskiUnitSection B S F U t) with htF
  -- `Y` maps to the candidate, and the candidate's section agrees there with `x i`.
  set a := BigZariskiOver.baseProductLift B S h (k ≫ p i)
  have haq : a ≫ qF = k ≫ p i := BigZariskiOver.baseProductLift_snd B S h (k ≫ p i)
  have hkey : (zariskiInverseImagePresheaf B S F).map a.op tF =
      (zariskiInverseImagePresheaf B S F).map k.op (x i) := by
    rw [htF, ← Functor.map_comp_apply, ← op_comp,
      BigZariskiOver.baseProductLift_fst B S h (k ≫ p i), hkt]
  -- The base change of the fpqc covering to the candidate, and the restricted family.
  have hpF : Presieve.ofArrows (fun j => BigZariskiOver.pairProduct B S qF (p j))
      (fun j => BigZariskiOver.pairProductFst B S qF (p j)) ∈
      Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) VF :=
    BigZariskiOver.pairProductFst_mem_fpqcPrecoverage_comap B S Z p hp qF
  -- Stacks 03N0 descends the equality loci to an open of the candidate.
  obtain ⟨W, hW, -⟩ := existsUnique_preimage_eq_zariskiInverseImageEqLocus B S F
    (fun j => BigZariskiOver.pairProduct B S qF (p j))
    (fun j => BigZariskiOver.pairProductFst B S qF (p j)) hpF
    (fun j => (zariskiInverseImagePresheaf B S F).map
      (BigZariskiOver.pairProductSnd B S qF (p j)).op (x j))
    (compatible_map_pairProductSnd B S F Z p x hx qF) tF
  refine ⟨BigZariskiOver.openObj B S W, BigZariskiOver.openObjι B S W ≫ qF,
    (zariskiInverseImagePresheaf B S F).map (BigZariskiOver.openObjι B S W).op tF, ?_, ?_, ?_⟩
  · -- The member is open in `X`: an open immersion followed by a base change of `U ⟶ S`.
    have h₁ : IsOpenImmersion (B.inclusion.map (BigZariskiOver.openObjι B S W).left) :=
      BigZariskiOver.isOpenImmersion_openObjι_left B S W
    have h₂ : IsOpenImmersion (B.inclusion.map qF.left) :=
      BigZariskiOver.isOpenImmersion_baseProductSnd_left B S _ X U.property
    rw [show (BigZariskiOver.openObjι B S W ≫ qF).left =
      (BigZariskiOver.openObjι B S W).left ≫ qF.left from rfl, B.inclusion.map_comp]
    infer_instance
  · -- The image of `Y` lies in the member.
    exact mem_range_openObjι_comp_of_preimage_eq B S F qF (p i) (x i) tF W (hW i) a k haq hkey
  · -- The member's section agrees with the whole family.
    exact fun j =>
      map_pairProductFst_openObjι_eq_of_preimage_eq B S F qF (p j) (x j) tF W (hW j)

/-- **Stacks 09XN, the Zariski refinement step.** Every compatible family of sections of
`π_S⁻¹F` on an fpqc covering `{p i : Z i ⟶ X}` is *locally represented*: there are a family
`{v k : V k ⟶ X}` generating a covering sieve of the big Zariski topology and jointly surjective
on points, and sections `t k` of `π_S⁻¹F` over `V k`, such that `t k` agrees with every `x i` on
the fibre product `V k ×_X Z i`.

The members are produced one at a time by
`AlgebraicGeometry.exists_zariski_refinement_member`, indexed by the arrows of the big Zariski
covering sieves along which the sections `x i` come from the small Zariski site of `S`
(`AlgebraicGeometry.exists_locally_zariskiUnitSection`). Joint surjectivity holds because an
fpqc covering is jointly surjective and so is each of those covering sieves
(`AlgebraicGeometry.BigZariskiOver.exists_mem_arrows_mem_range`), and each member's image
contains the image of the arrow it was built from; openness of the members then makes the family
a big Zariski covering by
`AlgebraicGeometry.BigZariskiOver.generate_ofArrows_mem_topology`. -/
public theorem exists_locally_represented_of_mem_fpqcPrecoverage_zariski
    (X : BigZariskiOver B S.obj S.property) (I : Type (u + 1))
    (Z : I → BigZariskiOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X)
    (x : ∀ i, (zariskiInverseImagePresheaf B S F).obj (op (Z i)))
    (hx : Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) p x) :
    ∃ (K : Type (u + 1)) (V : K → BigZariskiOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
      (t : ∀ k, (zariskiInverseImagePresheaf B S F).obj (op (V k))),
      Sieve.generate (Presieve.ofArrows V v) ∈
          BigZariskiOver.topology B S.obj S.property X ∧
        (∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left)) ∧
        ∀ k i, (zariskiInverseImagePresheaf B S F).map
              (BigZariskiOver.pairProductFst B S (v k) (p i)).op (t k) =
          (zariskiInverseImagePresheaf B S F).map
            (BigZariskiOver.pairProductSnd B S (v k) (p i)).op (x i) := by
  classical
  -- Each `x i` comes from the small Zariski site of `S` along a big Zariski covering sieve.
  choose R hRmem hRdata using fun i => exists_locally_zariskiUnitSection B S F (Z i) (x i)
  -- One member of the refinement for each arrow of each of those sieves.
  choose U hU t hUt using fun κ : Σ (i : I) (Y : BigZariskiOver B S.obj S.property),
    {k : Y ⟶ Z i // (R i).arrows k} => hRdata κ.1 κ.2.2.1 κ.2.2.2
  choose V v s hopen hrange hagree using fun κ : Σ (i : I)
    (Y : BigZariskiOver B S.obj S.property), {k : Y ⟶ Z i // (R i).arrows k} =>
    exists_zariski_refinement_member B S F Z p hp x hx κ.2.2.1 (U κ) (hU κ) (t κ) (hUt κ)
  -- The members are jointly surjective: the fpqc covering and the sieves are.
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hp
  have hsurj : ∀ y : B.inclusion.obj X.left,
      ∃ κ, y ∈ Set.range (B.inclusion.map (v κ).left) := by
    intro y
    obtain ⟨i, z, hz⟩ := fpqc_jointly_surjective _ hp y
    obtain ⟨Y, k, hk, w, hw⟩ :=
      BigZariskiOver.exists_mem_arrows_mem_range B S.obj S.property (hRmem i) z
    obtain ⟨y', hy'⟩ := hrange ⟨i, Y, ⟨k, hk⟩⟩ w
    refine ⟨⟨i, Y, ⟨k, hk⟩⟩, y', hy'.trans ?_⟩
    rwa [BigZariskiOver.inclusion_map_comp_apply, hw]
  exact ⟨_, V, v, s,
    BigZariskiOver.generate_ofArrows_mem_topology B S.obj S.property V v hopen hsurj,
    hsurj, hagree⟩

end Refinement

/-! ### The fpqc sheaf condition -/

/-- **Stacks 09XN, the fpqc sheaf condition (Zariski case).** Let `S` be a scheme in a big
Zariski site `B`, let `F` be a sheaf of sets on the small Zariski site of `S` and let `π_S` be
the projection from the big Zariski topos over `S` to the small Zariski topos of `S`. Then the
presheaf underlying `π_S⁻¹F` — by the sections formula, `X ↦ Γ(X_Zar, f_X⁻¹F)` — is a sheaf for
the fpqc topology on the big Zariski site over `S`.

The uniqueness half is
`AlgebraicGeometry.smallZariskiProjection_inverseImage_isSeparatedFor_fpqc` and the existence
half is `AlgebraicGeometry.exists_isAmalgamation_of_locallyRepresentable_zariski`, whose local
representability hypothesis is the Zariski refinement step
`AlgebraicGeometry.exists_locally_represented_of_mem_fpqcPrecoverage_zariski`.

This is the second of the two conclusions of Tag 09XN, at the Zariski value of `τ`. The whole
tag — both conclusions, at both values of `τ` — is
`AlgebraicGeometry.smallSiteInverseImage_sections_and_isSheaf_fpqc`, which carries the tag. -/
public theorem smallZariskiProjection_inverseImage_isSheaf_fpqc (B : BigZariskiSite.{u})
    (S : B.Schemes) (F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1))) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap
        (BigZariskiOver.toScheme B S.obj S.property)).toGrothendieck)
      ((smallZariskiProjection B S).inverseImage.obj F).obj :=
  smallZariskiProjection_inverseImage_isSheaf_fpqc_of_locallyRepresentable B S F
    fun X I Z p hp y hy =>
      exists_locally_represented_of_mem_fpqcPrecoverage_zariski B S F X I Z p hp y hy

end AlgebraicGeometry

end
