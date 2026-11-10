module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimitGlobal
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.SectionsOverAnObjectOfColimitOfFiniteSites

/-! # A finite one-hypercover of a quasi-compact quasi-separated etale object by affine opens

The Cech step of [Stacks, Tag 09YQ] over a quasi-compact *separated* etale object `V` of a level
needs the sections of a sheaf over `V` described as matching families on a finite family of
*affine* objects, `V` itself not being an object of the small affine etale site unless it is
affine. `Stacks.WeakSites.ColimitGlobalSections.IsOneHypercoverOf` is that description on the side
of sites; this file supplies the geometry for it.

The datum is the one the absolute case uses: finitely many affine opens covering `V`, together
with finitely many affine opens covering each pairwise overlap, which
`Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens` produces for any
quasi-compact quasi-separated scheme and in particular for a `V` quasi-compact and separated over
a quasi-compact quasi-separated base. What is new is that the family lives in the small etale site
of the base and covers the *object* `V` there rather than the terminal sheaf.

## Main definitions

* `etaleObjOfAffineOpen`: an affine open of an object of the small etale site of `S` is again an
  object of it, and an affine one. This is
  `Stacks.EtaleCohomology.QcqsLimitCohomology.objOfAffineOpenOver` read in the small etale site.
* `etaleObjToAmbient`, `etaleObjLe`, `etaleObjResLE`: the three morphisms of the datum -- the
  open immersion into the ambient object, the inclusion of one affine open of it in another, and
  the restriction of a morphism of the site to affine opens of source and target.

The two identities `etaleObjLe_comp_toAmbient` and `etaleObjResLE_comp_toAmbient` between them,
and the monomorphism instance `mono_etaleObjToAmbient`, are stated at the level of the SITE rather
than of schemes, and the implementation notes say why.

## Main results

* `isOneHypercoverOf_etaleObjOfAffineOpen`: **the datum is a one-hypercover of `V`.** A family of
  affine opens covering `V`, together with affine opens covering each pairwise overlap, is a
  finite one-hypercover of `V` in the small etale site of `S`.

## Implementation notes

The covering clause is `Stacks.EtaleCohomology.ofArrows_mem_topology`: in the small etale site a
jointly surjective family is covering, with no cardinality side condition to discharge -- unlike
the small *affine* etale site, where the bound `#I₀ ≤ B.coveringBound` is dischargeable only
through `AlgebraicGeometry.mem_smallAffineEtale_precoverage_iff` and only for an affine target.

The factorisation clause needs a covering of an arbitrary object `Z` of the site subordinate to
the opens covering the overlap, and it takes that covering by *affine* opens of `Z` indexed by the
points of `Z` -- the same device as
`Stacks.EtaleCohomology.QcqsLimitCohomology.exists_presieve_subordinate`, here cheaper because the
small etale site needs no finiteness. The two factorisation equations are then discharged by the
same fact as in the absolute case: the structure morphism of the object of an affine open is an
open immersion, hence a monomorphism, so two morphisms into it which agree over `V` agree.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.EtaleCohomology.QcSeparatedSections

open AlgebraicGeometry Stacks.EtaleCohomology.AffineLimitCohomology
open Stacks.EtaleCohomology.QcqsLimitCohomology
open Stacks.WeakSites.ColimitGlobalSections

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine open of an object of the small etale site of `S` is an object of it.** The
structure morphism is the open immersion followed by that of the ambient object; this is
`Stacks.EtaleCohomology.QcqsLimitCohomology.objOfAffineOpenOver`, whose ambient datum is a bare
etale morphism, read at the structure morphism of `Z` and placed back in the small etale site. -/
def etaleObjOfAffineOpen (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) : AlgebraicGeometry.SmallEtale B S hS :=
  (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).obj
    (objOfAffineOpenOver B S hS (contains_toScheme_obj B hS Z)
      (B.inclusion.map Z.obj.hom) O hO)

/-- The underlying scheme of the object of an affine open is that open. -/
@[simp]
theorem toScheme_etaleObjOfAffineOpen (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) :
    (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj (etaleObjOfAffineOpen B S hS Z O hO) =
      O.toScheme :=
  rfl

/-- The structure morphism of the object of an affine open of `Z` is the open immersion followed
by the structure morphism of `Z`. -/
theorem hom_etaleObjOfAffineOpen (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) :
    B.inclusion.map (etaleObjOfAffineOpen B S hS Z O hO).obj.hom =
      O.ι ≫ B.inclusion.map Z.obj.hom :=
  structMap_objOfAffineOpenOver B S hS (contains_toScheme_obj B hS Z)
    (B.inclusion.map Z.obj.hom) O hO

/-- The open immersion of an affine open of `Z` into `Z`, as a morphism of the small etale
site. -/
def etaleObjToAmbient (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) : etaleObjOfAffineOpen B S hS Z O hO ⟶ Z :=
  mkHom B hS O.ι (hom_etaleObjOfAffineOpen B S hS Z O hO).symm

/-- On underlying schemes, `etaleObjToAmbient` is the open immersion `O.ι`. -/
@[simp]
theorem toScheme_map_etaleObjToAmbient (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) :
    (AlgebraicGeometry.SmallEtale.toScheme B S hS).map (etaleObjToAmbient B S hS Z O hO) = O.ι :=
  rfl

/-- The inclusion of one affine open of `Z` in another, as a morphism of the small etale site. -/
def etaleObjLe (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (e : O ≤ O') : etaleObjOfAffineOpen B S hS Z O hO ⟶ etaleObjOfAffineOpen B S hS Z O' hO' :=
  mkHom B hS (((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).homOfLE e) (by
    change ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).homOfLE e ≫
        (O'.ι ≫ B.inclusion.map Z.obj.hom) = O.ι ≫ B.inclusion.map Z.obj.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- On underlying schemes, `etaleObjLe` is the inclusion of opens `homOfLE e`. -/
@[simp]
theorem toScheme_map_etaleObjLe (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (e : O ≤ O') :
    (AlgebraicGeometry.SmallEtale.toScheme B S hS).map (etaleObjLe B S hS Z O O' hO hO' e) =
      ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).homOfLE e :=
  rfl

/-- **The restriction of a morphism of the site to affine opens of its source and target.** Given
`g : Z ⟶ W` and an affine open `O` of `Z` carried by `g` into an affine open `O'` of `W`, the
induced morphism of the objects of those opens. This is where
`AlgebraicGeometry.Scheme.Hom.resLE` does the work. -/
def etaleObjResLE {Z W : AlgebraicGeometry.SmallEtale B S hS} (g : Z ⟶ W)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O)
    (O' : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj W).Opens)
    (hO' : AlgebraicGeometry.IsAffineOpen O')
    (e : O ≤ ((AlgebraicGeometry.SmallEtale.toScheme B S hS).map g) ⁻¹ᵁ O') :
    etaleObjOfAffineOpen B S hS Z O hO ⟶ etaleObjOfAffineOpen B S hS W O' hO' :=
  mkHom B hS (((AlgebraicGeometry.SmallEtale.toScheme B S hS).map g).resLE O' O e) (by
    change ((AlgebraicGeometry.SmallEtale.toScheme B S hS).map g).resLE O' O e ≫
        (O'.ι ≫ B.inclusion.map W.obj.hom) = O.ι ≫ B.inclusion.map Z.obj.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Stacks.EtaleCohomology.toScheme_map_comp_hom])

/-- On underlying schemes, `etaleObjResLE` is the restriction `resLE` of the underlying morphism
of `g`. -/
@[simp]
theorem toScheme_map_etaleObjResLE {Z W : AlgebraicGeometry.SmallEtale B S hS} (g : Z ⟶ W)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O)
    (O' : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj W).Opens)
    (hO' : AlgebraicGeometry.IsAffineOpen O')
    (e : O ≤ ((AlgebraicGeometry.SmallEtale.toScheme B S hS).map g) ⁻¹ᵁ O') :
    (AlgebraicGeometry.SmallEtale.toScheme B S hS).map
      (etaleObjResLE B S hS g O hO O' hO' e) =
      ((AlgebraicGeometry.SmallEtale.toScheme B S hS).map g).resLE O' O e :=
  rfl

/-- **The inclusion of affine opens is compatible with the open immersions into the ambient
object.** A site-level equation, which is what makes the factorisation obligations of the
one-hypercover below provable by rewriting: at the level of schemes both sides are `O.ι` only
after unfolding the object of an affine open, and `rw` cannot abstract over that. -/
@[simp]
theorem etaleObjLe_comp_toAmbient (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (e : O ≤ O') :
    etaleObjLe B S hS Z O O' hO hO' e ≫ etaleObjToAmbient B S hS Z O' hO' =
      etaleObjToAmbient B S hS Z O hO :=
  Stacks.EtaleCohomology.hom_ext B hS
    (Scheme.homOfLE_ι ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z) e)

/-- **The restriction of a morphism to affine opens is compatible with the open immersions into
the ambient objects.** The site-level form of `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`. -/
@[simp]
theorem etaleObjResLE_comp_toAmbient {Z W : AlgebraicGeometry.SmallEtale B S hS} (g : Z ⟶ W)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O)
    (O' : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj W).Opens)
    (hO' : AlgebraicGeometry.IsAffineOpen O')
    (e : O ≤ ((AlgebraicGeometry.SmallEtale.toScheme B S hS).map g) ⁻¹ᵁ O') :
    etaleObjResLE B S hS g O hO O' hO' e ≫ etaleObjToAmbient B S hS W O' hO' =
      etaleObjToAmbient B S hS Z O hO ≫ g :=
  Stacks.EtaleCohomology.hom_ext B hS (Scheme.Hom.resLE_comp_ι _ _)

/-- The open immersion of an affine open into the ambient object is a monomorphism of the site:
it is one on underlying schemes, and `AlgebraicGeometry.SmallEtale.toScheme` is faithful. -/
instance mono_etaleObjToAmbient (Z : AlgebraicGeometry.SmallEtale B S hS)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) : Mono (etaleObjToAmbient B S hS Z O hO) :=
  (AlgebraicGeometry.SmallEtale.toScheme B S hS).mono_of_mono_map
    (show Mono O.ι from inferInstance)

/-- **A morphism of the site into the object of an affine open carries every point into that
open.** The relative form of
`Stacks.EtaleCohomology.QcqsLimitCohomology.base_mem_of_hom`: the morphism is one over `Z`, and
the structure morphism of the object of `O` is `O.ι`, whose range is `O`. -/
theorem base_mem_of_hom_etaleObj {Z : AlgebraicGeometry.SmallEtale B S hS}
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) {T : AlgebraicGeometry.SmallEtale B S hS}
    (t : T ⟶ etaleObjOfAffineOpen B S hS Z O hO)
    (x : (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj T) :
    ((AlgebraicGeometry.SmallEtale.toScheme B S hS).map
      (t ≫ etaleObjToAmbient B S hS Z O hO)).base x ∈ O := by
  have hr : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).map
      (t ≫ etaleObjToAmbient B S hS Z O hO)).base x ∈ Set.range (O.ι.base) := by
    rw [Functor.map_comp, toScheme_map_etaleObjToAmbient]
    exact ⟨_, rfl⟩
  rwa [show Set.range (O.ι.base) =
    (O : Set ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z)) from
      Scheme.Opens.range_ι O] at hr

/-! ### The one-hypercover of an object -/

section Datum

variable (V : AlgebraicGeometry.SmallEtale B S hS)
  {κ ν : Type u} (U : κ → ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V).Opens)
  (O : κ → κ → ν → ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V).Opens)
  (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k))
  (hOaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (O k l m))
  (hOle : ∀ k l m, O k l m ≤ U k ⊓ U l)

/-- **The affine opens of `V` and of its overlaps are a one-hypercover of the object `V`.** A
family of affine opens covering `V`, together with affine opens covering each pairwise overlap, is
a one-hypercover of `V` in the small etale site of `S` in the sense of
`Stacks.WeakSites.ColimitGlobalSections.IsOneHypercoverOf`; so for a sheaf of sets the sections
over `V` are the matching families on it
(`Stacks.WeakSites.ColimitGlobalSections.sectionOverEquivMatchingFamily`), and when the two index
types are finite that is a FINITE limit of sections over objects of the site.

This is the relative counterpart of
`Stacks.EtaleCohomology.QcqsLimitCohomology.isTopOneHypercover_hc`, and both the `hlev` and the
`hC` half of the Cech step over a quasi-compact separated etale object instantiate it -- at a
level and at the limit respectively, with `V` the transition image there.

The four pieces of the datum are written out as lambdas rather than named, which is the opposite
of the choice made for the absolute case in `hcObj`/`hcInter`/`hcFst`/`hcSnd`. The reason is
that named definitions here are opaque to `rw` inside the three obligations, so every step of
the three proofs has to unfold them again, and two of the four `Scheme.homOfLE_ι` rewrites fail
on type-correctness through them. Nothing is lost -- the absolute case needed names because
`hlev` speaks of the *transition images* of a chosen family, and the transition images are formed
from the lambdas just as well. -/
theorem isOneHypercoverOf_etaleObjOfAffineOpen
    (hUtop : (⨆ k, U k) = ⊤) (hOsup : ∀ k l, (⨆ m, O k l m) = U k ⊓ U l) :
    IsOneHypercoverOf (AlgebraicGeometry.SmallEtale.topology B S hS) V
      (fun k => etaleObjOfAffineOpen B S hS V (U k) (hUaff k))
      (fun k => etaleObjToAmbient B S hS V (U k) (hUaff k))
      (fun k l m => etaleObjOfAffineOpen B S hS V (O k l m) (hOaff k l m))
      (fun k l m => etaleObjLe B S hS V _ _ (hOaff k l m) (hUaff k)
        ((hOle k l m).trans inf_le_left))
      (fun k l m => etaleObjLe B S hS V _ _ (hOaff k l m) (hUaff l)
        ((hOle k l m).trans inf_le_right)) where
  covers := by
    refine Stacks.EtaleCohomology.ofArrows_mem_topology B hS _ _ fun x => ?_
    have hmem : x ∈ (⨆ k, U k :
        ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V).Opens) := by
      rw [hUtop]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    exact ⟨k, ⟨x, hk⟩, rfl⟩
  comm k l m := by
    simp only [etaleObjLe_comp_toAmbient]
  locally_factors Z k l g h hgh := by
    classical
    set zV := (AlgebraicGeometry.SmallEtale.toScheme B S hS).map
      (g ≫ etaleObjToAmbient B S hS V (U k) (hUaff k)) with hzV
    have hpt : ∀ x : (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z,
        ∃ (m : ν) (G : ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Z).Opens),
          AlgebraicGeometry.IsAffineOpen G ∧ x ∈ G ∧ G ≤ zV ⁻¹ᵁ (O k l m) := by
      intro x
      have hx : zV.base x ∈ U k ⊓ U l := by
        refine ⟨base_mem_of_hom_etaleObj B S hS (U k) (hUaff k) g x, ?_⟩
        have hl := base_mem_of_hom_etaleObj B S hS (U l) (hUaff l) h x
        rwa [← hgh] at hl
      rw [← hOsup k l] at hx
      obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      obtain ⟨-, ⟨G, hG, rfl⟩, hxG, hle⟩ :=
        ((AlgebraicGeometry.SmallEtale.toScheme B S
            hS).obj Z).isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ (zV ⁻¹ᵁ (O k l m) : _) from hm) (zV ⁻¹ᵁ (O k l m)).isOpen
      exact ⟨m, G, hG, hxG, hle⟩
    choose mm GG hGGaff hGGmem hGGle using hpt
    refine ⟨Sieve.ofArrows (fun x => etaleObjOfAffineOpen B S hS Z (GG x) (hGGaff x))
      (fun x => etaleObjToAmbient B S hS Z (GG x) (hGGaff x)), ?_, ?_⟩
    · refine Stacks.EtaleCohomology.ofArrows_mem_topology B hS _ _ fun x => ?_
      exact ⟨x, ⟨x, hGGmem x⟩, rfl⟩
    · rintro T q ⟨T', a, b, ⟨x⟩, rfl⟩
      refine ⟨mm x, a ≫ etaleObjResLE B S hS (g ≫ etaleObjToAmbient B S hS V (U k) (hUaff k))
        (GG x) (hGGaff x) (O k l (mm x)) (hOaff k l (mm x)) (hGGle x), ?_, ?_⟩
      · refine (cancel_mono (etaleObjToAmbient B S hS V (U k) (hUaff k))).1 ?_
        simp only [Category.assoc, etaleObjLe_comp_toAmbient, etaleObjResLE_comp_toAmbient]
      · refine (cancel_mono (etaleObjToAmbient B S hS V (U l) (hUaff l))).1 ?_
        simp only [Category.assoc, etaleObjLe_comp_toAmbient, etaleObjResLE_comp_toAmbient,
          ← hgh]

end Datum

end Stacks.EtaleCohomology.QcSeparatedSections

end
