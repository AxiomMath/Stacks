module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeIsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IsFibreSectionsGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsFiniteLocallyFree

/-!
# The relative morphism functor at an arbitrary representable target (Stacks 05Y6)

Let `S` be a scheme contained in a big fppf site, let `V`, `Z` and `X` be objects of the big
fppf site of `S` and let `z : Z ⟶ V` and `x : X ⟶ V` be morphisms of the site with the morphism
of schemes underlying `z` finite locally free. This file proves that the relative morphism
functor `Mor_{yoneda V}(yoneda Z, yoneda X)` of Stacks 05Y2 is an algebraic space over `S`, for
an **arbitrary** target `X` of the site.

`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_isAffineHom`
(`Spaces/RelativeHomSchemeComparison.lean`) proves this when the morphism of schemes underlying
`x` is affine, by transporting the scheme-side representability of Stacks 0BL3 across the
comparison of the two relative morphism functors. The restriction to an affine `x` is what the
source removes with its reduction to a target that is a disjoint union of affines, and that
reduction is what this file carries out. It takes two steps.

* The scheme-side representability is available at a target much more general than an affine one:
  Stacks 0BL4, `Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable`, needs only that every
  finite set of points of the target lying in one fibre be contained in an affine open of the
  target. A scheme which is a coproduct of affine schemes satisfies that condition —
  `AlgebraicGeometry.exists_isAffineOpen_superset_of_sigmaIso` below — with no reference to the
  fibre: a finite set of points meets finitely many summands, and a finite disjoint union of
  affine opens is an affine open.
* Every object of the site is covered, surjectively and étale, by an object of the site whose
  underlying scheme is a coproduct of affine schemes. That is Stacks 03FX, in the form
  `AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`, applied to the presheaf
  represented by the target. Algebraicity of the relative morphism functor then descends from the
  cover to the target by the reduction on the target in the proof of Stacks 05Y7,
  `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget`.

The second step consumes finite local freeness of `z` in the sense of Stacks 03ZV, because that
is what Stacks 05Y5 consumes, whereas the first consumes it in the sense of Section 03HA, for the
morphism of schemes. The two readings are reconciled by Stacks 03ZU, which the library does not
have; what it does have, unconditionally, is the rank form of the direction needed here,
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank`. That is
why the hypothesis below is finite local freeness of the morphism of schemes **of a rank** `d`:
the rank is what carries the Stacks 03HA reading into the Stacks 03ZV one.

## Main definitions

* `AlgebraicGeometry.Space.RelativeHomRepresentingContained`: the condition that the big fppf
  site of `S` contain the representing objects which Stacks 0BL4 produces for `z`.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_superset_of_sigmaIso`: a finite set of points of a
  scheme which is a coproduct of affine schemes lies in an affine open.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_finiteSubsets`: Stacks 05Y6 for
  algebraic spaces at a target whose finite sets of points lie in affine opens.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_isFiniteLocallyFreeOfRank`:
  the relative morphism functor of two morphisms of the site is an algebraic space over `S`, for
  an arbitrary target of the site, when the morphism of schemes underlying `z` is finite locally
  free of rank `d`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank`:
  the same, for an arbitrary morphism of presheaves between the represented target and the
  represented base.

## Implementation notes

`AlgebraicGeometry.Space.RelativeHomRepresentingContained` is asked of the objects of the site
whose finite sets of points lie in affine opens, which is exactly the class of targets at which
Stacks 0BL4 produces a representing object, so the condition is never vacuously about an object
Stacks 0BL4 says nothing of. It is a condition on the site, not on the morphisms being studied,
and it is proved in
`StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsSiteSize` as
`AlgebraicGeometry.Space.relativeHomRepresentingContained`; the statements of this file are kept
with it as a hypothesis because the proof of it needs the size machinery of
`StacksDraft.AlgebraicGeometry.Size`, which nothing else here does.

No `@[stacks]` attribute is placed here. The source's Stacks 05Y6 is stated over an affine base
and is already registered on the scheme side; what the main results of this file state is the
transport of its glued form Stacks 0BL3 and Stacks 0BL4 to the functor of Stacks 05Y2 over an
arbitrary base of the site, under a hypothesis on the site.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y5](https://stacks.math.columbia.edu/tag/05Y5)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
* [Stacks Project, Tag 05Y7](https://stacks.math.columbia.edu/tag/05Y7)
* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
* [Stacks Project, Tag 0BL3](https://stacks.math.columbia.edu/tag/0BL3)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A finite set of points of a scheme which is a coproduct of affine schemes lies in an affine
open.** The finite set meets finitely many summands, and the union of those is an affine open by
`AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint`, the summands of a coproduct of schemes being
pairwise disjoint open subschemes.

This is the hypothesis of Stacks 0BL4 on the target, in the form in which the reduction to a
target that is a disjoint union of affines supplies it; the fibre plays no part. -/
theorem exists_isAffineOpen_superset_of_sigmaIso {ι : Type u} (Y : ι → Scheme.{u})
    (hY : ∀ i, IsAffine (Y i)) {X : Scheme.{u}} (e : (∐ Y) ≅ X)
    {t : Set X} (ht : t.Finite) :
    ∃ O : X.Opens, IsAffineOpen O ∧ t ⊆ O := by
  classical
  have _ : ∀ i, IsAffine (Y i) := hY
  set idx : (∐ Y : Scheme.{u}) → ι := fun p => ((sigmaMk Y).symm p).1 with hidx
  have hmem : ∀ p : (∐ Y : Scheme.{u}), p ∈ (Sigma.ι Y (idx p)).opensRange := by
    intro p
    refine ⟨((sigmaMk Y).symm p).2, ?_⟩
    have h1 := sigmaMk_mk Y (idx p) ((sigmaMk Y).symm p).2
    have h0 : (sigmaMk Y) ((sigmaMk Y).symm p) = p := (sigmaMk Y).apply_symm_apply p
    exact h1.symm.trans h0
  set t' : Set (∐ Y : Scheme.{u}) := e.inv.base '' t with ht'
  have ht'fin : t'.Finite := ht.image _
  set F : Set ι := idx '' t' with hF
  have hFfin : F.Finite := ht'fin.image _
  have _ : Finite F := hFfin
  set O' : (∐ Y : Scheme.{u}).Opens := ⨆ i : F, (Sigma.ι Y (i : ι)).opensRange with hO'
  have hO'aff : IsAffineOpen O' :=
    IsAffineOpen.iSup_of_disjoint (fun i => isAffineOpen_opensRange (Sigma.ι Y (i : ι)))
      (fun i j hij =>
        disjoint_opensRange_sigmaι Y (i : ι) (j : ι) fun h => hij (Subtype.ext h))
  refine ⟨e.inv ⁻¹ᵁ O', hO'aff.preimage_of_isIso e.inv, ?_⟩
  intro w hw
  have h1 : e.inv.base w ∈ t' := ⟨w, hw, rfl⟩
  have h2 : idx (e.inv.base w) ∈ F := ⟨_, h1, rfl⟩
  show e.inv.base w ∈ O'
  rw [hO']
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, h2⟩, hmem _⟩

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {V Zs Xs : BigFppfOver B S hS}

/-- **The condition that the big fppf site of `S` contain the representing objects of the
relative morphism functors of Stacks 0BL2 attached to `z`.** For every object `X` of the site
over `V` whose finite sets of points lie in affine opens — the class of targets at which
Stacks 0BL4 produces a representing object — every object of the category of schemes over the
scheme underlying `V` which represents `Mor_V(Z, X)` has its underlying scheme in the site.

This is a condition on the site, asked of the objects the scheme-side representability theorem
produces something at. -/
def RelativeHomRepresentingContained (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V Zs : BigFppfOver B S hS} (z : Zs ⟶ V) : Prop :=
  ∀ (Xs : BigFppfOver B S hS) (x : Xs ⟶ V),
    (∀ t : Set ((BigFppfOver.toScheme B S hS).obj Xs), t.Finite →
      ∃ O : ((BigFppfOver.toScheme B S hS).obj Xs).Opens, IsAffineOpen O ∧ t ⊆ O) →
    ∀ W : Over ((BigFppfOver.toScheme B S hS).obj V),
      (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
          (Over.mk ((BigFppfOver.toScheme B S hS).map x))).RepresentableBy W →
        B.Contains W.left

/-- **Stacks 05Y6 for algebraic spaces, at a target whose finite sets of points lie in affine
opens.** For morphisms `z : Z ⟶ X` and `x : X ⟶ V` of the big fppf site of `S` with the morphism
of schemes underlying `z` finite locally free, the relative morphism functor
`Mor_{yoneda V}(yoneda Z, yoneda X)` of Stacks 05Y2 is an algebraic space over `S` as soon as
every finite set of points of the scheme underlying `X` lies in an affine open of it.

The scheme-side representability is Stacks 0BL4,
`Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable`, whose hypothesis on the target is
the one made here, with the fibre condition discarded; the passage to the functor of
Stacks 05Y2 is
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_representableBy`. -/
theorem isAlgebraicSpace_relativeHom_yoneda_of_finiteSubsets (z : Zs ⟶ V) (x : Xs ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z)]
    (hXaff : ∀ t : Set ((BigFppfOver.toScheme B S hS).obj Xs), t.Finite →
      ∃ O : ((BigFppfOver.toScheme B S hS).obj Xs).Opens, IsAffineOpen O ∧ t ⊆ O)
    (hsize : RelativeHomRepresentingContained B S hS z) :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs)
        (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V)) := by
  have hrep : (AlgebraicGeometry.relativeHom
      (Over.mk ((BigFppfOver.toScheme B S hS).map z))
      (Over.mk ((BigFppfOver.toScheme B S hS).map x))).IsRepresentable :=
    Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable
      ((BigFppfOver.toScheme B S hS).map z) ((BigFppfOver.toScheme B S hS).map x)
      (fun _ t ht _ => hXaff t ht)
  have e := (AlgebraicGeometry.relativeHom
    (Over.mk ((BigFppfOver.toScheme B S hS).map z))
    (Over.mk ((BigFppfOver.toScheme B S hS).map x))).representableBy
  exact isAlgebraicSpace_relativeHom_yoneda_of_representableBy z x _
    (hsize Xs x hXaff _ e) e

/-- **The relative morphism functor of Stacks 05Y2 at an arbitrary representable target.** For
morphisms `z : Z ⟶ V` and `x : X ⟶ V` of the big fppf site of `S` with the morphism of schemes
underlying `z` finite locally free of rank `d`, the relative morphism functor
`Mor_{yoneda V}(yoneda Z, yoneda X)` is an algebraic space over `S`.

The target is reduced to a coproduct of affine schemes by Stacks 03FX,
`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`, applied to the presheaf
represented by `X`; algebraicity descends from the cover by the reduction on the target in the
proof of Stacks 05Y7,
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget`, and holds on the
cover by `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_finiteSubsets` together
with `AlgebraicGeometry.exists_isAffineOpen_superset_of_sigmaIso`.

The rank is what reconciles the two readings of finite local freeness that the two steps consume:
the reduction on the target consumes the definition of Stacks 03ZV, which
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank` supplies
from the morphism of schemes at a fixed rank. -/
theorem isAlgebraicSpace_relativeHom_yoneda_of_isFiniteLocallyFreeOfRank (z : Zs ⟶ V)
    (x : Xs ⟶ V) (d : ℕ)
    [hzr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map z) d]
    (hsize : RelativeHomRepresentingContained B S hS z) :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs)
        (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V)) := by
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  have hpre : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map z) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance z hzr
  have hzsp : IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk (yoneda.map z) :
        (⟨yoneda.obj Zs, isAlgebraicSpace_yoneda B S hS Zs⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS)) :=
    (isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank B S hS _
        (Functor.relativelyRepresentable.map yoneda z) d hpre).isFiniteLocallyFree
  obtain ⟨U', f, I, Wf, -, e, hfsurj, hfetale, hWaff, -, -, -, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS (yoneda.obj Xs)
      (isAlgebraicSpace_yoneda B S hS Xs)
  have hXaff' : ∀ t : Set ((BigFppfOver.toScheme B S hS).obj U'), t.Finite →
      ∃ O : ((BigFppfOver.toScheme B S hS).obj U').Opens, IsAffineOpen O ∧ t ⊆ O :=
    fun t ht => exists_isAffineOpen_superset_of_sigmaIso
      (fun i => (BigFppfOver.toScheme B S hS).obj (Wf i)) hWaff e ht
  exact isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget
    (X' := (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS))
    (X := (⟨yoneda.obj Xs, isAlgebraicSpace_yoneda B S hS Xs⟩ : AlgebraicSpaces B S hS))
    (Z := (⟨yoneda.obj Zs, isAlgebraicSpace_yoneda B S hS Zs⟩ : AlgebraicSpaces B S hS))
    (Q := (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (x' := ObjectProperty.homMk (yoneda.map (yoneda.preimage f ≫ x)))
    (x := ObjectProperty.homMk (yoneda.map x))
    (z := ObjectProperty.homMk (yoneda.map z))
    (relativeHomData B S hS (yoneda.obj Zs) (yoneda.obj U') (yoneda.obj V) (yoneda.map z)
      (yoneda.map (yoneda.preimage f ≫ x)) (isAlgebraicSpace_yoneda B S hS Zs)
      (isAlgebraicSpace_yoneda B S hS U') (isAlgebraicSpace_yoneda B S hS V))
    (relativeHomData B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V) (yoneda.map z)
      (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs)
      (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V))
    (ObjectProperty.homMk (yoneda.map (yoneda.preimage f)))
    (yoneda.map_comp (yoneda.preimage f) x).symm
    (isEtale_of_presheaf_etale B S hS (by simpa using hfetale))
    (isSurjective_of_presheafSurjective B S hS _ (by simpa using hfsurj)) hzsp
    (isFibreSectionsAlgebraicEtale_of_isFinite _ _
      (isFinite_of_isFiniteLocallyFree B S hS _ hzsp))
    (isSheaf_relativeHom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V) (yoneda.map z)
      (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs) (isAlgebraicSpace_yoneda B S hS Xs)
      (isAlgebraicSpace_yoneda B S hS V))
    (isAlgebraicSpace_relativeHom_yoneda_of_finiteSubsets z (yoneda.preimage f ≫ x) hXaff'
      hsize)

/-- **The relative morphism functor of Stacks 05Y2 at an arbitrary representable target, for an
arbitrary morphism of presheaves into the represented base.** Yoneda is fully faithful, so a
morphism `yoneda X ⟶ yoneda V` of presheaves is the image of a morphism of the site and
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_isFiniteLocallyFreeOfRank`
applies. -/
theorem isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank (z : Zs ⟶ V)
    (u : yoneda.obj Xs ⟶ yoneda.obj V) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map z) d]
    (hsize : RelativeHomRepresentingContained B S hS z) :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) u (isAlgebraicSpace_yoneda B S hS Zs)
        (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V)) := by
  obtain ⟨x, rfl⟩ : ∃ x : Xs ⟶ V, yoneda.map x = u := ⟨yoneda.preimage u, yoneda.map_preimage u⟩
  exact isAlgebraicSpace_relativeHom_yoneda_of_isFiniteLocallyFreeOfRank z x d hsize

end Space

end AlgebraicGeometry

end
