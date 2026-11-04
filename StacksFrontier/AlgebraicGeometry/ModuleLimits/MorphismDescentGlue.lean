module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineFaithful
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentAgree
public import StacksFrontier.AlgebraicGeometry.Topologies.PullbackCoverGlueing

/-!
# Descent of a morphism of finitely presented modules through a cofiltered limit of
quasi-compact quasi-separated schemes

[Stacks Project, Tag 01ZR] (2) for a cofiltered diagram of quasi-compact quasi-separated schemes
is proved from the affine case by Zariski glueing, in three steps: a local descent over each
affine open of a stage, a common refinement of the local descents with agreement on the overlaps,
and the glueing itself.  The second step is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_descent_agree`, which takes the first as a
hypothesis.  This file proves that hypothesis unconditionally, performs the third step using the
Zariski glueing `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_cover`, and
assembles the clause.  Both statements are therefore unconditional, and they carry the clause
labels `"descend_morphisms"` for part (2), on `exists_map_of_pullback_of_isLimit`, and
`"descend_modules"` for part (1), on
`exists_isFinitePresentation_pullback_iso_of_qcqs`.  Part (3) is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit`, elsewhere.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.canMerge`: a morphism between iterated pullbacks, read
  as a morphism between pullbacks along the composite.
* `Stacks.AlgebraicGeometry.ModuleLimits.canSplit`: the inverse operation.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.canStep_eq_iff`: the canonical equation of
  [Stacks Project, Tag 01ZR] (2) says exactly that
  `Stacks.AlgebraicGeometry.ModuleLimits.canStep` of the descended morphism is the given one.
  This is the form in which every comparison below is made.
* `Stacks.AlgebraicGeometry.ModuleLimits.canStep_canMerge_of_canStep_eq_canSplit`: **the
  canonical equation descends along `canMerge`.**  For a chain of three morphisms, a morphism
  between the pullbacks along the middle one satisfying the canonical equation over the first is
  carried by `canMerge` to a morphism satisfying the canonical equation over the composite.
* `Stacks.AlgebraicGeometry.ModuleLimits.canSplit_canStep`: `canSplit` commutes with passing one
  step further.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isStageDescent_of_isAffineOpen`:
  **[Stacks Project, Tag 01ZR] (2) over an affine open of a stage**, in the form
  `Stacks.AlgebraicGeometry.ModuleLimits.IsStageDescent`, which is the hypothesis `hloc` of
  `exists_stage_descent_agree`.  This is unconditional.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_of_isLimit`:
  **[Stacks Project, Tag 01ZR] (2)** for quasi-compact quasi-separated stages, with the index
  morphism universe unrestricted and the canonical identifications written out.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs`:
  **[Stacks Project, Tag 01ZR] (1)** for quasi-compact quasi-separated stages.  This is the
  `hmap` hypothesis of
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_map`
  discharged, and it is the statement [Stacks Project, Tag 0ASY] calls.

## Implementation notes

The affine case
`Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine'` is
applied to the diagram `AlgebraicGeometry.EventualLimit.preimageDiagram D i W` of preimages of
the affine open `W` of the stage `D.obj i`, indexed by `CategoryTheory.Over i`, whose stages are
affine because `W` is and whose limit is the preimage of `W` in the vertex of the cone.  Its base
object is `CategoryTheory.Over.mk (𝟙 i)`, carrying the open `D.map (𝟙 i) ⁻¹ᵁ W` rather than `W`
itself; as elsewhere in this directory no isomorphism is transported to repair that, and the
argument is run with `D.map (𝟙 i) ⁻¹ᵁ W` throughout.

The two sheaves of modules on that base object are the pullbacks of `F` and `G` along
`Stacks.AlgebraicGeometry.ModuleLimits.preimageHom (D.map (𝟙 i)) W`, **not** along the inclusion
of the open.  Both are modules on the same scheme, and the two choices differ only by the factor
`D.map (𝟙 i) = 𝟙`, but only the first makes the transition morphism of the preimage diagram
compose with the structure morphism to the structure morphism one stage down
(`preimageRes_comp_preimageHom`), so with that choice the passage from the conclusion of the
affine case to `IsStageDescent` is formal: it is one instance of the cocycle condition
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`, packaged as
`canStep_canMerge_of_canStep_eq_canSplit`, and no `AlgebraicGeometry.Scheme.Hom.resLE` square and
no `Stacks.AlgebraicGeometry.ModuleLimits.sqIso` is needed.  With the inclusion of the open
instead, the same passage additionally has to cross the identification `D.map (𝟙 i) = 𝟙` on
morphisms and the identification of `sqIso` with `canStep` on the limit side, and neither is
formal.  That is why the affine case is applied here directly rather than through an intermediate
statement in the inclusion spelling.

The local descent and the glueing step are proved for `{I : Type u} [Category.{u} I]`, as is
`exists_stage_descent_agree` and for the same reason: the affine case is applied with index
category `CategoryTheory.Over i`, whose objects must then lie in the universe of the schemes.
Unlike for the local descent that restriction is removed for the glueing step, by passing to
`CategoryTheory.Functor.FullImage D`: the conclusion there mentions only `D` and the cone, and
not the objects of a diagram of preimages, which are only propositionally equal to their
counterparts over the full image.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Reading a morphism of iterated pullbacks as a morphism of pullbacks of a composite -/

section Conjugation

variable {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi) (mg : Zk ⟶ Zi)
  (hmg : m ≫ g = mg) {F G : Zi.Modules}

/-- A morphism between the pullbacks along `m` of the pullbacks along `g` of `F` and `G`, read
through the canonical comparison as a morphism between the pullbacks along the composite `mg`.
It is `Stacks.AlgebraicGeometry.ModuleLimits.canStep` with the pullback along `m` of a morphism
replaced by an arbitrary morphism between the same objects, and it is the operation that turns
the morphism produced by the affine case of [Stacks Project, Tag 01ZR] (2) into a morphism over
the preimage of an open of a stage. -/
noncomputable def canMerge
    (θ : (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj G)) :
    (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G :=
  (canIso m g mg hmg F).inv ≫ θ ≫ canHom m g mg hmg G

/-- The operation inverse to `Stacks.AlgebraicGeometry.ModuleLimits.canMerge`: a morphism between
the pullbacks along a composite `mg`, read through the canonical comparison as a morphism between
the iterated pullbacks.  It is how a morphism given over the preimage of an open of a stage is
handed to the affine case of [Stacks Project, Tag 01ZR] (2). -/
noncomputable def canSplit
    (Φ : (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G) :
    (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj G) :=
  canHom m g mg hmg F ≫ Φ ≫ (canIso m g mg hmg G).inv

/-- **The characterising property of `Stacks.AlgebraicGeometry.ModuleLimits.canSplit`.**  The
canonical comparison carries `canSplit` of a morphism to that morphism. -/
theorem canHom_comp_canSplit
    (Φ : (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G) :
    canSplit m g mg hmg Φ ≫ canHom m g mg hmg G = canHom m g mg hmg F ≫ Φ := by
  simp only [canSplit, Category.assoc, ← canIso_hom, Iso.inv_hom_id, Category.comp_id]

/-- `Stacks.AlgebraicGeometry.ModuleLimits.canMerge` undoes
`Stacks.AlgebraicGeometry.ModuleLimits.canSplit`. -/
theorem canMerge_canSplit
    (Φ : (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G) :
    canMerge m g mg hmg (canSplit m g mg hmg Φ) = Φ := by
  rw [canMerge, canHom_comp_canSplit, ← canIso_hom m g mg hmg F, Iso.inv_hom_id_assoc]

/-- **`canMerge` is an equation between canonical comparisons.**  That `canMerge` of a morphism
`θ` is `Φ` says exactly that the canonical comparison carries `θ` to `Φ`; this is the shape in
which the conclusion of [Stacks Project, Tag 01ZR] (2) is stated. -/
theorem canMerge_eq_iff
    (θ : (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj G))
    (Φ : (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G) :
    canMerge m g mg hmg θ = Φ ↔
      θ ≫ canHom m g mg hmg G = canHom m g mg hmg F ≫ Φ := by
  rw [canMerge, Iso.inv_comp_eq, canIso_hom]

/-- `Stacks.AlgebraicGeometry.ModuleLimits.canSplit` undoes
`Stacks.AlgebraicGeometry.ModuleLimits.canMerge`. -/
theorem canSplit_canMerge
    (θ : (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj G)) :
    canSplit m g mg hmg (canMerge m g mg hmg θ) = θ := by
  rw [← cancel_mono (canHom m g mg hmg G), canHom_comp_canSplit]
  exact ((canMerge_eq_iff m g mg hmg θ _).mp rfl).symm

/-- A morphism whose `canMerge` is `Φ` is `canSplit` of `Φ`. -/
theorem eq_canSplit_of_canMerge_eq
    (θ : (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj G))
    (Φ : (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G)
    (h : canMerge m g mg hmg θ = Φ) : θ = canSplit m g mg hmg Φ := by
  rw [← h, canSplit_canMerge]

/-- `Stacks.AlgebraicGeometry.ModuleLimits.canStep` is
`Stacks.AlgebraicGeometry.ModuleLimits.canMerge` of the pullback of the morphism. -/
theorem canStep_eq_canMerge
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G) :
    canStep m g mg hmg ψ = canMerge m g mg hmg ((Scheme.Modules.pullback m).map ψ) := rfl

/-- **The canonical equation of [Stacks Project, Tag 01ZR] (2), as an equation between
morphisms.**  That the canonical comparison carries the pullback of `ψ` along `m` to `Φ` says
exactly that `Stacks.AlgebraicGeometry.ModuleLimits.canStep` of `ψ` is `Φ`.  Every comparison
below is made in the right-hand form, which has no composites in it. -/
theorem canStep_eq_iff
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (Φ : (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G) :
    canStep m g mg hmg ψ = Φ ↔
      (Scheme.Modules.pullback m).map ψ ≫ canHom m g mg hmg G = canHom m g mg hmg F ≫ Φ := by
  rw [canStep_eq_canMerge, canMerge_eq_iff]

/-- Two morphisms with the same `Stacks.AlgebraicGeometry.ModuleLimits.canStep` have the same
pullback. -/
theorem pullback_map_eq_of_canStep_eq
    {ψ ψ' : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G}
    (h : canStep m g mg hmg ψ = canStep m g mg hmg ψ') :
    (Scheme.Modules.pullback m).map ψ = (Scheme.Modules.pullback m).map ψ' := by
  have key := congrArg (canSplit m g mg hmg) h
  rwa [canStep_eq_canMerge, canStep_eq_canMerge, canSplit_canMerge, canSplit_canMerge] at key

end Conjugation

/-! ### The canonical equation along a chain of three morphisms -/

section Chain

variable {A C B X : Scheme.{u}} (t : A ⟶ C) (s : C ⟶ B) (g : B ⟶ X) (m : A ⟶ B) (p : C ⟶ X)
  (q : A ⟶ X) (hts : t ≫ s = m) (hsg : s ≫ g = p) (hmg : m ≫ g = q) (htp : t ≫ p = q)
  {F G : X.Modules}

/-- **The canonical equation descends along `Stacks.AlgebraicGeometry.ModuleLimits.canMerge`.**
Let `A ⟶ C ⟶ B ⟶ X` be a chain of three morphisms of schemes.  If a morphism `θ` between the
pullbacks along `s` of the pullbacks along `g` of `F` and `G` satisfies the canonical equation
over `A` with the morphism `canSplit` produces from `Φ`, then the morphism `canMerge` produces
from `θ`, which lives over the composite `p`, satisfies the canonical equation with `Φ` itself.

This is one instance of the cocycle condition
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`, used once at `F` and once at `G`; nothing
geometric enters.  It is what carries the conclusion of the affine case of
[Stacks Project, Tag 01ZR] (2) over the diagram of preimages of an open of a stage to the descent
condition `Stacks.AlgebraicGeometry.ModuleLimits.IsStageDescent` over that open. -/
theorem canStep_canMerge_of_canStep_eq_canSplit
    (Φ : (Scheme.Modules.pullback q).obj F ⟶ (Scheme.Modules.pullback q).obj G)
    (θ : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g).obj G))
    (h : canStep t s m hts θ = canSplit m g q hmg Φ) :
    canStep t p q htp (canMerge s g p hsg θ) = Φ := by
  rw [canStep_eq_iff] at h ⊢
  have cocF := canHom_comp t s g m p q hts hsg hmg htp F
  have cocG := canHom_comp t s g m p q hts hsg hmg htp G
  simp only [canMerge, Functor.map_comp, Category.assoc]
  rw [cocG, reassoc_of% h, canHom_comp_canSplit, ← reassoc_of% cocF,
    ← canIso_hom s g p hsg F, Iso.map_inv_hom_id_assoc]

end Chain

/-! ### Passing one step further commutes with splitting -/

section Further

variable {A C B X : Scheme.{u}} (v : A ⟶ C) (u : C ⟶ B) (g : B ⟶ X) (vu : A ⟶ B) (ug : C ⟶ X)
  (vug : A ⟶ X) (hvu : v ≫ u = vu) (hug : u ≫ g = ug) (hvug : v ≫ ug = vug)
  (hvu' : vu ≫ g = vug) {F G : X.Modules}

/-- **`Stacks.AlgebraicGeometry.ModuleLimits.canSplit` commutes with passing one step further.**
Splitting a morphism over `ug` and then carrying it along `v` is carrying it along `v` and then
splitting.  Both `Stacks.AlgebraicGeometry.ModuleLimits.canStep` operations are determined by the
canonical comparison, so this is again the cocycle condition
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`.

It is what turns the agreement on overlaps produced by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_descent_agree`, which is stated for pullbacks
along the structure morphisms `preimageHom`, into agreement for pullbacks along the inclusions of
the opens of the stage, which is what a Zariski glueing on that stage asks for.  It serves
[Stacks Project, Tag 01ZR] (2). -/
theorem canSplit_canStep
    (Φ : (Scheme.Modules.pullback ug).obj F ⟶ (Scheme.Modules.pullback ug).obj G) :
    canStep v u vu hvu (canSplit u g ug hug Φ)
      = canSplit vu g vug hvu' (canStep v ug vug hvug Φ) := by
  refine eq_canSplit_of_canMerge_eq vu g vug hvu' _ _ ?_
  rw [canMerge_eq_iff]
  have cocF := canHom_comp v u g vu ug vug hvu hug hvu' hvug F
  have cocG := canHom_comp v u g vu ug vug hvu hug hvu' hvug G
  simp only [canStep, Category.assoc, canIso_hom]
  rw [← cocG, ← Functor.map_comp_assoc, canHom_comp_canSplit, Functor.map_comp, Category.assoc,
    ← canHom_comp_canStep v ug vug hvug Φ, reassoc_of% cocF, ← canIso_hom v u vu hvu,
    Iso.inv_hom_id_assoc, ← canIso_hom v ug vug hvug F, Iso.inv_hom_id_assoc]

end Further

/-! ### Tag 01ZR (2) over an affine open of a stage -/

section Local

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- The affine case of [Stacks Project, Tag 01ZR] (2), applied to the diagram of preimages of an
affine open `W` of the stage `D.obj i`: a morphism `Φ` of the pullbacks of `F` and `G` to the
preimage of `W` in the vertex of the cone is, after splitting through the base object of
`CategoryTheory.Over i`, the image under the canonical comparison of a morphism at some stage
over `i`.

Both local modules are pullbacks along
`Stacks.AlgebraicGeometry.ModuleLimits.preimageHom (D.map (𝟙 i)) W`; see the implementation
notes for why that and not the inclusion of the open.  The commuting triangle of the stage is
carried in the existential so that no type ascription is needed at the point of use. -/
private theorem exists_over_canStep_eq_canSplit (hc : IsLimit c) (i : I)
    {W : (D.obj i).Opens} (hW : IsAffineOpen W)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (Φ : (Scheme.Modules.pullback (preimageHom (c.π.app i) W)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (c.π.app i) W)).obj G) :
    ∃ (k : Over i) (e : k ⟶ Over.mk (𝟙 i))
      (hts : coneRes D c k.hom W ≫ (EventualLimit.preimageDiagram D i W).map e
        = coneRes D c (𝟙 i) W)
      (φk : (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i W).map e)).obj
            ((Scheme.Modules.pullback (preimageHom (D.map (𝟙 i)) W)).obj F) ⟶
          (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i W).map e)).obj
            ((Scheme.Modules.pullback (preimageHom (D.map (𝟙 i)) W)).obj G)),
      canStep (coneRes D c k.hom W) ((EventualLimit.preimageDiagram D i W).map e)
          (coneRes D c (𝟙 i) W) hts φk
        = canSplit (coneRes D c (𝟙 i) W) (preimageHom (D.map (𝟙 i)) W)
            (preimageHom (c.π.app i) W) (coneRes_comp_preimageHom D c (𝟙 i) W) Φ := by
  have haff : ∀ k : Over i, IsAffine ((EventualLimit.preimageDiagram D i W).obj k) :=
    EventualLimit.isAffine_preimageDiagram_obj D i hW
  have hdl : IsLimit (EventualLimit.preimageCone D c i W) :=
    EventualLimit.isLimitPreimageCone D c hc i W
  have hFfp : ((Scheme.Modules.pullback (preimageHom (D.map (𝟙 i)) W)).obj
      F).IsFinitePresentation := isFinitePresentation_pullback _ F
  have hGfp : ((Scheme.Modules.pullback (preimageHom (D.map (𝟙 i)) W)).obj
      G).IsFinitePresentation := isFinitePresentation_pullback _ G
  obtain ⟨k, e, φk, hφk⟩ := @exists_map_of_pullback_canonical_of_isAffine' _ _ _
    (EventualLimit.preimageDiagram D i W) (EventualLimit.preimageCone D c i W) haff hdl
    (Over.mk (𝟙 i)) _ _ hFfp hGfp
    (canSplit (coneRes D c (𝟙 i) W) (preimageHom (D.map (𝟙 i)) W) (preimageHom (c.π.app i) W)
      (coneRes_comp_preimageHom D c (𝟙 i) W) Φ)
  refine ⟨k, e, (EventualLimit.preimageCone D c i W).w e, φk, ?_⟩
  exact (canStep_eq_iff _ _ _ _ _ _).mpr hφk

/-- **[Stacks Project, Tag 01ZR] (2) over an affine open of a stage.**  Let `c` be a limit cone
on a cofiltered diagram `D` of schemes with affine transition morphisms, let `W` be an affine
open of a stage `D.obj i`, let `F` and `G` be sheaves of modules of finite presentation on
`D.obj i` and let `φ` be a morphism of their pullbacks to the vertex of the cone.  Then `φ`
descends over `W` at some stage over `i`, in the sense of
`Stacks.AlgebraicGeometry.ModuleLimits.IsStageDescent`.

This is the hypothesis `hloc` of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_descent_agree`.  Only the stages of the
diagram of preimages of `W` have to be affine, and they are because `W` is, so the stages of `D`
are required to be neither affine, nor quasi-compact, nor quasi-separated. -/
theorem exists_isStageDescent_of_isAffineOpen (hc : IsLimit c) (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G)
    {W : (D.obj i).Opens} (hW : IsAffineOpen W) :
    ∃ (j : I) (e : j ⟶ i)
      (ψ : (Scheme.Modules.pullback (preimageHom (D.map e) W)).obj F ⟶
        (Scheme.Modules.pullback (preimageHom (D.map e) W)).obj G),
      IsStageDescent D c e φ W ψ := by
  obtain ⟨k, e, hts, φk, hφk⟩ :=
    exists_over_canStep_eq_canSplit D c hc i hW F G (limitRestrictHom D c φ W)
  have hw : e.left ≫ 𝟙 i = k.hom := Over.w e
  have hgf : D.map e.left ≫ D.map (𝟙 i) = D.map k.hom := by rw [← D.map_comp, hw]
  have hsg : (EventualLimit.preimageDiagram D i W).map e ≫ preimageHom (D.map (𝟙 i)) W
      = preimageHom (D.map k.hom) W :=
    preimageRes_comp_preimageHom (D.map e.left) (D.map (𝟙 i)) (D.map k.hom) hgf W
  refine ⟨k.left, k.hom, canMerge ((EventualLimit.preimageDiagram D i W).map e)
    (preimageHom (D.map (𝟙 i)) W) (preimageHom (D.map k.hom) W) hsg φk, ?_⟩
  refine (canStep_eq_iff (coneRes D c k.hom W) (preimageHom (D.map k.hom) W)
    (preimageHom (c.π.app i) W) (coneRes_comp_preimageHom D c k.hom W) _ _).mp ?_
  exact canStep_canMerge_of_canStep_eq_canSplit (coneRes D c k.hom W)
    ((EventualLimit.preimageDiagram D i W).map e) (preimageHom (D.map (𝟙 i)) W)
    (coneRes D c (𝟙 i) W) (preimageHom (D.map k.hom) W) (preimageHom (c.π.app i) W) hts hsg
    (coneRes_comp_preimageHom D c (𝟙 i) W) (coneRes_comp_preimageHom D c k.hom W)
    (limitRestrictHom D c φ W) φk hφk

end Local

/-! ### Tag 01ZR (2) for a quasi-compact quasi-separated stage -/

section Glue

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **[Stacks Project, Tag 01ZR] (2) for a quasi-compact quasi-separated stage.**  A morphism of
the pullbacks to the vertex of the cone of two sheaves of modules of finite presentation on a
quasi-compact quasi-separated stage is
`Stacks.AlgebraicGeometry.ModuleLimits.canStep` of a morphism at some stage over it.

The three steps are the local descent
`exists_isStageDescent_of_isAffineOpen` over each member of the finite affine covering
`(D.obj i).affineCover.finiteSubcover` of the stage, the common refinement with agreement on
overlaps `exists_stage_descent_agree`, and the glueing.  That the family covers the stage is
supplied here: `exists_stage_descent_agree` does not require it.  The agreement produced there is
stated for pullbacks along the structure morphisms
`Stacks.AlgebraicGeometry.ModuleLimits.preimageHom` and is moved to pullbacks along the
inclusions of the opens by `canSplit_canStep`; the resulting equation is verified by locality
(`hom_ext_of_pullback_cover`) and, over each member of the covering, by the composition law
`Stacks.AlgebraicGeometry.ModuleLimits.canStep_canStep`. -/
theorem exists_canStep_eq_of_isLimit (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      canStep (c.π.app j) (D.map e) (c.π.app i) (c.w e) φj = φ := by
  classical
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  let V : 𝒰.I₀ → (D.obj i).Opens := fun a => (𝒰.f a).opensRange
  have hcov : ∀ x : D.obj i, ∃ a, x ∈ V a := fun x => 𝒰.isOpenCover_opensRange.exists_mem x
  obtain ⟨k, e, ψ, hψ, hagree⟩ := exists_stage_descent_agree D c hc i F G φ V
    (fun a => isAffineOpen_opensRange _)
    (fun W hW => exists_isStageDescent_of_isAffineOpen D c hc i F G φ hW)
  have hZ : ∀ a b, (D.map e ⁻¹ᵁ V a) ⊓ (D.map e ⁻¹ᵁ V b) ≤ D.map e ⁻¹ᵁ (V a ⊓ V b) :=
    fun _ _ _ hx => hx
  have hcovk : ∀ x : D.obj k, ∃ a, x ∈ D.map e ⁻¹ᵁ V a := fun x => hcov ((D.map e).base x)
  have hsplit : ∀ (a b x : 𝒰.I₀) (h : V a ⊓ V b ≤ V x),
      canStep ((D.obj k).homOfLE ((D.map e).preimage_mono h)) (D.map e ⁻¹ᵁ V x).ι
          (D.map e ⁻¹ᵁ (V a ⊓ V b)).ι ((D.obj k).homOfLE_ι _)
          (canSplit (D.map e ⁻¹ᵁ V x).ι (D.map e) (preimageHom (D.map e) (V x)) rfl (ψ x))
        = canSplit (D.map e ⁻¹ᵁ (V a ⊓ V b)).ι (D.map e) (preimageHom (D.map e) (V a ⊓ V b)) rfl
          (preimageHomLE (D.map e) h (ψ x)) := fun a b x h =>
    canSplit_canStep ((D.obj k).homOfLE ((D.map e).preimage_mono h)) (D.map e ⁻¹ᵁ V x).ι (D.map e)
      (D.map e ⁻¹ᵁ (V a ⊓ V b)).ι (preimageHom (D.map e) (V x))
      (preimageHom (D.map e) (V a ⊓ V b)) ((D.obj k).homOfLE_ι _) rfl
      (preimageLE_comp_preimageHom (D.map e) h) rfl _
  obtain ⟨φj, hφj⟩ := exists_pullback_map_eq_of_cover (fun a => D.map e ⁻¹ᵁ V a) hcovk
    (fun a b => D.map e ⁻¹ᵁ (V a ⊓ V b))
    (fun _ _ => (D.map e).preimage_mono inf_le_left)
    (fun _ _ => (D.map e).preimage_mono inf_le_right) hZ
    (fun a => canSplit (D.map e ⁻¹ᵁ V a).ι (D.map e) (preimageHom (D.map e) (V a)) rfl (ψ a))
    fun a b => (hsplit a b a inf_le_left).trans
      ((congrArg _ (hagree a b)).trans (hsplit a b b inf_le_right).symm)
  refine ⟨k, e, φj, ?_⟩
  refine hom_ext_of_pullback_cover (fun a => c.π.app i ⁻¹ᵁ V a)
    (fun x => hcov ((c.π.app i).base x)) (fun a => ?_)
  refine pullback_map_eq_of_canStep_eq (c.π.app i ⁻¹ᵁ V a).ι (c.π.app i)
    (preimageHom (c.π.app i) (V a)) rfl ?_
  have hιe : (D.map e ⁻¹ᵁ V a).ι ≫ D.map e = preimageHom (D.map e) (V a) := rfl
  have hιi : (c.π.app i ⁻¹ᵁ V a).ι ≫ c.π.app i = preimageHom (c.π.app i) (V a) := rfl
  have hq1 : ((c.π.app i ⁻¹ᵁ V a).ι ≫ c.π.app k) ≫ D.map e
      = preimageHom (c.π.app i) (V a) := by
    rw [Category.assoc, c.w e]; exact hιi
  have hq2 : (coneRes D c e (V a) ≫ (D.map e ⁻¹ᵁ V a).ι) ≫ D.map e
      = preimageHom (c.π.app i) (V a) := by
    rw [Category.assoc, hιe]; exact coneRes_comp_preimageHom D c e (V a)
  have h1 := canStep_canStep (c.π.app i ⁻¹ᵁ V a).ι (c.π.app k) (D.map e)
    ((c.π.app i ⁻¹ᵁ V a).ι ≫ c.π.app k) (c.π.app i) (preimageHom (c.π.app i) (V a))
    rfl (c.w e) rfl hq1 φj
  have hmorph : (c.π.app i ⁻¹ᵁ V a).ι ≫ c.π.app k
      = coneRes D c e (V a) ≫ (D.map e ⁻¹ᵁ V a).ι :=
    (preimageRes_comp_ι (c.π.app k) (D.map e) (c.π.app i) (c.w e) (V a)).symm
  have h2 := canStep_congr_hom hmorph (D.map e) (preimageHom (c.π.app i) (V a)) hq1 hq2 φj
  have h3 := canStep_canStep (coneRes D c e (V a)) (D.map e ⁻¹ᵁ V a).ι (D.map e)
    (coneRes D c e (V a) ≫ (D.map e ⁻¹ᵁ V a).ι) (preimageHom (D.map e) (V a))
    (preimageHom (c.π.app i) (V a)) rfl hιe (coneRes_comp_preimageHom D c e (V a)) hq2 φj
  have h4 : canStep (D.map e ⁻¹ᵁ V a).ι (D.map e) (preimageHom (D.map e) (V a)) hιe φj
      = ψ a := by
    refine Eq.trans (canStep_eq_canMerge (D.map e ⁻¹ᵁ V a).ι (D.map e)
      (preimageHom (D.map e) (V a)) hιe φj) ?_
    rw [hφj a]
    exact canMerge_canSplit _ _ _ _ (ψ a)
  refine h1.trans (h2.trans (h3.symm.trans ?_))
  rw [h4]
  exact (canStep_eq_iff (coneRes D c e (V a)) (preimageHom (D.map e) (V a))
    (preimageHom (c.π.app i) (V a)) (coneRes_comp_preimageHom D c e (V a)) (ψ a)
    (limitRestrictHom D c φ (V a))).mpr (hψ a)

/-- **[Stacks Project, Tag 01ZR] (2) for a quasi-compact quasi-separated stage, in the canonically
pinned form.**  This is `exists_canStep_eq_of_isLimit` read through `canStep_eq_iff`. -/
theorem exists_map_of_pullback_canonical_of_isLimit (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G
        = canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F ≫ φ := by
  obtain ⟨j, e, φj, h⟩ := exists_canStep_eq_of_isLimit D c hc i F G φ
  exact ⟨j, e, φj, (canStep_eq_iff _ _ _ _ _ _).mp h⟩

end Glue

/-! ### The index morphism universe -/

section IndexHomUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **[Stacks Project, Tag 01ZR] (2) with the index morphism universe unrestricted.**  This is
`exists_map_of_pullback_canonical_of_isLimit` applied to
`CategoryTheory.Functor.FullImage D`; the conclusion mentions only `D` and the cone, so it
transports, which it would not if it mentioned the objects of a diagram of preimages. -/
theorem exists_map_of_pullback_canonical_of_isLimit' (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G
        = canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F ≫ φ := by
  obtain ⟨j, gm, hgm⟩ := @exists_map_of_pullback_canonical_of_isLimit (FullImage D) _ _
    (ι D) _ (cone D c) (isLimitCone D hc) ⟨i⟩ ‹_› ‹_› F G ‹_› ‹_› φ
  refine ⟨j.as, hom D gm, ?_⟩
  exact exists_canonical_congr (c.π.app j.as) (map_hom D gm) (c.π.app i)
    (c.w (hom D gm)) ((cone D c).w gm) F G φ hgm

/-- **[Stacks Project, Tag 01ZR] (2), with the canonical identifications written out.**  This is
the statement of the clause of the tag verbatim, obtained from
`exists_map_of_pullback_canonical_of_isLimit'` by unfolding the canonical identification. -/
@[stacks 01ZR "descend_morphisms"]
theorem exists_map_of_pullback_of_isLimit (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫
          (Scheme.Modules.pullbackComp (c.π.app j) (D.map e)).hom.app G ≫
            (Scheme.Modules.pullbackCongr (c.w e)).hom.app G =
        (Scheme.Modules.pullbackComp (c.π.app j) (D.map e)).hom.app F ≫
          (Scheme.Modules.pullbackCongr (c.w e)).hom.app F ≫ φ := by
  obtain ⟨j, e, φj, heq⟩ := exists_map_of_pullback_canonical_of_isLimit' D c hc i F G φ
  refine ⟨j, e, φj, ?_⟩
  rw [canHom, canHom, Category.assoc] at heq
  exact heq

/-- **[Stacks Project, Tag 01ZR] (1) for a cofiltered limit of quasi-compact quasi-separated
schemes with affine transition morphisms.**  A sheaf of modules of finite presentation on the
limit is the pullback of one on a stage.  This is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_map` with its
hypothesis `hmap` discharged by `exists_map_of_pullback_of_isLimit`, and it is the statement
[Stacks Project, Tag 0ASY] calls. -/
@[stacks 01ZR "descend_modules"]
theorem exists_isFinitePresentation_pullback_iso_of_qcqs (hc : IsLimit c)
    [∀ j : I, CompactSpace (D.obj j)] [∀ j : I, QuasiSeparatedSpace (D.obj j)]
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) := by
  refine exists_isFinitePresentation_pullback_iso_of_map D c hc
    (fun j F' G' hF hG φ => ?_) F
  exact @exists_map_of_pullback_of_isLimit _ _ _ D _ c hc j _ _ F' G' hF hG φ

end IndexHomUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end
