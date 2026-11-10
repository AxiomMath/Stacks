module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericFibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.OffDiagonalIncidenceVariety
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection

/-!
# Intersecting a closed subvariety with the cone swept out by a general projection

Let `V` be a vector space of dimension `n + 1` over an algebraically closed field and let
`Y, Z ⊆ 𝐏(V)` be closed subsets with `Y` not all of `𝐏(V)`. For a closed point `p` of a
nonempty Zariski open subset of `𝐏(V)`,

`Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E`

with `E ⊆ Y` closed of dimension at most `dim Y + dim Z + 1 - n`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_lineSubmodule_swap`: **three
  collinear closed points are collinear in any order** — if `y` lies on the line joining `p` to
  `z` then `p` lies on the line joining `y` to `z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_point_offDiagIncidenceVariety`: **a collinear
  triple of closed points is a point of the off-diagonal incidence variety** lying over the third
  of them.
* `exists_isOpen_forall_topologicalKrullDim_fiber_incidenceVarietyToProj_add_le`:
  the general fibre of `T ⟶ 𝐏(V)` has dimension at most `dim Y + dim Z + 1 - n`.
* `ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq_of_union_ne_univ`:
  the decomposition together with the dimension bound on `E`, for `Y ∪ Z` not all of `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq_of_ne_univ`:
  the same under the weaker hypothesis that `Y` alone is not all of `𝐏(V)`, nothing being asked
  of `Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_isOpen_inter_projectionCone_univ_eq`:
  that hypothesis is the weakest possible — for `Y = Z = 𝐏(V)` the asserted decomposition holds
  over no nonempty open subset at all.

## Implementation notes

`E` is the **closure of the difference** `(Y ∖ Z) ∩ r_p^{-1}(r_p(Z))`, as in the source, where the
bound is read off the incidence variety

`T = {(y, z, p) : y ∈ Y ∖ Z, z ∈ Z, p on the line joining y and z}`.

It cannot be taken to be the whole of `Y ∩ r_p^{-1}(r_p(Z))`: that set contains `Y ∩ Z`, so for
`Y = Z` a single closed point of a `𝐏(V)` of dimension at least two the asserted bound would read
`n ≤ 1`. The decomposition holds for the closure of the difference because `Y ∩ r_p^{-1}(r_p(Z))`
is closed, the image of `Z` under the projection being closed.

The count has three steps. The first is the bound `dim T ≤ dim Y + dim Z + 1`, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_offDiagIncidenceVariety_le`: the
projection of `T` to `(Y ∖ Z) × Z` has one-dimensional fibres at the closed points and the base
has dimension at most `dim Y + dim Z`.

The second carries that bound to the general fibre of `T ⟶ 𝐏(V)` through
`AlgebraicGeometry.exists_isOpen_forall_topologicalKrullDim_fiber_add_le_of_ne_top`, which asks of
`T` only that its space be Noetherian and of the morphism only that it be quasi-compact — no
irreducibility of `T` and no flatness. Both are supplied here: `T` is of finite type over `Spec k`
and compact over its base, which makes it Noetherian, and a morphism out of a Noetherian space is
quasi-compact. The triangle over `Spec k` the bound needs is
`AlgebraicGeometry.ProjectiveSpaceOfModule.incidenceVarietyToProj_comp_toSpec`, obtained from the
pullback square defining `T` together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.prFst_comp_prodTwoToSpec` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.pr₃_comp_toSpec`.

The third identifies `E`. Only one containment is needed,

`(Y ∖ Z) ∩ r_p^{-1}(r_p(Z)) ⊆ closure (image in 𝐏(V) of the fibre of T ⟶ 𝐏(V) over p)`,

and since `𝐏(V)` is a Jacobson space and the left-hand side is locally closed it suffices to place
its **closed** points in that image
(`JacobsonSpace.closure_inter_closedPoints_eq_closure`). For a closed point `y` there, a point of
`Z` has the same image as `y` under `r_p`, so `Z ∩ L(p, y)` is a nonempty closed subset and
carries a closed point `z` of `𝐏(V)`; the triple `(y, z, p)` is then collinear, because `z` lies
on `L(p, y)` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_lineSubmodule_swap` turns that into
`p ∈ L(y, z)`. That swap is the only piece of projective geometry the count needs beyond what was
already available: the equations of two distinct closed points cut out a submodule of corank two,
so a containment of two such submodules is an equality.

Turning the collinear triple into a point of `T` is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_point_offDiagIncidenceVariety`. Over an
algebraically closed field the three closed points are rational
(`AlgebraicGeometry.isRationalPoint_of_isClosed`), so `(y, z)` is a `k`-point of `(Y ∖ Z) × Z` and
`(y, z, p)` is a `k`-point of the triple product obtained from
`AlgebraicGeometry.ProjectiveSpaceOfModule.rationalFibreSection`; it lands in the collinearity
locus, and `AlgebraicGeometry.Scheme.Pullback.range_fst` lifts it to the pullback `T`.

Dimensions take values in `WithBot ℕ∞`, which has no subtraction, so the bound
`dim E ≤ dim Y + dim Z + 1 - n` is stated additively as `dim E + n ≤ dim Y + dim Z + 1`.

The hypothesis `Y ∪ Z ≠ 𝐏(V)` is a correction to the source, which leaves it implicit: for
`Y = Z = 𝐏(V)` the asserted identity fails for every `p`, the left-hand side missing `p` while
`Y ∩ Z` contains it. It is slightly stronger than strictly necessary — for `Y = 𝐏(V)` and `Z = ∅`
the conclusion holds with `E = ∅` — but it is what the source's choice of `U` describes.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### Three collinear closed points are collinear in any order -/

/-- The line joining two points does not depend on their order. -/
public theorem lineSubmodule_comm (p q : projectiveSpaceOfModule k V) :
    lineSubmodule k V p q = lineSubmodule k V q p :=
  inf_comm _ _

/-- **Collinearity of three closed points is symmetric in the first and third.** If a closed
point `y` lies on the line joining two distinct closed points `p` and `z`, then `p` lies on the
line joining `y` to `z`, provided `y ≠ z`.

Both lines are cut out by submodules of corank two — the degree-one forms vanishing at two
distinct closed points — and the hypothesis says that the first is contained in the second, so
the two submodules coincide.

The hypothesis `y ≠ z` is needed: `z` always lies on the line joining `p` to `z`, while `p` lies
on the line joining `z` to itself only if `p = z`. -/
public theorem mem_linearSubspace_lineSubmodule_swap [IsAlgClosed k] [Module.Finite k V]
    {p y z : projectiveSpaceOfModule k V}
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V)))
    (hz : IsClosed ({z} : Set (projectiveSpaceOfModule k V)))
    (hpz : p ≠ z) (hyz : y ≠ z)
    (h : y ∈ linearSubspace k V (lineSubmodule k V p z)) :
    p ∈ linearSubspace k V (lineSubmodule k V y z) := by
  have hdef : ∀ a b : projectiveSpaceOfModule k V,
      lineSubmodule k V a b = pointSubmodule k V a ⊓ pointSubmodule k V b := fun _ _ => rfl
  have hle : lineSubmodule k V p z ≤ lineSubmodule k V y z := by
    rw [hdef y z]
    exact le_inf ((mem_linearSubspace_iff k V _ y).mp h) (by rw [hdef p z]; exact inf_le_right)
  have hrank : Module.finrank k ↥(lineSubmodule k V p z) =
      Module.finrank k ↥(lineSubmodule k V y z) := by
    have h1 := (lineSubmodule k V p z).finrank_quotient_add_finrank
    have h2 := (lineSubmodule k V y z).finrank_quotient_add_finrank
    rw [finrank_quotient_lineSubmodule k V hp hz hpz] at h1
    rw [finrank_quotient_lineSubmodule k V hy hz hyz] at h2
    omega
  rw [mem_linearSubspace_iff, ← Submodule.eq_of_le_of_finrank_eq hle hrank, hdef p z]
  exact inf_le_left

/-- **A point of `Z` on the line joining `p` to a point of the cone it sweeps out.** If `y` lies
in `r_p^{-1}(r_p(Z))` for a closed subset `Z`, then some *closed* point of `Z` lies on the line
joining `p` to `y`: a point of `Z` with the same image as `y` under `r_p` lies on that line, so
`Z ∩ L(p, y)` is a nonempty closed subset of the Jacobson space `𝐏(V)`. -/
public theorem exists_isClosed_mem_inter_linearSubspace_lineSubmodule [IsAlgClosed k]
    [Module.Finite k V] [Nontrivial V] {p y : projectiveSpaceOfModule k V}
    {Z : Set (projectiveSpaceOfModule k V)} (hZ : IsClosed Z)
    (hy : y ∈ projectionCone k V p Z) :
    ∃ z ∈ Z, IsClosed ({z} : Set (projectiveSpaceOfModule k V)) ∧
      z ∈ linearSubspace k V (lineSubmodule k V p y) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  obtain ⟨x, ⟨w, hwZ, hproj⟩, hxy⟩ := hy
  have hwline : (projectionDomain k V (pointSubmodule k V p)).ι.base w ∈
      linearSubspace k V (lineSubmodule k V p y) := by
    rw [← hxy]
    exact mem_linearSubspace_inf_of_projection_eq k V (pointSubmodule k V p) w x hproj
  have hne : (Z ∩ linearSubspace k V (lineSubmodule k V p y)).Nonempty :=
    ⟨_, hwZ, hwline⟩
  have hcl : IsClosed (Z ∩ linearSubspace k V (lineSubmodule k V p y)) :=
    hZ.inter (isClosed_linearSubspace k V _)
  obtain ⟨z, ⟨hzZ, hzL⟩, hzcl⟩ := nonempty_inter_closedPoints hne hcl.isLocallyClosed
  exact ⟨z, hzZ, mem_closedPoints_iff.mp hzcl, hzL⟩

/-- The projection domain of a closed point `p` is the complement of `p`. -/
private theorem range_projectionDomain_ι_base [IsAlgClosed k] [Module.Finite k V]
    {p : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base = {p}ᶜ := by
  rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V p hpc]

/-- The empty subset has dimension `⊥`, so it satisfies any bound of the form `dim E + n ≤ a`. -/
private theorem topologicalKrullDim_empty_add_le (n : ℕ) (a : WithBot ℕ∞) :
    topologicalKrullDim ↥(∅ : Set (projectiveSpaceOfModule k V)) + (n : WithBot ℕ∞) ≤ a := by
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty
    (↥(∅ : Set (projectiveSpaceOfModule k V)))).mpr inferInstance]
  simp

/-- A point of a closed subscheme of `𝐏(V)` lying over a closed point of `𝐏(V)` is closed. -/
private theorem isClosed_singleton_of_closedSubschemeOfι {W : Set (projectiveSpaceOfModule k V)}
    (hW : IsClosed W) {w : closedSubschemeOf k V W hW} {x : projectiveSpaceOfModule k V}
    (hw : (closedSubschemeOfι k V W hW).base w = x) (hx : IsClosed ({x} : Set _)) :
    IsClosed ({w} : Set (closedSubschemeOf k V W hW)) :=
  (closedSubschemeOfι k V W hW).isClosedEmbedding.isClosed_iff_image_isClosed.mpr
    (by rwa [Set.image_singleton, hw])

/-! ### The off-diagonal incidence variety over `𝐏(V)` -/

variable [FiniteDimensional k V] [Nontrivial V]

/-- The projection of the collinearity subscheme to the first two factors is quasi-compact,
being a closed immersion followed by a base change of the proper structure morphism of
`𝐏(V)`. -/
public instance quasiCompact_collinearProj : QuasiCompact (collinearProj k V) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have := isClosedImmersion_collinearSubschemeι k V
  rw [collinearProj, prFst]
  infer_instance

/-- `𝐏(V) ×_k 𝐏(V)` is proper over the ground field. -/
public instance isProper_prodTwoToSpec : IsProper (prodTwoToSpec k V) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  rw [prodTwoToSpec]
  infer_instance

/-- **`𝐏(V) ×_k 𝐏(V)` has a Noetherian underlying space**, being proper over a field. -/
public instance noetherianSpace_prodTwo : NoetherianSpace (prodTwo k V) := by
  have : IsLocallyNoetherian (prodTwo k V) :=
    LocallyOfFiniteType.isLocallyNoetherian (prodTwoToSpec k V)
  have : CompactSpace (prodTwo k V) :=
    QuasiCompact.compactSpace_of_compactSpace (prodTwoToSpec k V)
  have : IsNoetherian (prodTwo k V) := {}
  infer_instance

variable (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) (hZ : IsClosed Z)

/-- A closed subscheme of `𝐏(V)` is proper over the ground field. -/
public instance isProper_closedSubschemeOfToSpec :
    IsProper (closedSubschemeOfToSpec k V Y hY) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have := isClosedImmersion_closedSubschemeOfι k V Y hY
  rw [closedSubschemeOfToSpec]
  infer_instance

/-- A closed subscheme of `𝐏(V)` has a compact underlying space. -/
public instance compactSpace_closedSubschemeOf :
    CompactSpace (closedSubschemeOf k V Y hY) := by
  have := isProper_closedSubschemeOfToSpec k V Y hY
  exact QuasiCompact.compactSpace_of_compactSpace (closedSubschemeOfToSpec k V Y hY)

/-- The product of two closed subschemes of `𝐏(V)` has a Noetherian underlying space: it is
locally of finite type over the ground field, and compact over its first factor, which is itself
compact. -/
public instance noetherianSpace_prodOfClosed :
    NoetherianSpace (prodOfClosed k V Y Z hY hZ) := by
  have hpY := isProper_closedSubschemeOfToSpec k V Y hY
  have hcZ : CompactSpace (closedSubschemeOf k V Z hZ) := compactSpace_closedSubschemeOf k V Z hZ
  have : IsLocallyNoetherian (prodOfClosed k V Y Z hY hZ) :=
    LocallyOfFiniteType.isLocallyNoetherian (prodOfClosedToSpec k V Y Z hY hZ)
  have : CompactSpace (prodOfClosed k V Y Z hY hZ) :=
    inferInstanceAs (CompactSpace
      ↥(pullback (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ)))
  have : IsNoetherian (prodOfClosed k V Y Z hY hZ) := {}
  infer_instance

/-- The off-diagonal base `(Y ∖ Z) × Z` has a Noetherian underlying space, being an open
subscheme of a product of two closed subschemes of `𝐏(V)`. -/
public instance noetherianSpace_offDiagBase :
    NoetherianSpace (offDiagBase k V Y Z hY hZ) :=
  (offDiagLocus k V Y Z hY hZ).ι.isEmbedding.isInducing.noetherianSpace

/-- The projection of the off-diagonal incidence variety to its base is quasi-compact, being a
base change of the projection of the collinearity subscheme. -/
public instance quasiCompact_offDiagIncidenceVarietyToBase :
    QuasiCompact (offDiagIncidenceVarietyToBase k V Y Z hY hZ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_incidenceVariety k V (offDiagBaseToProdTwo k V Y Z hY hZ)) inferInstance

/-- **The off-diagonal incidence variety has a Noetherian underlying space.** It is locally of
finite type over the ground field, hence locally Noetherian, and compact over its base, which is
itself compact. -/
public instance noetherianSpace_offDiagIncidenceVariety :
    NoetherianSpace (offDiagIncidenceVariety k V Y Z hY hZ) := by
  have : IsLocallyNoetherian (offDiagIncidenceVariety k V Y Z hY hZ) :=
    LocallyOfFiniteType.isLocallyNoetherian (offDiagIncidenceVarietyToSpec k V Y Z hY hZ)
  have : CompactSpace (offDiagIncidenceVariety k V Y Z hY hZ) :=
    QuasiCompact.compactSpace_of_compactSpace (offDiagIncidenceVarietyToBase k V Y Z hY hZ)
  have : IsNoetherian (offDiagIncidenceVariety k V Y Z hY hZ) := {}
  infer_instance

omit [FiniteDimensional k V] [Nontrivial V] in
/-- **The morphism `T ⟶ 𝐏(V)` of the incidence variety is a morphism over `Spec k`**: the triangle
the general-fibre dimension bound asks for. -/
public theorem incidenceVarietyToProj_comp_toSpec :
    incidenceVarietyToProj k V (offDiagBaseToProdTwo k V Y Z hY hZ) ≫
        projectiveSpaceOfModuleToSpec k V =
      offDiagIncidenceVarietyToSpec k V Y Z hY hZ := by
  calc incidenceVarietyToProj k V (offDiagBaseToProdTwo k V Y Z hY hZ) ≫
        projectiveSpaceOfModuleToSpec k V
      = incidenceVarietyToCollinear k V (offDiagBaseToProdTwo k V Y Z hY hZ) ≫
          collinearSubschemeι k V ≫ (pr₃ k V ≫ projectiveSpaceOfModuleToSpec k V) := by
        rw [incidenceVarietyToProj, collinearProj₃]
        simp only [Category.assoc]
    _ = incidenceVarietyToCollinear k V (offDiagBaseToProdTwo k V Y Z hY hZ) ≫
          collinearSubschemeι k V ≫ (prFst k V ≫ prodTwoToSpec k V) := by
        rw [pr₃_comp_toSpec, prFst_comp_prodTwoToSpec]
    _ = (incidenceVarietyToCollinear k V (offDiagBaseToProdTwo k V Y Z hY hZ) ≫
          collinearProj k V) ≫ prodTwoToSpec k V := by
        rw [collinearProj]
        simp only [Category.assoc]
    _ = (offDiagIncidenceVarietyToBase k V Y Z hY hZ ≫
          offDiagBaseToProdTwo k V Y Z hY hZ) ≫ prodTwoToSpec k V := by
        rw [(isPullback_incidenceVariety k V (offDiagBaseToProdTwo k V Y Z hY hZ)).w]
    _ = offDiagIncidenceVarietyToSpec k V Y Z hY hZ := by
        rw [offDiagIncidenceVarietyToSpec, offDiagBaseToSpec]
        simp only [Category.assoc]

/-- **The first coordinate of the off-diagonal incidence variety**: the morphism
`T ⟶ 𝐏(V)`, `(y, z, p) ↦ y`, whose image on a fibre over `p` is the closed subset `E` of
[Stacks, Tag 0B1R]. -/
public def offDiagIncidenceFst :
    offDiagIncidenceVariety k V Y Z hY hZ ⟶ projectiveSpaceOfModule k V :=
  offDiagIncidenceVarietyToBase k V Y Z hY hZ ≫
    offDiagBaseToProdTwo k V Y Z hY hZ ≫ prodTwoFst k V

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The first coordinate is a morphism over `Spec k`. -/
public theorem offDiagIncidenceFst_comp_toSpec :
    offDiagIncidenceFst k V Y Z hY hZ ≫ projectiveSpaceOfModuleToSpec k V =
      offDiagIncidenceVarietyToSpec k V Y Z hY hZ := by
  rw [offDiagIncidenceFst, offDiagIncidenceVarietyToSpec, offDiagBaseToSpec]
  simp only [Category.assoc]
  rfl

/-! ### A collinear triple of closed points as a point of the incidence variety -/

/-- **A collinear triple of closed points is a point of the off-diagonal incidence variety.** For
closed points `y ∈ Y ∖ Z` and `z ∈ Z` and a point `p` on the line joining them there is a point
of `T` whose image in `𝐏(V)` is `p` and whose first coordinate is `y`.

The three points are rational over an algebraically closed field, so `(y, z)` is a `k`-point of
`(Y ∖ Z) × Z` and `(y, z, p)` a `k`-point of the triple product; the latter is collinear, hence a
point of the collinearity subscheme, and a point of a fibre product exists over any point of one
factor whose image lies in the range of the other. -/
public theorem exists_point_offDiagIncidenceVariety [IsAlgClosed k]
    {y z p : projectiveSpaceOfModule k V}
    (hyc : IsClosed ({y} : Set (projectiveSpaceOfModule k V)))
    (hzc : IsClosed ({z} : Set (projectiveSpaceOfModule k V)))
    (hyY : y ∈ Y) (hyZ : y ∉ Z) (hzZ : z ∈ Z) (hyz : y ≠ z)
    (hp : p ∈ linearSubspace k V (lineSubmodule k V y z)) :
    ∃ t : offDiagIncidenceVariety k V Y Z hY hZ,
      (incidenceVarietyToProj k V (offDiagBaseToProdTwo k V Y Z hY hZ)).base t = p ∧
        (offDiagIncidenceFst k V Y Z hY hZ).base t = y := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  -- the two points, read in the closed subschemes they lie on
  obtain ⟨y', hy'⟩ : y ∈ Set.range (closedSubschemeOfι k V Y hY).base := by
    rwa [range_closedSubschemeOfι]
  obtain ⟨z', hz'⟩ : z ∈ Set.range (closedSubschemeOfι k V Z hZ).base := by
    rwa [range_closedSubschemeOfι]
  have hy'c := isClosed_singleton_of_closedSubschemeOfι k V hY hy' hyc
  have hz'c := isClosed_singleton_of_closedSubschemeOfι k V hZ hz' hzc
  -- the two `k`-points
  set ptY := ptOfIsRationalPoint (closedSubschemeOfToSpec k V Y hY) y'
    (isRationalPoint_of_isClosed k (closedSubschemeOfToSpec k V Y hY) y' hy'c) with hptY
  set ptZ := ptOfIsRationalPoint (closedSubschemeOfToSpec k V Z hZ) z'
    (isRationalPoint_of_isClosed k (closedSubschemeOfToSpec k V Z hZ) z' hz'c) with hptZ
  have hptYc : ptY ≫ closedSubschemeOfToSpec k V Y hY = 𝟙 _ := ptOfIsRationalPoint_comp _ _ _
  have hptZc : ptZ ≫ closedSubschemeOfToSpec k V Z hZ = 𝟙 _ := ptOfIsRationalPoint_comp _ _ _
  set x₀ : ↥(Spec (CommRingCat.of k)) := default with hx₀
  have hptYa : (closedSubschemeOfι k V Y hY).base (ptY.base x₀) = y := by
    rw [hptY, ptOfIsRationalPoint_apply, hy']
  have hptZa : (closedSubschemeOfι k V Z hZ).base (ptZ.base x₀) = z := by
    rw [hptZ, ptOfIsRationalPoint_apply, hz']
  -- the `k`-point of the product of the two closed subschemes
  have hwpair : ptY ≫ closedSubschemeOfToSpec k V Y hY =
      ptZ ≫ closedSubschemeOfToSpec k V Z hZ := by rw [hptYc, hptZc]
  set ptPair : Spec (CommRingCat.of k) ⟶ prodOfClosed k V Y Z hY hZ :=
    pullback.lift ptY ptZ hwpair with hptPair
  have hliftfst : ptPair ≫ pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ) = ptY := pullback.lift_fst _ _ _
  have hliftsnd : ptPair ≫ pullback.snd (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ) = ptZ := pullback.lift_snd _ _ _
  have hpairfst : ptPair ≫ prodOfClosedFst k V Y Z hY hZ =
      ptY ≫ closedSubschemeOfι k V Y hY :=
    (Category.assoc ptPair (pullback.fst (closedSubschemeOfToSpec k V Y hY)
        (closedSubschemeOfToSpec k V Z hZ)) (closedSubschemeOfι k V Y hY)).symm.trans
      (congrArg (· ≫ closedSubschemeOfι k V Y hY) hliftfst)
  have hpairsnd : ptPair ≫ prodOfClosedSnd k V Y Z hY hZ =
      ptZ ≫ closedSubschemeOfι k V Z hZ :=
    (Category.assoc ptPair (pullback.snd (closedSubschemeOfToSpec k V Y hY)
        (closedSubschemeOfToSpec k V Z hZ)) (closedSubschemeOfι k V Z hZ)).symm.trans
      (congrArg (· ≫ closedSubschemeOfι k V Z hZ) hliftsnd)
  have hpairfsta : (prodOfClosedFst k V Y Z hY hZ).base (ptPair.base x₀) = y := by
    rw [← Scheme.Hom.comp_apply, hpairfst, Scheme.Hom.comp_apply, hptYa]
  -- it lands in the off-diagonal locus
  have hloc : ptPair.base x₀ ∈
      ((offDiagLocus k V Y Z hY hZ : (prodOfClosed k V Y Z hY hZ).Opens) :
        Set (prodOfClosed k V Y Z hY hZ)) := by
    change (prodOfClosedFst k V Y Z hY hZ).base (ptPair.base x₀) ∈ Zᶜ
    rw [hpairfsta]
    exact hyZ
  have hrangesub : Set.range ptPair.base ⊆
      Set.range (offDiagLocus k V Y Z hY hZ).ι.base := by
    rw [range_base_eq_singleton ptPair x₀, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hloc
  set ptBase := IsOpenImmersion.lift (offDiagLocus k V Y Z hY hZ).ι ptPair hrangesub
    with hptBase
  have hbasefac : ptBase ≫ (offDiagLocus k V Y Z hY hZ).ι = ptPair :=
    IsOpenImmersion.lift_fac _ _ _
  -- the `k`-point of `𝐏(V) ×_k 𝐏(V)` it determines
  set pt := ptBase ≫ offDiagBaseToProdTwo k V Y Z hY hZ with hpt
  have hptfac : pt = ptPair ≫ prodOfClosedToProdTwo k V Y Z hY hZ := by
    rw [hpt, offDiagBaseToProdTwo, ← Category.assoc, hbasefac]
  have hptfst : pt ≫ prodTwoFst k V = ptY ≫ closedSubschemeOfι k V Y hY := by
    rw [hptfac, Category.assoc, prodOfClosedToProdTwo_comp_prodTwoFst, hpairfst]
  have hptsnd : pt ≫ prodTwoSnd k V = ptZ ≫ closedSubschemeOfι k V Z hZ := by
    rw [hptfac, Category.assoc, prodOfClosedToProdTwo_comp_prodTwoSnd, hpairsnd]
  have hptspec : pt ≫ prodTwoToSpec k V = 𝟙 _ := by
    have hdef : prodTwoToSpec k V = prodTwoFst k V ≫ projectiveSpaceOfModuleToSpec k V := rfl
    rw [hdef, ← Category.assoc, hptfst, Category.assoc]
    exact hptYc
  set q := pt.base x₀ with hq
  have hqrange : Set.range pt.base = {q} := range_base_eq_singleton pt x₀
  have hqfst : (prodTwoFst k V).base q = y := by
    rw [hq, ← Scheme.Hom.comp_apply, hptfst, Scheme.Hom.comp_apply, hptYa]
  have hqsnd : (prodTwoSnd k V).base q = z := by
    rw [hq, ← Scheme.Hom.comp_apply, hptsnd, Scheme.Hom.comp_apply, hptZa]
  have hqimg : q ∈ Set.range (offDiagBaseToProdTwo k V Y Z hY hZ).base :=
    ⟨ptBase.base x₀, by rw [hq, hpt, Scheme.Hom.comp_apply]⟩
  -- the collinear triple
  set t₃ := (rationalFibreSection k V pt hptspec).base p with ht₃
  have h3 : (pr₃ k V).base t₃ = p := pr₃_base_rationalFibreSection pt hptspec p
  have hprFst : (prFst k V).base t₃ = q := by
    rw [ht₃, ← Scheme.Hom.comp_apply, rationalFibreSection_comp_prFst pt hptspec,
      Scheme.Hom.comp_apply]
    have hmem : pt.base ((projectiveSpaceOfModuleToSpec k V).base p) ∈ Set.range pt.base :=
      Set.mem_range_self _
    rw [hqrange] at hmem
    exact hmem
  have h1 : (pr₁ k V).base t₃ = y := by
    rw [pr₁_eq_prFst_comp, Scheme.Hom.comp_apply, hprFst, hqfst]
  have h2 : (pr₂ k V).base t₃ = z := by
    rw [pr₂_eq_prFst_comp, Scheme.Hom.comp_apply, hprFst, hqsnd]
  have hcol : t₃ ∈ collinearLocus k V := by
    refine (mem_collinearLocus_iff_mem_linearSubspace_lineSubmodule k V
      (by rwa [h1]) (by rwa [h2]) (by rwa [h1, h2])).mpr ?_
    rwa [h1, h2, h3]
  obtain ⟨c, hc⟩ : t₃ ∈ Set.range (collinearSubschemeι k V).base := by
    rwa [range_collinearSubschemeι]
  have hcproj : (collinearProj k V).base c = q := by
    rw [collinearProj, Scheme.Hom.comp_apply, hc, hprFst]
  obtain ⟨t, ht⟩ : c ∈
      Set.range (incidenceVarietyToCollinear k V (offDiagBaseToProdTwo k V Y Z hY hZ)).base := by
    have hpre : c ∈ (collinearProj k V).base ⁻¹'
        Set.range (offDiagBaseToProdTwo k V Y Z hY hZ).base := by
      rw [Set.mem_preimage, hcproj]
      exact hqimg
    exact (Set.ext_iff.mp (Scheme.Pullback.range_fst (collinearProj k V)
      (offDiagBaseToProdTwo k V Y Z hY hZ)) c).mpr hpre
  refine ⟨t, ?_, ?_⟩
  · rw [incidenceVarietyToProj, Scheme.Hom.comp_apply, ht, collinearProj₃,
      Scheme.Hom.comp_apply, hc, h3]
  · have hbase : (offDiagBaseToProdTwo k V Y Z hY hZ).base
        ((offDiagIncidenceVarietyToBase k V Y Z hY hZ).base t) =
        (collinearProj k V).base
          ((incidenceVarietyToCollinear k V (offDiagBaseToProdTwo k V Y Z hY hZ)).base t) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        (isPullback_incidenceVariety k V (offDiagBaseToProdTwo k V Y Z hY hZ)).w]
    rw [offDiagIncidenceFst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hbase, ht, hcproj,
      hqfst]

/-! ### The dimension of a general fibre of `T ⟶ 𝐏(V)` -/

/-- **The general fibre of the off-diagonal incidence variety over `𝐏(V)`.** For a vector space
of dimension `n + 1` the fibres of `T ⟶ 𝐏(V)` over a nonempty Zariski open subset of `𝐏(V)` all
satisfy `dim T_p + n ≤ dim Y + dim Z + 1`.

This is [Stacks, Tag 0B2L] applied to `T ⟶ 𝐏(V)` through
`AlgebraicGeometry.exists_isOpen_forall_topologicalKrullDim_fiber_add_le_of_ne_top`, whose
hypotheses on the source are only that its space be Noetherian and that the morphism be
quasi-compact. -/
public theorem exists_isOpen_forall_topologicalKrullDim_fiber_incidenceVarietyToProj_add_le
    [IsAlgClosed k] {n : ℕ} (hn : Module.finrank k V = n + 1) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧ ∀ p ∈ U,
      topologicalKrullDim ((incidenceVarietyToProj k V
          (offDiagBaseToProdTwo k V Y Z hY hZ)).fiber p) + (n : WithBot ℕ∞) ≤
        topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have hPdim : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  -- the bound on the source is finite
  have hle : ∀ W : Set (projectiveSpaceOfModule k V), topologicalKrullDim ↥W ≤ (n : WithBot ℕ∞) :=
    fun W => by
      rw [← hPdim, ← topologicalKrullDim_univ (X := projectiveSpaceOfModule k V)]
      exact topologicalKrullDim_le_of_subset (Set.subset_univ W)
  have hfin : topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ≠ ⊤ := by
    have h1 : topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ≤
        ((n + n + 1 : ℕ) : WithBot ℕ∞) := by
      push_cast
      exact add_le_add (add_le_add (hle Y) (hle Z)) le_rfl
    refine ne_top_of_le_ne_top ?_ h1
    exact fun htop => ENat.natCast_ne_top (n + n + 1) (WithBot.coe_eq_top.mp htop)
  exact exists_isOpen_forall_topologicalKrullDim_fiber_add_le_of_ne_top k
    (offDiagIncidenceVarietyToSpec k V Y Z hY hZ) (projectiveSpaceOfModuleToSpec k V)
    (incidenceVarietyToProj k V (offDiagBaseToProdTwo k V Y Z hY hZ))
    (incidenceVarietyToProj_comp_toSpec k V Y Z hY hZ) hfin
    (topologicalKrullDim_offDiagIncidenceVariety_le k V Y Z hY hZ) hPdim

/-! ### The tag -/

include hY hZ in
/-- **The decomposition and the dimension bound, for `Y ∪ Z` not all of `𝐏(V)`.** Let `V` be a
vector space of dimension `n + 1` over an algebraically closed field and let `Y, Z ⊆ 𝐏(V)` be
closed subsets whose union is not all of `𝐏(V)`. There is a nonempty Zariski open `U ⊆ 𝐏(V)`
such that for every closed point `p ∈ U`

`Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E`

with `E ⊆ Y` closed and `dim E ≤ dim Y + dim Z + 1 - n`.

The subset `E` produced is the closure of `(Y ∖ Z) ∩ r_p^{-1}(r_p(Z))`, and its dimension is
bounded by that of the fibre over `p` of the incidence variety
`T = {(y, z, p) : y ∈ Y ∖ Z, z ∈ Z, p on the line joining y and z}`, which the general-fibre
bound makes at most `dim Y + dim Z + 1 - n`.

The hypothesis is relaxed to `Y ≠ 𝐏(V)` alone in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq_of_ne_univ`.
It cannot be dropped altogether:
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_isOpen_inter_projectionCone_univ_eq`
shows that for `Y = Z = 𝐏(V)` the conclusion fails over every nonempty open subset. -/
public theorem exists_isOpen_inter_projectionCone_eq_of_union_ne_univ [IsAlgClosed k]
    {n : ℕ} (hn : Module.finrank k V = n + 1) (hYZ : Y ∪ Z ≠ Set.univ) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Y ∧
          topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
            topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ∧
          Y ∩ projectionCone k V p Z = (Y ∩ Z) ∪ E := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  obtain ⟨U₀, hU₀open, hU₀ne, hU₀⟩ :=
    exists_isOpen_forall_topologicalKrullDim_fiber_incidenceVarietyToProj_add_le k V Y Z hY hZ hn
  refine ⟨U₀ ∩ (Y ∪ Z)ᶜ, hU₀open.inter (hY.union hZ).isOpen_compl, ?_, ?_⟩
  · -- `𝐏(V)` is irreducible, so two nonempty open subsets meet
    exact nonempty_preirreducible_inter hU₀open (hY.union hZ).isOpen_compl hU₀ne
      (Set.nonempty_compl.mpr hYZ)
  intro p hp hpc
  obtain ⟨hpU₀, hpYZ⟩ := hp
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hpYZ
  obtain ⟨hpY, hpZ⟩ := hpYZ
  rcases subsingleton_or_nontrivial ↥(pointSubmodule k V p) with hWs | hWnt
  · -- `p` has no hyperplane, so `𝐏(V)` is the single point `p` and `Y` is empty
    have hbot : pointSubmodule k V p = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      simpa using congrArg Subtype.val
        (Subsingleton.elim (⟨x, hx⟩ : ↥(pointSubmodule k V p)) 0)
    have huniv : (Set.univ : Set (projectiveSpaceOfModule k V)) = {p} := by
      rw [← linearSubspace_pointSubmodule k V p hpc, hbot, linearSubspace_bot]
    have hYempty : Y = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hpY ?_
      have hx1 : x ∈ ({p} : Set (projectiveSpaceOfModule k V)) := by
        rw [← huniv]; trivial
      exact Set.mem_singleton_iff.mp hx1 ▸ hx
    exact ⟨∅, isClosed_empty, Set.empty_subset _, topologicalKrullDim_empty_add_le k V n _,
      by simp [hYempty]⟩
  -- the cone is the trace on the complement of `p` of a closed subset of `𝐏(V)`
  have hdisj : Disjoint Z (linearSubspace k V (pointSubmodule k V p)) := by
    rw [linearSubspace_pointSubmodule k V p hpc]
    exact Set.disjoint_singleton_right.mpr hpZ
  have hKclosed := isClosed_image_projection k V (pointSubmodule k V p) hZ hdisj
  have hpre : IsClosed ((projection k V (pointSubmodule k V p)).base ⁻¹'
      ((projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' Z))) :=
    hKclosed.preimage (Scheme.Hom.continuous (projection k V (pointSubmodule k V p)))
  obtain ⟨C, hCclosed, hCeq⟩ :=
    (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isInducing.isClosed_iff.mp
      hpre
  have hcone : projectionCone k V p Z = C ∩ {p}ᶜ := by
    rw [projectionCone, ← hCeq, Set.image_preimage_eq_inter_range,
      range_projectionDomain_ι_base k V hpc]
  have hYcone : Y ∩ projectionCone k V p Z = Y ∩ C := by
    rw [hcone]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun hx => hpY (hx ▸ h.1)⟩⟩
  have hYconeClosed : IsClosed (Y ∩ projectionCone k V p Z) := by
    rw [hYcone]; exact hY.inter hCclosed
  -- the closed subset `E`
  refine ⟨closure ((Y \ Z) ∩ projectionCone k V p Z), isClosed_closure,
    closure_minimal (fun x hx => hx.1.1) hY, ?_, ?_⟩
  · -- the dimension bound
    set f := incidenceVarietyToProj k V (offDiagBaseToProdTwo k V Y Z hY hZ) with hf
    set F := f.base ⁻¹' {p} with hF
    have hFclosed : IsClosed F := hpc.preimage (Scheme.Hom.continuous f)
    -- every closed point of the difference is in the image of the fibre
    have hsubimg : ((Y \ Z) ∩ projectionCone k V p Z) ∩
        closedPoints (projectiveSpaceOfModule k V) ⊆
          (offDiagIncidenceFst k V Y Z hY hZ).base '' F := by
      rintro x ⟨⟨⟨hxY, hxZ⟩, hxcone⟩, hxcl⟩
      rw [mem_closedPoints_iff] at hxcl
      obtain ⟨z, hzZ, hzcl, hzL⟩ :=
        exists_isClosed_mem_inter_linearSubspace_lineSubmodule k V hZ hxcone
      have hpx : p ≠ x := fun h => hpY (h ▸ hxY)
      have hzx : z ≠ x := fun h => hxZ (h ▸ hzZ)
      have hpline : p ∈ linearSubspace k V (lineSubmodule k V x z) := by
        rw [lineSubmodule_comm]
        exact mem_linearSubspace_lineSubmodule_swap k V hpc hzcl hxcl hpx hzx hzL
      obtain ⟨t, htp, htx⟩ := exists_point_offDiagIncidenceVariety k V Y Z hY hZ
        hxcl hzcl hxY hxZ hzZ (Ne.symm hzx) hpline
      exact ⟨t, htp, htx⟩
    have hlc : IsLocallyClosed ((Y \ Z) ∩ projectionCone k V p Z) := by
      have hrw : (Y \ Z) ∩ projectionCone k V p Z =
          (Y ∩ projectionCone k V p Z) ∩ Zᶜ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
        tauto
      rw [hrw]
      exact hYconeClosed.isLocallyClosed.inter hZ.isOpen_compl.isLocallyClosed
    have hEle : topologicalKrullDim ↥(closure ((Y \ Z) ∩ projectionCone k V p Z)) ≤
        topologicalKrullDim ↥F := by
      have h1 : closure ((Y \ Z) ∩ projectionCone k V p Z) ⊆
          closure ((offDiagIncidenceFst k V Y Z hY hZ).base '' F) := by
        rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure hlc]
        exact closure_mono hsubimg
      refine le_trans (topologicalKrullDim_le_of_subset h1) ?_
      exact topologicalKrullDim_closure_image_le k (offDiagIncidenceFst k V Y Z hY hZ)
        (offDiagIncidenceVarietyToSpec k V Y Z hY hZ) (projectiveSpaceOfModuleToSpec k V)
        (offDiagIncidenceFst_comp_toSpec k V Y Z hY hZ) hFclosed
    have hFdim : topologicalKrullDim ↥F = topologicalKrullDim (f.fiber p) :=
      ((f.fiberHomeo p).isHomeomorph.topologicalKrullDim_eq).symm
    refine le_trans (add_le_add (hEle.trans (le_of_eq hFdim)) (le_refl (n : WithBot ℕ∞))) ?_
    exact hU₀ p hpU₀
  · -- the decomposition
    refine Set.Subset.antisymm (fun x hx => ?_) ?_
    · by_cases hxZ : x ∈ Z
      · exact Or.inl ⟨hx.1, hxZ⟩
      · exact Or.inr (subset_closure ⟨⟨hx.1, hxZ⟩, hx.2⟩)
    refine Set.union_subset (Set.subset_inter Set.inter_subset_left fun x hx => ?_) ?_
    · -- a point of `Z` other than `p` lies in the cone, being its own image
      obtain ⟨x', hx'⟩ : x ∈ Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := by
        rw [range_projectionDomain_ι_base k V hpc]
        exact fun h => hpY (Set.mem_singleton_iff.mp h ▸ hx.1)
      exact ⟨x', ⟨x', by rw [Set.mem_preimage, hx']; exact hx.2, rfl⟩, hx'⟩
    · exact closure_minimal (fun x hx => ⟨hx.1.1, hx.2⟩) hYconeClosed

/-! ### The weakest hypothesis under which the decomposition holds -/

include hY hZ in
/-- **The decomposition and the dimension bound, for `Y` not all of `𝐏(V)`.** Let `V` be a vector
space of dimension `n + 1` over an algebraically closed field, let `Y, Z ⊆ 𝐏(V)` be closed
subsets and let `Y ≠ 𝐏(V)`. There is a nonempty Zariski open `U ⊆ 𝐏(V)` such that for every
closed point `p ∈ U`

`Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E`

with `E ⊆ Y` closed and `dim E ≤ dim Y + dim Z + 1 - n`.

Nothing is asked of `Z`. When `Z` too is a proper closed subset, `𝐏(V)` is irreducible and so
`Y ∪ Z` is again a proper closed subset, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq_of_union_ne_univ`.
When `Z = 𝐏(V)` the projection away from `p` is surjective, so `r_p^{-1}(r_p(Z))` is the whole of
`𝐏(V) ∖ {p}`; taking `U` to be the complement of `Y` makes its intersection with `Y` the whole of
`Y`, and `E = ∅` serves.

The hypothesis `Y ≠ 𝐏(V)` cannot be dropped:
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_isOpen_inter_projectionCone_univ_eq`
shows that for `Y = Z = 𝐏(V)` no nonempty open has the asserted property. -/
public theorem exists_isOpen_inter_projectionCone_eq_of_ne_univ [IsAlgClosed k]
    {n : ℕ} (hn : Module.finrank k V = n + 1) (hYuniv : Y ≠ Set.univ) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Y ∧
          topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
            topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ∧
          Y ∩ projectionCone k V p Z = (Y ∩ Z) ∪ E := by
  by_cases hZuniv : Z = Set.univ
  · -- the projection away from `p` is surjective, so the cone is the complement of `p`
    subst hZuniv
    refine ⟨Yᶜ, hY.isOpen_compl, Set.nonempty_compl.mpr hYuniv, ?_⟩
    intro p hpY hpc
    refine ⟨∅, isClosed_empty, Set.empty_subset _, topologicalKrullDim_empty_add_le k V n _, ?_⟩
    · have hcone : projectionCone k V p Set.univ =
          ({p}ᶜ : Set (projectiveSpaceOfModule k V)) := by
        rw [projectionCone, Set.preimage_univ, Set.image_univ, Set.preimage_range,
          Set.image_univ, range_projectionDomain_ι_base k V hpc]
      rw [hcone, Set.inter_univ, Set.union_empty]
      exact Set.inter_eq_left.mpr fun x hx hxp => hpY (Set.mem_singleton_iff.mp hxp ▸ hx)
  · -- two proper closed subsets of the irreducible `𝐏(V)` have proper closed union
    refine exists_isOpen_inter_projectionCone_eq_of_union_ne_univ k V Y Z hY hZ hn
      (Set.nonempty_compl.mp ?_)
    rw [Set.compl_union]
    exact nonempty_preirreducible_inter hY.isOpen_compl hZ.isOpen_compl
      (Set.nonempty_compl.mpr hYuniv) (Set.nonempty_compl.mpr hZuniv)

/-- **For `Y = Z = 𝐏(V)` the asserted decomposition holds over no nonempty open at all.** The
projection away from `p` is defined on the complement of `p`, so `r_p^{-1}(r_p(Z))` never
contains `p`, while the right-hand side `(Y ∩ Z) ∪ E` contains it as soon as `p ∈ Y ∩ Z`. For
`Y = Z = 𝐏(V)` that is every point, and `𝐏(V)` is a Jacobson space, so every nonempty open
carries a closed point at which the identity fails. No choice of `E` repairs it, the defect
being on the side of the equation `E` does not appear on, and it is not a defect of the
dimension bound: the bound here reads `dim E + n ≤ n + n + 1` and is satisfied by every `E`.

The `Y` and `Z` taken here are closed and irreducible, which the statement records, and
`𝐏(V)` is integral, so they are closed subvarieties of `𝐏(V)` and not a reducible or
non-reduced generalization of one. A hypothesis excluding `Y = 𝐏(V)` is therefore forced, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq_of_ne_univ`
carries one. -/
public theorem not_exists_isOpen_inter_projectionCone_univ_eq [IsAlgClosed k] {n : ℕ} :
    IsClosed (Set.univ : Set (projectiveSpaceOfModule k V)) ∧
      IsIrreducible (Set.univ : Set (projectiveSpaceOfModule k V)) ∧
      ¬∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
        ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
          ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Set.univ ∧
            topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
              topologicalKrullDim ↥(Set.univ : Set (projectiveSpaceOfModule k V)) +
                topologicalKrullDim ↥(Set.univ : Set (projectiveSpaceOfModule k V)) + 1 ∧
            Set.univ ∩ projectionCone k V p Set.univ =
              (Set.univ ∩ Set.univ : Set (projectiveSpaceOfModule k V)) ∪ E := by
  refine ⟨isClosed_univ, IrreducibleSpace.isIrreducible_univ (projectiveSpaceOfModule k V), ?_⟩
  rintro ⟨U, hUopen, hUne, hU⟩
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  obtain ⟨p, hpU, hpc⟩ := nonempty_inter_closedPoints hUne hUopen.isLocallyClosed
  obtain ⟨E, -, -, -, hEeq⟩ := hU p hpU (mem_closedPoints_iff.mp hpc)
  have hp : p ∈ (Set.univ ∩ Set.univ : Set (projectiveSpaceOfModule k V)) ∪ E :=
    Or.inl ⟨trivial, trivial⟩
  rw [← hEeq] at hp
  obtain ⟨x, -, hx⟩ := hp.2
  have hmem : p ∈ Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := ⟨x, hx⟩
  rw [range_projectionDomain_ι_base k V (mem_closedPoints_iff.mp hpc)] at hmem
  exact hmem rfl

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
