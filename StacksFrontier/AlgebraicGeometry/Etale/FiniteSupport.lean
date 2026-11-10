module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Sections with finite support, and the finite-support direct image

Let `f : X ⟶ Y` be a morphism of a big étale site and let `F` be an abelian sheaf on the small
étale site of `X`. For an object `V` of the small étale site of `Y` the fibre product
`X_V = V ×_Y X` carries the locally closed subsets which support a subscheme structure finite
over `V`; these form a partially ordered set, each one carries the abelian group `H_Z(F)` of
sections of `F` supported on it, and the inclusions of supports induce maps of those groups.
The colimit of that system is the group of finite-support sections over `V`, and as `V` varies
it assembles into the presheaf direct image with finite support `f_{p!}F`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.openObjectMap` — the morphism of the small étale site induced
  by a Zariski open mapped into another one.
* `AlgebraicGeometry.SmallEtale.IsFiniteSupport` and
  `AlgebraicGeometry.SmallEtale.FiniteSupport` — the eligible supports: the locally closed
  subsets of `X_V` which support a subscheme structure finite over `V`.
* `AlgebraicGeometry.SmallEtale.finiteSupportDiagram` — the diagram `Z ↦ H_Z(F)` of supported
  sections with the transition maps of Stacks 0F6F, and
  `AlgebraicGeometry.SmallEtale.finiteSupportSections` its colimit.
* `AlgebraicGeometry.SmallEtale.FiniteSupportBaseChange` and
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange` — the base change of a support and of
  its supported sections along a morphism of the small étale site of `Y`, together with
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChangeCocone`,
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChangeHom` and
  `AlgebraicGeometry.SmallEtale.finiteSupportPresheaf`, the resulting abelian presheaf.
* `AlgebraicGeometry.SmallEtale.finiteSupportDiagramMap` — the action of a morphism of abelian
  sheaves on the diagram of supported sections.
* `AlgebraicGeometry.SmallEtale.FiniteSupportPushforwardSpec` and
  `AlgebraicGeometry.SmallEtale.finiteSupportPushforward` — the direct image with finite
  support `f_{p!}` as a functor to abelian presheaves, characterized by its values and by both
  of its functorial actions on the colimit generators.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupport_isLocallyClosed` — an eligible support is
  locally closed, so `H_Z(F)` is defined for it.
* `AlgebraicGeometry.SmallEtale.finiteSupport_closedWithin` — one eligible support contained in
  another is closed in it, which is what makes the transition maps of Stacks 0F6F available.
* `AlgebraicGeometry.SmallEtale.exists_finiteSupport_sum` — every finite-support section over
  `V` is a finite formal sum `∑ (Z_i, s_i)` of sections supported on eligible supports.
* `AlgebraicGeometry.SmallEtale.isFiniteSupport_preimage` and
  `AlgebraicGeometry.SmallEtale.supportOpen_preimage_subset` — the inverse image of an
  eligible support is eligible, and its canonical open lies in the inverse image of the
  canonical open.
* `AlgebraicGeometry.SmallEtale.finiteSupportBaseChangeHom_ι` — the restriction map of the
  finite-support presheaf on a colimit generator.
* `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_sections_naturality`,
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_support_comp`,
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_arrow_comp`,
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_sections_comp`,
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_sheaf_naturality`,
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_support_id` and
  `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_sections_id` — the compatibilities of
  base change which make the presheaf and the functor well defined.

## Implementation notes

An eligible support is recorded as a *subset* together with the existence of a subscheme
structure on it which is finite over `V`, rather than as a chosen subscheme: the group
`H_Z(F)` of Stacks 0F6F depends only on the subset, so this keeps the index a partially
ordered set and the colimit of the source an honest colimit over inclusions. Closedness of one
support in another, which the source deduces from finiteness of `Z → V` and separatedness of
`Z' → V`, is proved here by base-changing the two immersions against each other.

Base change of supports is only functorial up to the propositional equality
`support = preimage`, not up to definitional equality, so the compatibilities of
`finiteSupportBaseChange` are stated for an arbitrary element of `FiniteSupportBaseChange` and
transported along that equality; this is why several of them are heterogeneous equalities.
The indexing posets are only known to be `v`-small by hypothesis, so the smallness is carried
as an assumption rather than derived, as in Stacks 0F6M itself where the colimit is a quotient
of finite formal sums.

## References

* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6J](https://stacks.math.columbia.edu/tag/0F6J)
* [Stacks Project, Tag 0F6F](https://stacks.math.columbia.edu/tag/0F6F)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section OpenObjectMap

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A Zariski open of an object of the small étale site mapped by a morphism of the site into
a Zariski open of the target induces a morphism of the corresponding objects of the site. -/
public def openObjectMap {W W' : SmallEtale B S hS} (φ : W' ⟶ W)
    (U : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (U' : ((SmallEtale.toScheme B S hS).obj W').Opens)
    (hU : (U' : Set ((SmallEtale.toScheme B S hS).obj W')) ⊆
      ((SmallEtale.toScheme B S hS).map φ).base ⁻¹' U) :
    openObject B S hS W' U' ⟶ openObject B S hS W U :=
  factorThroughOpenObject B S hS _ W (openObjectι B S hS W' U' ≫ φ) U (by
    rintro x ⟨y, rfl⟩
    have hy : ((SmallEtale.toScheme B S hS).map (openObjectι B S hS W' U')).base y ∈
        (U' : Set ((SmallEtale.toScheme B S hS).obj W')) := by
      rw [← openObjectι_range B S hS W' U']
      exact ⟨y, rfl⟩
    simpa only [Functor.map_comp, Scheme.Hom.comp_apply, Set.mem_preimage] using hU hy)

/-- The induced morphism of objects of the small étale site is compatible with the two open
inclusions. -/
public theorem openObjectMap_fac {W W' : SmallEtale B S hS} (φ : W' ⟶ W)
    (U : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (U' : ((SmallEtale.toScheme B S hS).obj W').Opens)
    (hU : (U' : Set ((SmallEtale.toScheme B S hS).obj W')) ⊆
      ((SmallEtale.toScheme B S hS).map φ).base ⁻¹' U) :
    openObjectMap B S hS φ U U' hU ≫ openObjectι B S hS W U =
      openObjectι B S hS W' U' ≫ φ :=
  factorThroughOpenObject_fac B S hS _ W (openObjectι B S hS W' U' ≫ φ) U _

/-- On schemes, the morphism induced by a containment of Zariski opens is the unique
factorization through the two open immersions. -/
public theorem openObjectMap_map {W W' : SmallEtale B S hS} (φ : W' ⟶ W)
    (U : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (U' : ((SmallEtale.toScheme B S hS).obj W').Opens)
    (hU : (U' : Set ((SmallEtale.toScheme B S hS).obj W')) ⊆
      ((SmallEtale.toScheme B S hS).map φ).base ⁻¹' U) :
    (SmallEtale.toScheme B S hS).map (openObjectMap B S hS φ U U' hU) ≫ U.ι =
      U'.ι ≫ (SmallEtale.toScheme B S hS).map φ := by
  have h := congrArg (SmallEtale.toScheme B S hS).map
    (openObjectMap_fac B S hS φ U U' hU)
  rwa [Functor.map_comp, Functor.map_comp, openObjectι_map, openObjectι_map] at h

end OpenObjectMap

section ColimitSpan

variable {J : Type*} [Category J] (D : J ⥤ AddCommGrpCat.{v}) [HasColimit D]

/-- The element of a colimit of abelian groups attached to an index of the diagram together
with an element of the group sitting over that index. -/
private def colimitGen (p : Σ j : J, ↥(D.obj j)) : ↥(colimit D) :=
  colimit.ι D p.1 p.2

/-- The subgroup of a colimit of abelian groups made of the finite sums of elements coming
from the groups of the diagram. -/
private def colimitSpan : AddSubgroup ↥(colimit D) where
  carrier := {x | ∃ (n : ℕ) (p : Fin n → Σ j : J, ↥(D.obj j)), x = ∑ i, colimitGen D (p i)}
  zero_mem' := ⟨0, fun i => i.elim0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, p, rfl⟩ ⟨m, q, rfl⟩
    refine ⟨n + m, Fin.append p q, ?_⟩
    rw [Fin.sum_univ_add]
    simp
  neg_mem' := by
    rintro x ⟨n, p, rfl⟩
    refine ⟨n, fun i => ⟨(p i).1, -(p i).2⟩, ?_⟩
    simp [colimitGen]

/-- The cocone on the diagram whose vertex is the subgroup of finite sums of elements of the
groups of the diagram. -/
private abbrev colimitSpanCocone : Cocone D where
  pt := AddCommGrpCat.of ↥(colimitSpan D)
  ι :=
  { app := fun j => AddCommGrpCat.ofHom
      { toFun := fun x => ⟨colimit.ι D j x, ⟨1, fun _ => ⟨j, x⟩, by simp [colimitGen]⟩⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun x y => Subtype.ext (by simp) }
    naturality := fun j j' u => by
      apply AddCommGrpCat.hom_ext
      ext x
      apply Subtype.ext
      simp }

/-- The images of the colimit inclusions generate a colimit of abelian groups, because the
subgroup they span receives the universal map of the colimit. -/
private theorem colimitSpan_eq_top : colimitSpan D = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).2 fun x => ?_
  have h : colimit.desc D (colimitSpanCocone D) ≫
      AddCommGrpCat.ofHom (colimitSpan D).subtype = 𝟙 (colimit D) := by
    refine colimit.hom_ext fun j => ?_
    rw [← Category.assoc, colimit.ι_desc, Category.comp_id]
    exact AddCommGrpCat.hom_ext rfl
  have hx : (AddCommGrpCat.ofHom (colimitSpan D).subtype)
      ((colimit.desc D (colimitSpanCocone D)) x) = x := by
    rw [← CategoryTheory.comp_apply, h, CategoryTheory.id_apply]
  rw [← hx]
  exact (colimit.desc D (colimitSpanCocone D) x).2

/-- Every element of a colimit of abelian groups is a finite sum of images of elements of the
groups of the diagram under the colimit inclusions. -/
private theorem exists_sum_colimit_ι (x : ↥(colimit D)) :
    ∃ (n : ℕ) (j : Fin n → J) (t : ∀ i, ↥(D.obj (j i))),
      x = ∑ i, colimit.ι D (j i) (t i) := by
  obtain ⟨n, p, hp⟩ := (colimitSpan_eq_top D).ge (AddSubgroup.mem_top x)
  exact ⟨n, fun i => (p i).1, fun i => (p i).2, hp⟩

end ColimitSpan

section FiniteSupport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The base change `X_V = V ×_Y X` of `X` along an object `V` of the small étale site of
`Y`, as an object of the small étale site of `X`. -/
public abbrev baseChange (V : SmallEtale B Y.obj Y.property) :
    SmallEtale B X.obj X.property :=
  (smallEtaleBaseChange B f).obj V

/-- **Stacks 0F6M.** A locally closed subset of `X_V` which carries a subscheme structure
finite over `V`. These are the supports the colimit of Stacks 0F6M is taken over. -/
public def IsFiniteSupport (V : SmallEtale B Y.obj Y.property)
    (E : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))) : Prop :=
  ∃ (Z : Scheme.{u})
    (i : Z ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)),
    IsImmersion i ∧
      IsFinite (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) ∧
      Set.range i.base = E

/-- **Stacks 0F6M.** The partially ordered set of supports of `X_V` which are finite over
`V`. -/
@[stacks 0F6M "the index of the colimit"]
public abbrev FiniteSupport (V : SmallEtale B Y.obj Y.property) :=
  {E : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)) //
    IsFiniteSupport B f V E}

/-- The support of a subscheme finite over `V` is locally closed, so the group `H_Z(F)` of
Stacks 0F6F is defined for it. -/
@[stacks 0F6M "local closedness of the supports"]
public theorem finiteSupport_isLocallyClosed (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) : IsLocallyClosed E.1 := by
  obtain ⟨Z, i, hi, _, he⟩ := E.property
  let : IsImmersion i := hi
  exact he ▸ i.isLocallyClosed_range

/-- One support finite over `V` contained in another is closed in it. This is the relation
making the transition maps of Stacks 0F6F available on the index, and in the source it is the
observation that `Z → Z'` is a closed immersion because `Z → V` is finite and `Z' → V` is
separated. -/
@[stacks 0F6M "closedness of the transition inclusions"]
public theorem finiteSupport_closedWithin (V : SmallEtale B Y.obj Y.property)
    (E E' : FiniteSupport B f V) (h : E ≤ E') :
    IsClosed ((Subtype.val : E'.1 → _) ⁻¹' E.1) := by
  obtain ⟨Z, i, hi, hfin, hrange⟩ := E.property
  obtain ⟨Z', i', hi', hfin', hrange'⟩ := E'.property
  let : IsImmersion i := hi
  let : IsImmersion i' := hi'
  let : IsFinite (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := hfin
  let : IsFinite (i' ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := hfin'
  have : IsImmersion (pullback.fst i i') := inferInstance
  have : IsImmersion (pullback.snd i i') := inferInstance
  have hrange₁ : Set.range (pullback.fst i i').base = Set.univ := by
    rw [Scheme.Pullback.range_fst]
    refine Set.eq_univ_iff_forall.mpr fun z => ?_
    rw [hrange']
    exact h (hrange ▸ Set.mem_range_self z)
  have : IsClosedImmersion (pullback.fst i i') :=
    IsClosedImmersion.of_isPreimmersion _ (hrange₁ ▸ isClosed_univ)
  have hcomp : pullback.fst i i' ≫ (i ≫ B.inclusion.map (pullback.fst V.obj.hom f)) =
      pullback.snd i i' ≫ (i' ≫ B.inclusion.map (pullback.fst V.obj.hom f)) := by
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  have : IsFinite (pullback.snd i i' ≫ (i' ≫ B.inclusion.map (pullback.fst V.obj.hom f))) := by
    rw [← hcomp]
    infer_instance
  have : IsProper (pullback.snd i i') :=
    IsProper.of_comp _ (i' ≫ B.inclusion.map (pullback.fst V.obj.hom f))
  have : IsClosedImmersion (pullback.snd i i') :=
    IsClosedImmersion.of_isPreimmersion _ (pullback.snd i i').isClosedMap.isClosed_range
  have hclosed : IsClosed (i'.base ⁻¹' E.1) := by
    have hr : Set.range (pullback.snd i i').base = i'.base ⁻¹' E.1 := by
      rw [Scheme.Pullback.range_snd, hrange]
    rw [← hr]
    exact (pullback.snd i i').isClosedEmbedding.isClosed_range
  obtain ⟨C, hC, hCeq⟩ :=
    (Scheme.Hom.isEmbedding i').isInducing.isClosed_iff.1 hclosed
  have hset : (Subtype.val : E'.1 → _) ⁻¹' E.1 = (Subtype.val : E'.1 → _) ⁻¹' C := by
    ext x
    obtain ⟨z, hz⟩ : x.1 ∈ Set.range i'.base := by rw [hrange']; exact x.2
    simp only [Set.mem_preimage, ← hz]
    exact (Set.ext_iff.1 hCeq z).symm
  rw [hset]
  exact hC.preimage continuous_subtype_val

/-- **Stacks 0F6M.** The diagram `Z ↦ H_Z(F)` of supported sections over the supports finite
over `V`, with the transition maps of Stacks 0F6F along the inclusions. -/
@[stacks 0F6M "the diagram of supported sections"]
public def finiteSupportDiagram
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) :
    FiniteSupport B f V ⥤ AddCommGrpCat.{v} where
  obj E := AddCommGrpCat.of
    (supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E))
  map {E E'} h := AddCommGrpCat.ofHom
    (supportedSectionsMap B X.obj X.property F (baseChange B f V) E.1 E'.1
      (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E')
      (leOfHom h) (finiteSupport_closedWithin B f V E E' (leOfHom h)))
  map_id E := AddCommGrpCat.hom_ext <|
    supportedSectionsMap_refl B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)
      (finiteSupport_closedWithin B f V E E (le_refl E))
  map_comp {E E' E''} h k := AddCommGrpCat.hom_ext
    (supportedSectionsMap_comp B X.obj X.property F (baseChange B f V)
      E.1 E'.1 E''.1
      (finiteSupport_isLocallyClosed B f V E)
      (finiteSupport_isLocallyClosed B f V E')
      (finiteSupport_isLocallyClosed B f V E'')
      (leOfHom h) (leOfHom k)
      (finiteSupport_closedWithin B f V E E' (leOfHom h))
      (finiteSupport_closedWithin B f V E' E'' (leOfHom k))
      (finiteSupport_closedWithin B f V E E'' ((leOfHom h).trans (leOfHom k)))).symm

/-- **Stacks 0F6M.** The abelian group of sections with finite support over `V`, namely the
colimit of `H_Z(F)` over the supports finite over `V`. -/
@[stacks 0F6M "the colimit formula"]
public abbrev finiteSupportSections
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    [Small.{v} (FiniteSupport B f V)] : AddCommGrpCat.{v} :=
  colimit (finiteSupportDiagram B f F V)

/-- **Stacks 0F6J.** Every section with finite support over `V` is a finite formal sum
`s = ∑ (Z_i, s_i)`, where each `Z_i` is a support finite over `V` and `s_i ∈ H_{Z_i}(F)`,
the pair `(Z_i, s_i)` standing for the image of `s_i` under the colimit inclusion at `Z_i`. -/
@[stacks 0F6J "the formal sum presentation"]
public theorem exists_finiteSupport_sum
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) [Small.{v} (FiniteSupport B f V)]
    (s : ↥(finiteSupportSections B f F V)) :
    ∃ (n : ℕ) (Z : Fin n → FiniteSupport B f V)
      (t : ∀ i, supportedSections B X.obj X.property F (baseChange B f V) (Z i).1
        (finiteSupport_isLocallyClosed B f V (Z i))),
      s = ∑ i, colimit.ι (finiteSupportDiagram B f F V) (Z i) (t i) :=
  exists_sum_colimit_ι (finiteSupportDiagram B f F V) s

/-- **Stacks 0F6M.** The inverse image of a support finite over `V` along a morphism
`V' ⟶ V` of the small étale site of `Y` is a support finite over `V'`. -/
@[stacks 0F6M "base change of the supports"]
public theorem isFiniteSupport_preimage {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) :
    IsFiniteSupport B f V' (((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base ⁻¹' E.1) := by
  obtain ⟨Z, i, hi, hfin, hrange⟩ := E.property
  let : IsImmersion i := hi
  set p := B.inclusion.map (pullback.fst V.obj.hom f) with hpdef
  set p' := B.inclusion.map (pullback.fst V'.obj.hom f) with hp'def
  let : IsFinite (i ≫ p) := hfin
  set k := (SmallEtale.toScheme B X.obj X.property).map
    ((smallEtaleBaseChange B f).map g) with hkdef
  set gOver := (SmallEtale.inclusion B Y.obj Y.property).map g with hgOverdef
  set gv := B.inclusion.map gOver.left with hgvdef
  have hgu : gOver.left ≫ V.obj.hom = V'.obj.hom := Over.w gOver
  have houter : IsPullback k p' p gv := by
    have hstd : IsPullback (pullback.snd gOver.left (pullback.fst V.obj.hom f))
        (pullback.fst gOver.left (pullback.fst V.obj.hom f))
        (pullback.fst V.obj.hom f) gOver.left :=
      (IsPullback.of_hasPullback gOver.left (pullback.fst V.obj.hom f)).flip
    have houterB : IsPullback ((Over.pullback f).map gOver).left
        (pullback.fst V'.obj.hom f) (pullback.fst V.obj.hom f) gOver.left := by
      refine hstd.of_iso'
        ((pullbackRightPullbackFstIso V.obj.hom f gOver.left).trans
          (pullback.congrHom hgu rfl)).symm
        (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
      · apply pullback.hom_ext
        · simp [Over.pullback_map_left, pullback.map, Category.assoc,
            pullback.congrHom_inv, pullbackRightPullbackFstIso_inv_snd_fst]
        · simp [Over.pullback_map_left, pullback.map, Category.assoc,
            pullback.congrHom_inv, pullbackRightPullbackFstIso_inv_snd_snd]
      · simp [Category.assoc, pullback.congrHom_inv, pullback.map]
    have hk : k = B.inclusion.map ((Over.pullback f).map gOver).left := rfl
    rw [hk]
    exact houterB.map B.inclusion
  have hbig : IsPullback (pullback.fst i k) (pullback.snd i k ≫ p') (i ≫ p) gv :=
    (IsPullback.of_hasPullback i k).paste_vert houter
  refine ⟨pullback i k, pullback.snd i k, inferInstance,
    MorphismProperty.of_isPullback hbig hfin, ?_⟩
  rw [Scheme.Pullback.range_snd, hrange]

/-- The canonical open of the inverse image support sits inside the inverse image of the
canonical open of the original support. -/
public theorem supportOpen_preimage_subset {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) (E' : FiniteSupport B f V')
    (hE' : E'.1 = ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base ⁻¹' E.1) :
    (supportOpen B X.obj X.property (baseChange B f V') E'.1
        (finiteSupport_isLocallyClosed B f V' E') :
      Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V'))) ⊆
      ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map g)).base ⁻¹'
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E) :
          Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))) := by
  have : Etale ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)) :=
    etale_toScheme_map B X.obj X.property ((smallEtaleBaseChange B f).map g)
  have hopen : IsOpenMap ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base :=
    ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).isOpenMap
  intro x hx
  have hx' : x ∈ coborder E'.1 := hx
  rw [hE'] at hx'
  exact hopen.coborder_preimage_subset E.1 hx'

/-- The data produced by base change of a support finite over `V` along `V' ⟶ V`: the
inverse-image support, the induced morphism of the two canonical opens, and the restriction
map on supported sections. -/
public structure FiniteSupportBaseChange
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) where
  /-- The inverse image of the given support. -/
  support : FiniteSupport B f V'
  /-- The inverse image support is the set-theoretic inverse image. -/
  support_eq : support.1 =
    ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base ⁻¹' E.1
  /-- The induced morphism between the canonical opens of the two supports. -/
  openMap :
    openObject B X.obj X.property (baseChange B f V')
      (supportOpen B X.obj X.property (baseChange B f V') support.1
        (finiteSupport_isLocallyClosed B f V' support)) ⟶
    openObject B X.obj X.property (baseChange B f V)
      (supportOpen B X.obj X.property (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E))
  /-- The induced morphism of canonical opens lies over the base change morphism. -/
  openMap_commutes :
    (SmallEtale.toScheme B X.obj X.property).map openMap ≫
      (supportOpen B X.obj X.property (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E)).ι =
      (supportOpen B X.obj X.property (baseChange B f V') support.1
        (finiteSupport_isLocallyClosed B f V' support)).ι ≫
        (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g)
  /-- The induced map on supported sections. -/
  sectionsMap :
    supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E) →+
    supportedSections B X.obj X.property F (baseChange B f V') support.1
      (finiteSupport_isLocallyClosed B f V' support)
  /-- The induced map on supported sections is restriction along the induced morphism of
  canonical opens. -/
  sectionsMap_apply : ∀ s, (sectionsMap s).val = F.obj.map openMap.op s.val

/-- **Stacks 0F6M.** Base change of a support finite over `V` and of its supported sections
along a morphism `V' ⟶ V` of the small étale site of `Y`. The support is the set-theoretic
inverse image and the map on sections is restriction. -/
@[stacks 0F6M "base change of supported sections"]
public def finiteSupportBaseChange
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) : FiniteSupportBaseChange B f F g E := by
  let k := (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g)
  let E' : FiniteSupport B f V' := ⟨k.base ⁻¹' E.1, isFiniteSupport_preimage B f g E⟩
  let U := supportOpen B X.obj X.property (baseChange B f V) E.1
    (finiteSupport_isLocallyClosed B f V E)
  let U' := supportOpen B X.obj X.property (baseChange B f V') E'.1
    (finiteSupport_isLocallyClosed B f V' E')
  have hU : (U' : Set ((SmallEtale.toScheme B X.obj X.property).obj
      (baseChange B f V'))) ⊆ k.base ⁻¹' (U : Set _) :=
    supportOpen_preimage_subset B f g E E' rfl
  let openMap := openObjectMap B X.obj X.property ((smallEtaleBaseChange B f).map g) U U' hU
  have hcomm := openObjectMap_map B X.obj X.property
    ((smallEtaleBaseChange B f).map g) U U' hU
  have hbase (x : (SmallEtale.toScheme B X.obj X.property).obj
      (openObject B X.obj X.property (baseChange B f V') U')) :
      U.ι.base (((SmallEtale.toScheme B X.obj X.property).map openMap).base x) =
        k.base (U'.ι.base x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m.base x) hcomm
  let sectionsMap :
      supportedSections B X.obj X.property F (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E) →+
      supportedSections B X.obj X.property F (baseChange B f V') E'.1
        (finiteSupport_isLocallyClosed B f V' E') :=
    { toFun := fun s => ⟨F.obj.map openMap.op s.val, by
        have hres := supportSection_restrict_subset_preimage B X.obj X.property F
          (openObject B X.obj X.property (baseChange B f V) U)
          (openObject B X.obj X.property (baseChange B f V') U') openMap s.val
        intro x hx
        have hx' : U.ι.base
            (((SmallEtale.toScheme B X.obj X.property).map openMap).base x) ∈ E.1 :=
          (hres.trans (Set.preimage_mono s.property)) hx
        change k.base (U'.ι.base x) ∈ E.1
        rw [← hbase x]
        exact hx'⟩
      map_zero' := Subtype.ext (F.obj.map openMap.op).hom.map_zero
      map_add' := fun s t => Subtype.ext ((F.obj.map openMap.op).hom.map_add s.val t.val) }
  exact FiniteSupportBaseChange.mk E' rfl openMap hcomm sectionsMap (fun _ => rfl)

/-- Base change on supported sections commutes with the transitions along inclusions of
supports. -/
public theorem finiteSupportBaseChange_sections_naturality
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    {E E' : FiniteSupport B f V} (h : E ≤ E')
    (d : FiniteSupportBaseChange B f F g E)
    (d' : FiniteSupportBaseChange B f F g E') :
    d'.sectionsMap.comp
        (supportedSectionsMap B X.obj X.property F (baseChange B f V)
          E.1 E'.1 (finiteSupport_isLocallyClosed B f V E)
          (finiteSupport_isLocallyClosed B f V E') h
          (finiteSupport_closedWithin B f V E E' h)) =
      (supportedSectionsMap B X.obj X.property F (baseChange B f V')
          d.support.1 d'.support.1
          (finiteSupport_isLocallyClosed B f V' d.support)
          (finiteSupport_isLocallyClosed B f V' d'.support)
          (by
            change d.support.1 ⊆ d'.support.1
            rw [d.support_eq, d'.support_eq]
            exact Set.preimage_mono h)
          (finiteSupport_closedWithin B f V' d.support d'.support (by
            change d.support.1 ⊆ d'.support.1
            rw [d.support_eq, d'.support_eq]
            exact Set.preimage_mono h))).comp d.sectionsMap := by
  have hbar : d.support.1 ≤ d'.support.1 := by
    rw [d.support_eq, d'.support_eq]
    exact Set.preimage_mono h
  have hcbar := finiteSupport_closedWithin B f V' d.support d'.support hbar
  let t := openObjectHomOfLE B X.obj X.property (baseChange B f V)
    (supportOpen_antitone B X.obj X.property (baseChange B f V)
      E.1 E'.1 (finiteSupport_isLocallyClosed B f V E)
      (finiteSupport_isLocallyClosed B f V E') h
      (finiteSupport_closedWithin B f V E E' h))
  let t' := openObjectHomOfLE B X.obj X.property (baseChange B f V')
    (supportOpen_antitone B X.obj X.property (baseChange B f V')
      d.support.1 d'.support.1 (finiteSupport_isLocallyClosed B f V' d.support)
      (finiteSupport_isLocallyClosed B f V' d'.support) hbar hcbar)
  let U := supportOpen B X.obj X.property (baseChange B f V) E.1
    (finiteSupport_isLocallyClosed B f V E)
  let U' := supportOpen B X.obj X.property (baseChange B f V') d.support.1
    (finiteSupport_isLocallyClosed B f V' d.support)
  let U'' := supportOpen B X.obj X.property (baseChange B f V') d'.support.1
    (finiteSupport_isLocallyClosed B f V' d'.support)
  let q := (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g)
  have ht : (SmallEtale.toScheme B X.obj X.property).map t ≫ U.ι =
      (supportOpen B X.obj X.property (baseChange B f V) E'.1
        (finiteSupport_isLocallyClosed B f V E')).ι := by
    rw [openObjectHomOfLE_map, Scheme.homOfLE_ι]
  have ht' : (SmallEtale.toScheme B X.obj X.property).map t' ≫ U'.ι = U''.ι := by
    rw [openObjectHomOfLE_map, Scheme.homOfLE_ι]
  have hd : (SmallEtale.toScheme B X.obj X.property).map d.openMap ≫ U.ι = U'.ι ≫ q :=
    d.openMap_commutes
  have hd' : (SmallEtale.toScheme B X.obj X.property).map d'.openMap ≫
      (supportOpen B X.obj X.property (baseChange B f V) E'.1
        (finiteSupport_isLocallyClosed B f V E')).ι = U''.ι ≫ q :=
    d'.openMap_commutes
  have hgeom : d'.openMap ≫ t = t' ≫ d.openMap := by
    apply (SmallEtale.toScheme B X.obj X.property).map_injective
    simp only [Functor.map_comp]
    apply (cancel_mono U.ι).1
    rw [Category.assoc, ht, hd', ← ht', Category.assoc, Category.assoc, hd]
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  change (d'.sectionsMap
      (supportedSectionsMap B X.obj X.property F (baseChange B f V)
        E.1 E'.1 (finiteSupport_isLocallyClosed B f V E)
        (finiteSupport_isLocallyClosed B f V E') h
        (finiteSupport_closedWithin B f V E E' h) s)).val =
    (supportedSectionsMap B X.obj X.property F (baseChange B f V')
      d.support.1 d'.support.1
      (finiteSupport_isLocallyClosed B f V' d.support)
      (finiteSupport_isLocallyClosed B f V' d'.support) hbar hcbar
      (d.sectionsMap s)).val
  rw [d'.sectionsMap_apply, supportedSectionsMap_apply, supportedSectionsMap_apply,
    d.sectionsMap_apply]
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← ConcreteCategory.comp_apply,
    ← F.obj.map_comp]
  simp only [← op_comp]
  rw [hgeom]

/-- The cocone on the diagram over `V` with vertex the finite-support sections over `V`,
given by base change of supports and restriction of sections. -/
public abbrev finiteSupportBaseChangeCocone
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    [Small.{v} (FiniteSupport B f V)] [Small.{v} (FiniteSupport B f V')] :
    Cocone (finiteSupportDiagram B f F V) := by
  refine {
    pt := finiteSupportSections B f F V'
    ι := {
      app := fun E =>
        AddCommGrpCat.ofHom (finiteSupportBaseChange B f F g E).sectionsMap ≫
          colimit.ι (finiteSupportDiagram B f F V')
            (finiteSupportBaseChange B f F g E).support
      naturality := ?_
    }
  }
  intro E E' h
  let d := finiteSupportBaseChange B f F g E
  let d' := finiteSupportBaseChange B f F g E'
  let sourceMap := supportedSectionsMap B X.obj X.property F
    (baseChange B f V) E.1 E'.1
    (finiteSupport_isLocallyClosed B f V E)
    (finiteSupport_isLocallyClosed B f V E') (leOfHom h)
    (finiteSupport_closedWithin B f V E E' (leOfHom h))
  have hbar : d.support ≤ d'.support := by
    change d.support.1 ⊆ d'.support.1
    rw [d.support_eq, d'.support_eq]
    exact Set.preimage_mono (leOfHom h)
  let targetMap := supportedSectionsMap B X.obj X.property F
    (baseChange B f V') d.support.1 d'.support.1
    (finiteSupport_isLocallyClosed B f V' d.support)
    (finiteSupport_isLocallyClosed B f V' d'.support) hbar
    (finiteSupport_closedWithin B f V' d.support d'.support hbar)
  have hcat : AddCommGrpCat.ofHom sourceMap ≫ AddCommGrpCat.ofHom d'.sectionsMap =
      AddCommGrpCat.ofHom d.sectionsMap ≫ AddCommGrpCat.ofHom targetMap :=
    AddCommGrpCat.hom_ext <| finiteSupportBaseChange_sections_naturality B f F g (leOfHom h) d d'
  have htarget' : AddCommGrpCat.ofHom targetMap ≫
      colimit.ι (finiteSupportDiagram B f F V') d'.support =
        colimit.ι (finiteSupportDiagram B f F V') d.support := by
    change (finiteSupportDiagram B f F V').map (homOfLE hbar) ≫ _ = _
    exact colimit.w (finiteSupportDiagram B f F V') (homOfLE hbar)
  change AddCommGrpCat.ofHom sourceMap ≫
      (AddCommGrpCat.ofHom d'.sectionsMap ≫
        colimit.ι (finiteSupportDiagram B f F V') d'.support) =
    AddCommGrpCat.ofHom d.sectionsMap ≫
      colimit.ι (finiteSupportDiagram B f F V') d.support
  calc
    _ = (AddCommGrpCat.ofHom sourceMap ≫ AddCommGrpCat.ofHom d'.sectionsMap) ≫
        colimit.ι (finiteSupportDiagram B f F V') d'.support :=
          (Category.assoc _ _ _).symm
    _ = (AddCommGrpCat.ofHom d.sectionsMap ≫ AddCommGrpCat.ofHom targetMap) ≫
        colimit.ι (finiteSupportDiagram B f F V') d'.support := by rw [hcat]
    _ = AddCommGrpCat.ofHom d.sectionsMap ≫
        (AddCommGrpCat.ofHom targetMap ≫
          colimit.ι (finiteSupportDiagram B f F V') d'.support) := Category.assoc _ _ _
    _ = AddCommGrpCat.ofHom d.sectionsMap ≫
        colimit.ι (finiteSupportDiagram B f F V') d.support := by rw [htarget']

/-- The map on finite-support sections induced by a morphism of the small étale site of
`Y`. -/
public def finiteSupportBaseChangeHom
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    [Small.{v} (FiniteSupport B f V)] [Small.{v} (FiniteSupport B f V')] :
    finiteSupportSections B f F V ⟶ finiteSupportSections B f F V' :=
  colimit.desc (finiteSupportDiagram B f F V) (finiteSupportBaseChangeCocone B f F g)

/-- The map on finite-support sections is computed on each colimit generator by base
change. -/
public theorem finiteSupportBaseChangeHom_ι
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    [Small.{v} (FiniteSupport B f V)] [Small.{v} (FiniteSupport B f V')]
    (E : FiniteSupport B f V) :
    colimit.ι (finiteSupportDiagram B f F V) E ≫ finiteSupportBaseChangeHom B f F g =
      AddCommGrpCat.ofHom (finiteSupportBaseChange B f F g E).sectionsMap ≫
        colimit.ι (finiteSupportDiagram B f F V')
          (finiteSupportBaseChange B f F g E).support := by
  dsimp [finiteSupportBaseChangeHom]
  rw [colimit.ι_desc]
  rfl

/-- The scheme-level maps of base change along two morphisms compose to the one along their
composite. -/
private theorem toScheme_map_baseChange_comp {V V₁ V₂ : SmallEtale B Y.obj Y.property}
    (g₁ : V₁ ⟶ V) (g₂ : V₂ ⟶ V₁) :
    (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g₂) ≫
      (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g₁) =
      (SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map (g₂ ≫ g₁)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]

/-- Base change of supports along a composite is base change along the two factors. -/
public theorem finiteSupportBaseChange_support_comp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V₁ V₂ : SmallEtale B Y.obj Y.property} (g₁ : V₁ ⟶ V) (g₂ : V₂ ⟶ V₁)
    (E : FiniteSupport B f V)
    (d₁ : FiniteSupportBaseChange B f F g₁ E)
    (d₂ : FiniteSupportBaseChange B f F g₂ d₁.support)
    (d : FiniteSupportBaseChange B f F (g₂ ≫ g₁) E) :
    d₂.support = d.support := by
  apply Subtype.ext
  have hcomp := toScheme_map_baseChange_comp B f g₁ g₂
  rw [d₂.support_eq, d.support_eq, d₁.support_eq]
  ext x
  change ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g₁)).base
      (((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map g₂)).base x) ∈ E.1 ↔ _
  rw [← Scheme.Hom.comp_apply, hcomp]
  exact Iff.rfl

/-- The induced morphisms of canonical opens compose. -/
public theorem finiteSupportBaseChange_arrow_comp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V₁ V₂ : SmallEtale B Y.obj Y.property} (g₁ : V₁ ⟶ V) (g₂ : V₂ ⟶ V₁)
    (E : FiniteSupport B f V)
    (d₁ : FiniteSupportBaseChange B f F g₁ E)
    (d₂ : FiniteSupportBaseChange B f F g₂ d₁.support)
    (d : FiniteSupportBaseChange B f F (g₂ ≫ g₁) E)
    (hsupport : d₂.support = d.support) :
    HEq (d₂.openMap ≫ d₁.openMap) d.openMap := by
  rcases d₁ with ⟨s₁, hs₁, a₁, c₁, sm₁, sap₁⟩
  rcases d₂ with ⟨s₂, hs₂, a₂, c₂, sm₂, sap₂⟩
  rcases d with ⟨s, hs, a, c, sm, sap⟩
  change s₂ = s at hsupport
  cases hsupport
  let U := supportOpen B X.obj X.property (baseChange B f V) E.1
    (finiteSupport_isLocallyClosed B f V E)
  let U₁ := supportOpen B X.obj X.property (baseChange B f V₁) s₁.1
    (finiteSupport_isLocallyClosed B f V₁ s₁)
  let U₂ := supportOpen B X.obj X.property (baseChange B f V₂) s₂.1
    (finiteSupport_isLocallyClosed B f V₂ s₂)
  let q₁ := (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g₁)
  let q₂ := (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g₂)
  have hcomp : q₂ ≫ q₁ = _ := toScheme_map_baseChange_comp B f g₁ g₂
  have hgeom : (SmallEtale.toScheme B X.obj X.property).map a₂ ≫
      (SmallEtale.toScheme B X.obj X.property).map a₁ =
        (SmallEtale.toScheme B X.obj X.property).map a := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, c₁, ← Category.assoc, c₂, Category.assoc, hcomp, c]
  have heq : a₂ ≫ a₁ = a := by
    apply (SmallEtale.toScheme B X.obj X.property).map_injective
    simpa only [Functor.map_comp] using hgeom
  cases heq
  rfl

/-- The induced maps on supported sections compose. -/
public theorem finiteSupportBaseChange_sections_comp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V₁ V₂ : SmallEtale B Y.obj Y.property} (g₁ : V₁ ⟶ V) (g₂ : V₂ ⟶ V₁)
    (E : FiniteSupport B f V)
    (d₁ : FiniteSupportBaseChange B f F g₁ E)
    (d₂ : FiniteSupportBaseChange B f F g₂ d₁.support)
    (d : FiniteSupportBaseChange B f F (g₂ ≫ g₁) E)
    (hsupport : d₂.support = d.support) :
    HEq (d₂.sectionsMap.comp d₁.sectionsMap) d.sectionsMap := by
  rcases d₁ with ⟨s₁, hs₁, a₁, c₁, sm₁, sap₁⟩
  rcases d₂ with ⟨s₂, hs₂, a₂, c₂, sm₂, sap₂⟩
  rcases d with ⟨s, hs, a, c, sm, sap⟩
  change s₂ = s at hsupport
  let d₁' : FiniteSupportBaseChange B f F g₁ E := ⟨s₁, hs₁, a₁, c₁, sm₁, sap₁⟩
  let d₂' : FiniteSupportBaseChange B f F g₂ d₁'.support := ⟨s₂, hs₂, a₂, c₂, sm₂, sap₂⟩
  let d' : FiniteSupportBaseChange B f F (g₂ ≫ g₁) E := ⟨s, hs, a, c, sm, sap⟩
  cases hsupport
  have hopen_eq : a₂ ≫ a₁ = a :=
    eq_of_heq (finiteSupportBaseChange_arrow_comp B f F g₁ g₂ E d₁' d₂' d' rfl)
  apply heq_of_eq
  change sm₂.comp sm₁ = sm
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change (sm₂ (sm₁ x)).val = (sm x).val
  rw [sap₂, sap₁, sap]
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  simp only [← op_comp]
  rw [hopen_eq]

/-- The morphism of diagrams of supported sections induced by a morphism of abelian
sheaves. -/
public def finiteSupportDiagramMap
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}
    (φ : F ⟶ G) (V : SmallEtale B Y.obj Y.property) :
    finiteSupportDiagram B f F V ⟶ finiteSupportDiagram B f G V where
  app E := AddCommGrpCat.ofHom
    (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E))
  naturality E E' h := AddCommGrpCat.hom_ext <|
    supportedSectionsMap_naturality B X.obj X.property φ (baseChange B f V)
      E.1 E'.1 (finiteSupport_isLocallyClosed B f V E)
      (finiteSupport_isLocallyClosed B f V E') (leOfHom h)
      (finiteSupport_closedWithin B f V E E' (leOfHom h))

/-- Base change on supported sections commutes with the action of a morphism of abelian
sheaves. -/
public theorem finiteSupportBaseChange_sheaf_naturality
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}
    (φ : F ⟶ G) {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) :
    let dF := finiteSupportBaseChange B f F g E
    let dG := finiteSupportBaseChange B f G g E
    HEq (dG.sectionsMap.comp
      (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E)))
      ((supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V')
        dF.support.1 (finiteSupport_isLocallyClosed B f V' dF.support)).comp
          dF.sectionsMap) := by
  dsimp
  let dF := finiteSupportBaseChange B f F g E
  let dG := finiteSupportBaseChange B f G g E
  have hs : dG.support = dF.support := rfl
  have ho : HEq dG.openMap dF.openMap := by
    cases hs
    rfl
  cases hs
  have ho' : dG.openMap = dF.openMap := eq_of_heq ho
  apply heq_of_eq
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  change (dG.sectionsMap
    (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E) s)).val = _
  rw [dG.sectionsMap_apply, ho']
  change G.obj.map dF.openMap.op (φ.hom.app _ s.val) =
    φ.hom.app _ (dF.sectionsMap s).val
  rw [dF.sectionsMap_apply]
  exact (ConcreteCategory.congr_hom (φ.hom.naturality dF.openMap.op) s.val).symm

/-- Base change along the identity does not change the support. -/
public theorem finiteSupportBaseChange_support_id
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (d : FiniteSupportBaseChange B f F (𝟙 V) E) : d.support = E := by
  apply Subtype.ext
  rw [d.support_eq, (smallEtaleBaseChange B f).map_id V,
    (SmallEtale.toScheme B X.obj X.property).map_id (baseChange B f V)]
  rfl

/-- Base change along the identity is the identity on supported sections. -/
public theorem finiteSupportBaseChange_sections_id
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (d : FiniteSupportBaseChange B f F (𝟙 V) E) (hsupport : d.support = E) :
    HEq d.sectionsMap (AddMonoidHom.id
      (supportedSections B X.obj X.property F (baseChange B f V) E.1
        (finiteSupport_isLocallyClosed B f V E))) := by
  rcases d with ⟨s, hs, a, ha, m, hm⟩
  change s = E at hsupport
  cases hsupport
  have ha' : a = 𝟙 _ := by
    apply (SmallEtale.toScheme B X.obj X.property).map_injective
    apply (cancel_mono (supportOpen B X.obj X.property (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)).ι).1
    rw [(smallEtaleBaseChange B f).map_id V,
      (SmallEtale.toScheme B X.obj X.property).map_id (baseChange B f V)] at ha
    simpa only [Category.id_comp, Category.comp_id,
      (SmallEtale.toScheme B X.obj X.property).map_id] using ha
  apply heq_of_eq
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change (m x).val = x.val
  rw [hm, ha']
  simp

/-- **Stacks 0F6M.** The abelian presheaf `V ↦ colim_Z H_Z(F)` on the small étale site of
`Y`, with base change of supports as its restriction maps. -/
@[stacks 0F6M "the finite-support presheaf"]
public abbrev finiteSupportPresheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{v} (FiniteSupport B f V)) :
    (SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{v} := by
  let _ (V : SmallEtale B Y.obj Y.property) := hsmall V
  refine {
    obj := fun V => finiteSupportSections B f F V.unop
    map := fun {V V'} g => finiteSupportBaseChangeHom B f F g.unop
    map_id := ?_
    map_comp := ?_
  }
  · intro V
    apply colimit.hom_ext
    intro E
    simp only [unop_id, Category.comp_id]
    rw [finiteSupportBaseChangeHom_ι]
    let d := finiteSupportBaseChange B f F (𝟙 V.unop) E
    change AddCommGrpCat.ofHom d.sectionsMap ≫
      colimit.ι (finiteSupportDiagram B f F V.unop) d.support =
        colimit.ι (finiteSupportDiagram B f F V.unop) E
    have hs := finiteSupportBaseChange_support_id B f F V.unop E d
    have hm := finiteSupportBaseChange_sections_id B f F V.unop E d hs
    rcases d with ⟨s, hse, a, ha, m, hmapp⟩
    change s = E at hs
    cases hs
    have hm' : m = AddMonoidHom.id _ := eq_of_heq hm
    change AddCommGrpCat.ofHom m ≫ colimit.ι (finiteSupportDiagram B f F V.unop) E =
      colimit.ι (finiteSupportDiagram B f F V.unop) E
    rw [hm', AddCommGrpCat.ofHom_id]
    exact Category.id_comp _
  · intro V V₁ V₂ g₁ g₂
    apply colimit.hom_ext
    intro E
    let d₁ := finiteSupportBaseChange B f F g₁.unop E
    let d₂ := finiteSupportBaseChange B f F g₂.unop d₁.support
    let d := finiteSupportBaseChange B f F (g₂.unop ≫ g₁.unop) E
    have hs := finiteSupportBaseChange_support_comp B f F g₁.unop g₂.unop E d₁ d₂ d
    have hm := finiteSupportBaseChange_sections_comp B f F g₁.unop g₂.unop E d₁ d₂ d hs
    simp only [unop_comp]
    rw [finiteSupportBaseChangeHom_ι, ← Category.assoc, finiteSupportBaseChangeHom_ι]
    have hright :
        (AddCommGrpCat.ofHom d₁.sectionsMap ≫
          colimit.ι (finiteSupportDiagram B f F V₁.unop) d₁.support) ≫
            finiteSupportBaseChangeHom B f F g₂.unop =
        AddCommGrpCat.ofHom d₁.sectionsMap ≫
          (AddCommGrpCat.ofHom d₂.sectionsMap ≫
            colimit.ι (finiteSupportDiagram B f F V₂.unop) d₂.support) := by
      calc
        _ = AddCommGrpCat.ofHom d₁.sectionsMap ≫
            (colimit.ι (finiteSupportDiagram B f F V₁.unop) d₁.support ≫
              finiteSupportBaseChangeHom B f F g₂.unop) := Category.assoc _ _ _
        _ = _ := congrArg (fun k => AddCommGrpCat.ofHom d₁.sectionsMap ≫ k)
          (finiteSupportBaseChangeHom_ι B f F g₂.unop d₁.support)
    change AddCommGrpCat.ofHom d.sectionsMap ≫
      colimit.ι (finiteSupportDiagram B f F V₂.unop) d.support =
      (AddCommGrpCat.ofHom d₁.sectionsMap ≫
        colimit.ι (finiteSupportDiagram B f F V₁.unop) d₁.support) ≫
        finiteSupportBaseChangeHom B f F g₂.unop
    rw [hright]
    rcases d₂ with ⟨s₂, hse₂, a₂, ha₂, m₂, hm₂⟩
    rcases d with ⟨s, hse, a, ha, m, hma⟩
    change s₂ = s at hs
    cases hs
    have hm' : m₂.comp d₁.sectionsMap = m := eq_of_heq hm
    change AddCommGrpCat.ofHom m ≫ colimit.ι (finiteSupportDiagram B f F V₂.unop) s₂ =
      AddCommGrpCat.ofHom d₁.sectionsMap ≫
        (AddCommGrpCat.ofHom m₂ ≫ colimit.ι (finiteSupportDiagram B f F V₂.unop) s₂)
    calc
      _ = (AddCommGrpCat.ofHom d₁.sectionsMap ≫ AddCommGrpCat.ofHom m₂) ≫
          colimit.ι (finiteSupportDiagram B f F V₂.unop) s₂ := by
            rw [← AddCommGrpCat.ofHom_comp, hm']
      _ = _ := Category.assoc _ _ _

/-- The characterization of the finite-support direct image: its values are the colimits of
supported sections, its restriction maps are base change of supports on colimit generators,
and a morphism of abelian sheaves acts by its component on each canonical open. -/
public structure FiniteSupportPushforwardSpec
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{v} (FiniteSupport B f V))
    (P : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{v})) : Prop where
  /-- The value over `V` is the colimit of the supported sections over the supports finite
  over `V`. -/
  obj_eq : ∀ (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
      (V : SmallEtale B Y.obj Y.property),
      letI := hsmall V
      (P.obj F).obj (op V) = finiteSupportSections B f F V
  /-- The restriction map sends the generator of a support to the generator of its inverse
  image, with section restricted along the induced morphism of canonical opens. -/
  map_restrict : ∀ (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
      {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (E : FiniteSupport B f V),
      letI := hsmall V
      letI := hsmall V'
      let d := finiteSupportBaseChange B f F g E
      colimit.ι (finiteSupportDiagram B f F V) E ≫
        eqToHom (obj_eq F V).symm ≫ (P.obj F).map g.op ≫ eqToHom (obj_eq F V') =
      AddCommGrpCat.ofHom d.sectionsMap ≫
        colimit.ι (finiteSupportDiagram B f F V') d.support
  /-- A morphism of abelian sheaves acts on each generator through its component on the
  canonical open of the support. -/
  map_sheaf : ∀ {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}
      (φ : F ⟶ G) (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V),
      letI := hsmall V
      colimit.ι (finiteSupportDiagram B f F V) E ≫
        eqToHom (obj_eq F V).symm ≫ (P.map φ).app (op V) ≫ eqToHom (obj_eq G V) =
      AddCommGrpCat.ofHom (supportedSectionsSheafMap B X.obj X.property φ
        (baseChange B f V) E.1 (finiteSupport_isLocallyClosed B f V E)) ≫
        colimit.ι (finiteSupportDiagram B f G V) E

/-- **Stacks 0F6M.** The direct image with finite support, as a functor from abelian sheaves
on the small étale site of `X` to abelian presheaves on the small étale site of `Y`. Its
values are the colimits `colim_Z H_Z(F)` and both of its functorial actions are pinned down on
the colimit generators. -/
@[stacks 0F6M "the finite-support direct image functor"]
public def finiteSupportPushforward
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{v} (FiniteSupport B f V)) :
    {P : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
        ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{v}) //
      FiniteSupportPushforwardSpec B f hsmall P} := by
  let _ (V : SmallEtale B Y.obj Y.property) := hsmall V
  let P : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
      ((SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{v}) := {
    obj := fun F => finiteSupportPresheaf B f F hsmall
    map := fun {F G} φ => {
      app := fun V => colim.map (finiteSupportDiagramMap B f φ V.unop)
      naturality := by
        intro V V' g
        apply colimit.hom_ext
        intro E
        let dF := finiteSupportBaseChange B f F g.unop E
        let dG := finiteSupportBaseChange B f G g.unop E
        have hs : dF.support = dG.support := rfl
        have hm := finiteSupportBaseChange_sheaf_naturality B f φ g.unop E
        dsimp at hm
        change HEq (dG.sectionsMap.comp
          (supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V.unop) E.1
            (finiteSupport_isLocallyClosed B f V.unop E)))
          ((supportedSectionsSheafMap B X.obj X.property φ (baseChange B f V'.unop)
            dF.support.1 (finiteSupport_isLocallyClosed B f V'.unop dF.support)).comp
              dF.sectionsMap) at hm
        cases hs
        have hcat :
            AddCommGrpCat.ofHom dF.sectionsMap ≫
              (finiteSupportDiagramMap B f φ V'.unop).app dF.support =
            (finiteSupportDiagramMap B f φ V.unop).app E ≫
              AddCommGrpCat.ofHom dG.sectionsMap :=
          AddCommGrpCat.hom_ext (eq_of_heq hm).symm
        have hcat' :
            (AddCommGrpCat.ofHom dF.sectionsMap ≫
              (finiteSupportDiagramMap B f φ V'.unop).app dF.support) ≫
                colimit.ι (finiteSupportDiagram B f G V'.unop) dF.support =
            ((finiteSupportDiagramMap B f φ V.unop).app E ≫
              AddCommGrpCat.ofHom dG.sectionsMap) ≫
                colimit.ι (finiteSupportDiagram B f G V'.unop) dG.support := by
          rw [hcat]
          rfl
        change
          (colimit.ι (finiteSupportDiagram B f F V.unop) E ≫
            finiteSupportBaseChangeHom B f F g.unop) ≫
            colim.map (finiteSupportDiagramMap B f φ V'.unop) =
          (colimit.ι (finiteSupportDiagram B f F V.unop) E ≫
            colim.map (finiteSupportDiagramMap B f φ V.unop)) ≫
            finiteSupportBaseChangeHom B f G g.unop
        rw [finiteSupportBaseChangeHom_ι, colimit.ι_map]
        change
          (AddCommGrpCat.ofHom dF.sectionsMap ≫
            colimit.ι (finiteSupportDiagram B f F V'.unop) dF.support) ≫
              colim.map (finiteSupportDiagramMap B f φ V'.unop) =
          ((finiteSupportDiagramMap B f φ V.unop).app E ≫
            colimit.ι (finiteSupportDiagram B f G V.unop) E) ≫
              finiteSupportBaseChangeHom B f G g.unop
        have hleft :
            (AddCommGrpCat.ofHom dF.sectionsMap ≫
              colimit.ι (finiteSupportDiagram B f F V'.unop) dF.support) ≫
                colim.map (finiteSupportDiagramMap B f φ V'.unop) =
            (AddCommGrpCat.ofHom dF.sectionsMap ≫
              (finiteSupportDiagramMap B f φ V'.unop).app dF.support) ≫
                colimit.ι (finiteSupportDiagram B f G V'.unop) dF.support := by
          calc
            _ = AddCommGrpCat.ofHom dF.sectionsMap ≫
                (colimit.ι (finiteSupportDiagram B f F V'.unop) dF.support ≫
                  colim.map (finiteSupportDiagramMap B f φ V'.unop)) :=
                    Category.assoc _ _ _
            _ = AddCommGrpCat.ofHom dF.sectionsMap ≫
                ((finiteSupportDiagramMap B f φ V'.unop).app dF.support ≫
                  colimit.ι (finiteSupportDiagram B f G V'.unop) dF.support) :=
                    congrArg (fun m => AddCommGrpCat.ofHom dF.sectionsMap ≫ m)
                      (colimit.ι_map (finiteSupportDiagramMap B f φ V'.unop) dF.support)
            _ = _ := (Category.assoc _ _ _).symm
        have hright :
            ((finiteSupportDiagramMap B f φ V.unop).app E ≫
              AddCommGrpCat.ofHom dG.sectionsMap) ≫
                colimit.ι (finiteSupportDiagram B f G V'.unop) dG.support =
            ((finiteSupportDiagramMap B f φ V.unop).app E ≫
              colimit.ι (finiteSupportDiagram B f G V.unop) E) ≫
                finiteSupportBaseChangeHom B f G g.unop := by
          calc
            _ = (finiteSupportDiagramMap B f φ V.unop).app E ≫
                (AddCommGrpCat.ofHom dG.sectionsMap ≫
                  colimit.ι (finiteSupportDiagram B f G V'.unop) dG.support) :=
                    Category.assoc _ _ _
            _ = (finiteSupportDiagramMap B f φ V.unop).app E ≫
                (colimit.ι (finiteSupportDiagram B f G V.unop) E ≫
                  finiteSupportBaseChangeHom B f G g.unop) := by
                    rw [finiteSupportBaseChangeHom_ι]
                    rfl
            _ = _ := (Category.assoc _ _ _).symm
        exact hleft.trans (hcat'.trans hright)
    }
    map_id := by
      intro F
      apply NatTrans.ext
      funext V
      apply colimit.hom_ext
      intro E
      simp only [colimit.ι_map, NatTrans.id_app, Category.comp_id]
      have hApp : (finiteSupportDiagramMap B f (𝟙 F) V.unop).app E = 𝟙 _ :=
        AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ => Subtype.ext rfl
      rw [hApp, Category.id_comp]
    map_comp := by
      intro F G H φ ψ
      apply NatTrans.ext
      funext V
      apply colimit.hom_ext
      intro E
      have hApp : (finiteSupportDiagramMap B f (φ ≫ ψ) V.unop).app E =
          (finiteSupportDiagramMap B f φ V.unop).app E ≫
            (finiteSupportDiagramMap B f ψ V.unop).app E :=
        AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ => Subtype.ext rfl
      simp only [NatTrans.comp_app, colimit.ι_map]
      rw [hApp, Category.assoc, ← colimit.ι_map (finiteSupportDiagramMap B f ψ V.unop) E,
        ← Category.assoc, ← colimit.ι_map (finiteSupportDiagramMap B f φ V.unop) E]
      exact Category.assoc _ _ _
  }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro F V
    rfl
  · intro F V V' g E
    change colimit.ι (finiteSupportDiagram B f F V) E ≫
      finiteSupportBaseChangeHom B f F g = _
    exact finiteSupportBaseChangeHom_ι B f F g E
  · intro F G φ V E
    change colimit.ι (finiteSupportDiagram B f F V) E ≫
      colim.map (finiteSupportDiagramMap B f φ V) = _
    exact colimit.ι_map (finiteSupportDiagramMap B f φ V) E

end FiniteSupport

end AlgebraicGeometry.SmallEtale

end
