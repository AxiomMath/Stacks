module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyExistence
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonStructureIso
public import StacksFrontier.Deformation.Artin.RimSchlessinger.PresheafSquareGluing

/-!
# The comparison at a thickening pushout is fully faithful

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` whose isomorphism sheaves
are algebraic spaces — condition (2) of [Stacks Project, Tag 045G], which for a stack is
equivalent to representability of the diagonal. At a commutative square
`i ≫ a = f ≫ b` of the site whose image in schemes is the pushout of a thickening `i` along an
affine morphism `f`, the comparison functor `Deformation.Artin.fiberSquareComparison` from the
fibre over the fourth corner `Y'` to the two-fibre product of the other three fibres is **fully
faithful**.

The argument is the one the source indicates, and no more:

* a morphism between two objects of the fibre over `Y'` is a section over `Y'` of the isomorphism
  sheaf `Isom(x, y)` — the fibres are groupoids, so a morphism between them is an isomorphism, and
  `CategoryTheory.Functor.morSection` identifies it with a section over the terminal object of the
  slice;
* `Isom(x, y)` is an algebraic space over `Y'`, which is the hypothesis;
* an algebraic space takes a thickening-and-affine pushout square of schemes to a pullback square
  of sets — [Stacks Project, Tag 07SY] in the functor-of-points form
  `AlgebraicGeometry.Space.existsUnique_section_of_isThickening_of_isAffineHom`.

So a pair of morphisms over the two middle corners agreeing over the initial corner comes from
exactly one morphism over `Y'`: uniqueness is faithfulness, existence is fullness. **No
smoothness, no atlas and no infinitesimal lifting property enters**, which is why this half of
[Stacks Project, Tag 0CXP] is available while essential surjectivity is not.

## Main results

* `Deformation.Artin.presheafGluesAt_isomPresheaf` — the isomorphism sheaf of two objects of the
  fibre over `Y'` glues at the square, read in the slice over `Y'`.
* `Deformation.Artin.faithful_fiberSquareComparison_of_isomPresheafAlgebraic` and
  `Deformation.Artin.full_fiberSquareComparison_of_isomPresheafAlgebraic` — faithfulness and
  fullness of the comparison.
* `Deformation.Artin.fullyFaithful_fiberSquareComparison_of_isomPresheafAlgebraic` — the two
  together, as a `CategoryTheory.Functor.FullyFaithful`.
* `Deformation.Artin.faithful_fiberSquareComparison_of_hasRepresentableDiagonal`,
  `Deformation.Artin.full_fiberSquareComparison_of_hasRepresentableDiagonal` and
  `Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal` — the same
  with the hypothesis in the shape condition (1) of [Stacks Project, Tag 045G], i.e.
  representability of the diagonal, which is the clause an algebraic stack carries.
* `Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal_of_isAffine`
  — the same at a square of the kind condition (RS*) quantifies over, where the corners are affine
  and the thickening is of first order. Only affineness of the source and target of the affine leg
  is used, and only the thickening belonging to the square — not the first-order thickening
  opposite to it.

## Implementation notes

Nothing here claims [Stacks Project, Tag 0CXP] or [Stacks Project, Tag 07WN]: those assert that
the comparison is an *equivalence*, and essential surjectivity is not proved here. No tag is
registered.

The algebraicity hypothesis is written out rather than taken as
`AlgebraicGeometry.Stack.IsAlgebraicSpaceIsomPresheaf`, which is stated for a bundled
`CategoryTheory.CatFiberedInGroupoids`; the two agree by definitional unfolding, since that
predicate is an `abbrev`, and the unbundled form applies to the plain functor
`p : 𝒜 ⥤ BigFppfOver B S hS` that `Deformation.Artin.SatisfiesRSStar` and
`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair`
quantify over. `Deformation.Artin.faithful_fiberSquareComparison_of_hasRepresentableDiagonal`
supplies it from the bundled condition through
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`.

`CategoryTheory.Functor.IsFibered` is carried as an instance argument *and*
`CategoryTheory.Functor.IsFiberedInGroupoids` as a hypothesis. It is a `Prop`, so a consumer
which has only the latter supplies `CategoryTheory.Functor.IsFiberedInGroupoids.isFibered` for the
former and obtains, by proof irrelevance, exactly the statement it wants about
`CategoryTheory.Functor.chosenPullbacks`.

Condition (2) of Stacks 045G presents `Isom(x, y)` as a presheaf on the slice
`BigFppfOver B Y'.left.1 Y'.left.2`, i.e. over the *scheme* underlying `Y'`, while the square and
the presheaf `CategoryTheory.Functor.isomPresheaf` live over the *object* `Y'` of the site. The
two are compared by `CategoryTheory.Over.iteratedSliceEquiv`, whose unit is not an identity: the
backward functor sends `g` to `Over.mk (Over.homMk g.hom)`, so a corner of the square presented as
`Over.mk b` is only isomorphic to, not equal to, its image. That transport is
`Deformation.Artin.PresheafGluesAt.of_natIsoFunctor`; the geometric hypotheses need no transport
at all, because the underlying scheme morphism of the image of `Over.homMk u` under
`CategoryTheory.Over.iteratedSliceForward` is the underlying scheme morphism of `u`, on the nose.

Two spellings of the commutativity of the square occur: the `w` this file is given, and the proof
`CategoryTheory.Over.w` extracts from `CategoryTheory.Over.homMk w`, which is what
`CategoryTheory.Functor.morRestrict_eq_pullbackFiberHom` and
`Deformation.Artin.fiberSquareComparison_chosenPullbacks_obj_iso_hom` put into their
`CategoryTheory.Functor.pullbackFiberCompIso'`. The gap between them is proof irrelevance only, so
it is closed by ascribing this file's spelling to the library lemma and letting `exact` check
definitional equality — not by rewriting, which proof irrelevance does not drive.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0CXP](https://stacks.math.columbia.edu/tag/0CXP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u v t

namespace Deformation.Artin

-- `CategoryTheory.Functor.Fiber` and `CategoryTheory.Functor.Fiber.fiberInclusion` are plain
-- `def`s, so a goal mentioning an object of a fibre is not type-correct at `implicit`
-- transparency and `rw` refuses it.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒜 : Type t} [Category.{v} 𝒜] (p : 𝒜 ⥤ BigFppfOver B S hS) [p.IsFibered]

/-- **The isomorphism sheaf of two objects of the fibre over the fourth corner of a thickening
pushout square glues at that square.** The square is read in the slice over `Y'`, with the fourth
corner the terminal object `Over.mk (𝟙 Y')`; `hIsom` is condition (2) of
[Stacks Project, Tag 045G], and the gluing is [Stacks Project, Tag 07SY] transported along the
isomorphism it provides and along `CategoryTheory.Over.iteratedSliceEquiv`. -/
public theorem presheafGluesAt_isomPresheaf
    (hIsom : ∀ (U : BigFppfOver B S hS) (x y : p.Fiber U),
      ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B U.left.1 U.left.2 F ∧
          Nonempty (F ⋙ uliftFunctor.{v, u} ≅
            ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, v}))
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (x y : p.Fiber Y') :
    PresheafGluesAt (p.isomPresheaf x y)
      (Over.homMk i w : Over.mk (f ≫ b) ⟶ Over.mk a)
      (Over.homMk f rfl : Over.mk (f ≫ b) ⟶ Over.mk b)
      (overArrow a) (overArrow b) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := hIsom Y' x y
  have : IsAffineHom ((BigFppfOver.toScheme B Y'.left.1 Y'.left.2).map
      ((Over.iteratedSliceForward Y').map
        (Over.homMk f rfl : Over.mk (f ≫ b) ⟶ Over.mk b))) :=
    inferInstanceAs (IsAffineHom ((BigFppfOver.toScheme B S hS).map f))
  have hFglue := AlgebraicGeometry.Space.existsUnique_section_of_isThickening_of_isAffineHom
    B Y'.left.1 Y'.left.2
    ((Over.iteratedSliceForward Y').map (Over.homMk i w : Over.mk (f ≫ b) ⟶ Over.mk a))
    ((Over.iteratedSliceForward Y').map (Over.homMk f rfl : Over.mk (f ≫ b) ⟶ Over.mk b))
    ((Over.iteratedSliceForward Y').map (overArrow a))
    ((Over.iteratedSliceForward Y').map (overArrow b))
    hi hpush F hF
  exact PresheafGluesAt.of_natIsoFunctor (Over.iteratedSliceEquiv Y').unitIso.symm
    (p.isomPresheaf x y) (PresheafGluesAt.of_uliftIso e hFglue)

/-- The square of the slice over `Y'` cut out by a commutative square of the site with fourth
corner `Y'`: the two triangles over `Y'` commute because the square does. -/
private theorem overArrow_square {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b) :
    (Over.homMk i w : Over.mk (f ≫ b) ⟶ Over.mk a) ≫ overArrow a =
      (Over.homMk f rfl : Over.mk (f ≫ b) ⟶ Over.mk b) ≫ overArrow b :=
  Over.OverMorphism.ext (by simpa using w)

/-- Restricting along `k` a section of `Isom(x, y)` over `Y'` that reads a morphism `γ` of the fibre
gives the base change of `γ` along `k`. -/
private theorem isomPresheaf_map_overArrow_val {Y' V : BigFppfOver B S hS} (x y : p.Fiber Y')
    (γ : x ⟶ y) (k : V ⟶ Y') (s : (p.isomPresheaf x y).obj (op (Over.mk (𝟙 Y'))))
    (hs : morSection p x y γ = s.1) :
    ((p.isomPresheaf x y).map (overArrow k).op s).1 = (chosenPullbacks p).homMap k γ := by
  obtain ⟨s, hm⟩ := s
  cases hs
  change morRestrict p x y (overArrow k) (morSection p x y γ) = _
  rw [chosenPullbacks_homMap]
  exact morRestrict_morSection p x y γ k

/-- Two morphisms conjugated into a common pair of objects by two pairs of isomorphisms agree as
soon as the two conjugation comparisons agree. This is the only computation in the fullness proof
below: the compatibility the comparison functor imposes and the compatibility the gluing property
asks for are two such conjugates of one another. -/
private theorem conj_inv_hom_eq {D : Type*} [Category* D] {A₁ A₂ B₁ B₂ T₁ T₂ : D}
    (u₁ : A₁ ≅ T₁) (u₂ : A₂ ≅ T₂) (v₁ : B₁ ≅ T₁) (v₂ : B₂ ≅ T₂) (m : A₁ ⟶ A₂) (n : B₁ ⟶ B₂)
    (h : n ≫ (v₂.hom ≫ u₂.inv) = (v₁.hom ≫ u₁.inv) ≫ m) :
    u₁.inv ≫ m ≫ u₂.hom = v₁.inv ≫ n ≫ v₂.hom := by
  calc u₁.inv ≫ m ≫ u₂.hom
      = v₁.inv ≫ ((v₁.hom ≫ u₁.inv) ≫ m) ≫ u₂.hom := by simp
    _ = v₁.inv ≫ (n ≫ (v₂.hom ≫ u₂.inv)) ≫ u₂.hom := by rw [← h]
    _ = v₁.inv ≫ n ≫ v₂.hom := by simp

/-- **The comparison at a thickening pushout square is faithful.** Two morphisms of the fibre over
`Y'` with the same restrictions to the two middle corners are two sections of `Isom(x, y)` over
`Y'` with the same restrictions, hence equal by the uniqueness half of
`Deformation.Artin.presheafGluesAt_isomPresheaf`. -/
public theorem faithful_fiberSquareComparison_of_isomPresheafAlgebraic
    (hp : p.IsFiberedInGroupoids)
    (hIsom : ∀ (U : BigFppfOver B S hS) (x y : p.Fiber U),
      ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B U.left.1 U.left.2 F ∧
          Nonempty (F ⋙ uliftFunctor.{v, u} ≅
            ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, v}))
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    (fiberSquareComparison p (chosenPullbacks p) f i b a w.symm).Faithful := by
  have : ∀ V : BigFppfOver B S hS, IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid
  refine faithful_fiberSquareComparison_of_homMap_ext p (chosenPullbacks p) f i b a w.symm ?_
  intro x y α β hrb hra
  -- A morphism of a fibre is invertible, so it is a section of `Isom(x, y)` and not merely of
  -- `Mor(x, y)`.
  let sec : ∀ (g : Over Y') (m : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom),
      (p.isomPresheaf x y).obj (op g) :=
    fun _ m => ⟨m, (mem_isomSubpresheaf_obj p x y m).2 inferInstance⟩
  -- Read as a section over the terminal object of the slice, a morphism of the fibre over `Y'`
  -- restricts to its base change along every morphism into `Y'`.
  have hr : ∀ {V : BigFppfOver B S hS} (k : V ⟶ Y'),
      (chosenPullbacks p).homMap k α = (chosenPullbacks p).homMap k β →
        (p.isomPresheaf x y).map (overArrow k).op (sec (Over.mk (𝟙 Y')) (morSection p x y α)) =
          (p.isomPresheaf x y).map (overArrow k).op (sec (Over.mk (𝟙 Y')) (morSection p x y β)) :=
    fun k h => Subtype.ext <|
      (isomPresheaf_map_overArrow_val B S hS p x y α k _ rfl).trans <| h.trans
        (isomPresheaf_map_overArrow_val B S hS p x y β k _ rfl).symm
  have hcompat : (p.isomPresheaf x y).map
        (Over.homMk i w : Over.mk (f ≫ b) ⟶ Over.mk a).op
        ((p.isomPresheaf x y).map (overArrow a).op
          (sec (Over.mk (𝟙 Y')) (morSection p x y α))) =
      (p.isomPresheaf x y).map (Over.homMk f rfl : Over.mk (f ≫ b) ⟶ Over.mk b).op
        ((p.isomPresheaf x y).map (overArrow b).op
          (sec (Over.mk (𝟙 Y')) (morSection p x y α))) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      overArrow_square B S hS i f a b w]
  obtain ⟨s, -, huniq⟩ :=
    presheafGluesAt_isomPresheaf B S hS p hIsom i f a b w hi hpush x y _ _ hcompat
  have hsecEq : sec (Over.mk (𝟙 Y')) (morSection p x y α) =
      sec (Over.mk (𝟙 Y')) (morSection p x y β) :=
    (huniq _ ⟨rfl, rfl⟩).trans (huniq _ ⟨(hr a hra).symm, (hr b hrb).symm⟩).symm
  exact morSection_injective p x y (congrArg Subtype.val hsecEq)

/-- **The comparison at a thickening pushout square is full.** A pair of morphisms of the two
middle fibres compatible with the structure isomorphism is a pair of sections of `Isom(x, y)`
agreeing over the initial corner, so the existence half of
`Deformation.Artin.presheafGluesAt_isomPresheaf` produces a section over `Y'`, i.e. a morphism of
the fibre over `Y'` whose two chosen restrictions they are. -/
public theorem full_fiberSquareComparison_of_isomPresheafAlgebraic
    (hp : p.IsFiberedInGroupoids)
    (hIsom : ∀ (U : BigFppfOver B S hS) (x y : p.Fiber U),
      ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B U.left.1 U.left.2 F ∧
          Nonempty (F ⋙ uliftFunctor.{v, u} ≅
            ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, v}))
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    (fiberSquareComparison p (chosenPullbacks p) f i b a w.symm).Full := by
  have : ∀ V : BigFppfOver B S hS, IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid
  refine full_fiberSquareComparison_of_exists_homMap p (chosenPullbacks p) f i b a w.symm ?_
  intro x y α β hcompat
  -- The structure isomorphism of the comparison is the composite of the two contractions of an
  -- iterated chosen pullback, both taken at the one name `f ≫ b`.
  have hisoHom : ∀ z : p.Fiber Y',
      ((fiberSquareComparison p (chosenPullbacks p) f i b a w.symm).obj z).iso.hom =
        (pullbackFiberCompIso' z b f (f ≫ b) rfl).hom ≫
          (pullbackFiberCompIso' z a i (f ≫ b) w).inv := fun z =>
    fiberSquareComparison_chosenPullbacks_obj_iso_hom p f i b a w.symm z
  rw [hisoHom x, hisoHom y] at hcompat
  -- The same compatibility with the two base changes spelled as
  -- `CategoryTheory.Functor.pullbackFiberHom`, which is how
  -- `CategoryTheory.Functor.morRestrict_eq_pullbackFiberHom` presents a restriction.
  have hc : pullbackFiberHom α f ≫ ((pullbackFiberCompIso' y b f (f ≫ b) rfl).hom ≫
        (pullbackFiberCompIso' y a i (f ≫ b) w).inv) =
      ((pullbackFiberCompIso' x b f (f ≫ b) rfl).hom ≫
        (pullbackFiberCompIso' x a i (f ≫ b) w).inv) ≫ pullbackFiberHom β i := by
    rwa [← chosenPullbacks_homMap p f α, ← chosenPullbacks_homMap p i β]
  let sec : ∀ (g : Over Y') (m : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom),
      (p.isomPresheaf x y).obj (op g) :=
    fun _ m => ⟨m, (mem_isomSubpresheaf_obj p x y m).2 inferInstance⟩
  have hcompat' : morRestrict p x y (Over.homMk i w : Over.mk (f ≫ b) ⟶ Over.mk a) β =
      morRestrict p x y (Over.homMk f rfl : Over.mk (f ≫ b) ⟶ Over.mk b) α := by
    rw [morRestrict_eq_pullbackFiberHom p x y (Over.homMk i w : Over.mk (f ≫ b) ⟶ Over.mk a) β,
      morRestrict_eq_pullbackFiberHom p x y (Over.homMk f rfl : Over.mk (f ≫ b) ⟶ Over.mk b) α]
    exact conj_inv_hom_eq (pullbackFiberCompIso' x a i (f ≫ b) w)
      (pullbackFiberCompIso' y a i (f ≫ b) w) (pullbackFiberCompIso' x b f (f ≫ b) rfl)
      (pullbackFiberCompIso' y b f (f ≫ b) rfl) (pullbackFiberHom β i) (pullbackFiberHom α f)
      hc
  obtain ⟨s, ⟨hsa, hsb⟩, -⟩ :=
    presheafGluesAt_isomPresheaf B S hS p hIsom i f a b w hi hpush x y
      (sec (Over.mk a) β) (sec (Over.mk b) α) (Subtype.ext hcompat')
  have hsec : morSection p x y
      ((pullbackFiberIdIso x).inv ≫ s.1 ≫ (pullbackFiberIdIso y).hom) = s.1 := by
    simp [morSection]
  refine ⟨(pullbackFiberIdIso x).inv ≫ s.1 ≫ (pullbackFiberIdIso y).hom, ?_, ?_⟩
  · exact (isomPresheaf_map_overArrow_val B S hS p x y _ b s hsec).symm.trans
      (congrArg Subtype.val hsb)
  · exact (isomPresheaf_map_overArrow_val B S hS p x y _ a s hsec).symm.trans
      (congrArg Subtype.val hsa)

/-- **The comparison at a thickening pushout square is fully faithful**, the two halves together.
This is the fully-faithful half of the equivalence asserted by [Stacks Project, Tag 0CXP]; the
remaining half, essential surjectivity, is not proved here, so no tag is claimed. -/
public noncomputable def fullyFaithful_fiberSquareComparison_of_isomPresheafAlgebraic
    (hp : p.IsFiberedInGroupoids)
    (hIsom : ∀ (U : BigFppfOver B S hS) (x y : p.Fiber U),
      ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B U.left.1 U.left.2 F ∧
          Nonempty (F ⋙ uliftFunctor.{v, u} ≅
            ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, v}))
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    (fiberSquareComparison p (chosenPullbacks p) f i b a w.symm).FullyFaithful :=
  haveI := full_fiberSquareComparison_of_isomPresheafAlgebraic B S hS p hp hIsom i f a b w hi hpush
  haveI :=
    faithful_fiberSquareComparison_of_isomPresheafAlgebraic B S hS p hp hIsom i f a b w hi hpush
  Functor.FullyFaithful.ofFullyFaithful _

section RepresentableDiagonal

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
  [𝒳.val.p.IsFibered]

/-- **The comparison at a thickening pushout square is faithful for a category fibred in groupoids
with representable diagonal.** The diagonal condition is condition (1) of
[Stacks Project, Tag 045G], the clause an algebraic stack carries; it supplies the algebraicity of
the isomorphism sheaves through
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`. -/
public theorem faithful_fiberSquareComparison_of_hasRepresentableDiagonal
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    (fiberSquareComparison 𝒳.val.p (chosenPullbacks 𝒳.val.p) f i b a w.symm).Faithful :=
  faithful_fiberSquareComparison_of_isomPresheafAlgebraic B S hS 𝒳.val.p
    𝒳.isFiberedInGroupoids
    ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).1 hdiag)
    i f a b w hi hpush

/-- **The comparison at a thickening pushout square is full for a category fibred in groupoids
with representable diagonal.** -/
public theorem full_fiberSquareComparison_of_hasRepresentableDiagonal
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    (fiberSquareComparison 𝒳.val.p (chosenPullbacks 𝒳.val.p) f i b a w.symm).Full :=
  full_fiberSquareComparison_of_isomPresheafAlgebraic B S hS 𝒳.val.p
    𝒳.isFiberedInGroupoids
    ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).1 hdiag)
    i f a b w hi hpush

/-- **The comparison at a thickening pushout square is fully faithful for a category fibred in
groupoids with representable diagonal.** This is the fully-faithful half of the equivalence
asserted by [Stacks Project, Tag 0CXP] for an algebraic stack: of the four clauses of
`AlgebraicGeometry.Stack.IsAlgebraicStack` only the fibred-in-groupoids clause and the
representable-diagonal clause are used, and in particular neither the stack condition nor the
smooth surjective presentation enters. Essential surjectivity is not proved here, so no tag is
claimed. -/
public noncomputable def fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    (fiberSquareComparison 𝒳.val.p (chosenPullbacks 𝒳.val.p) f i b a w.symm).FullyFaithful :=
  fullyFaithful_fiberSquareComparison_of_isomPresheafAlgebraic B S hS 𝒳.val.p
    𝒳.isFiberedInGroupoids
    ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).1 hdiag)
    i f a b w hi hpush

/-- **The comparison is fully faithful at the squares condition (RS*) quantifies over.** Those
squares have affine corners and a thickening of *first* order
(`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair`),
and this is the fully-faithful half at a square of that kind: affineness of the source and target
of `f` makes `f` an affine morphism, and a first-order thickening is a thickening, so no
hypothesis beyond those of
`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal` is needed.
Only affineness of the two corners of `f` is used, and only the thickening `i` of the square — not
the morphism opposite to it. -/
public noncomputable def
    fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal_of_isAffine
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (hfirst : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    (fiberSquareComparison 𝒳.val.p (chosenPullbacks 𝒳.val.p) f i b a w.symm).FullyFaithful :=
  haveI := hX
  haveI := hY
  fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal B S hS 𝒳 hdiag i f a b w
    hfirst.isThickening hpush

end RepresentableDiagonal

end Deformation.Artin

end
