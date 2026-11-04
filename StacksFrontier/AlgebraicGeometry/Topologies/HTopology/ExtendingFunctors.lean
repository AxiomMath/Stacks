module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStagewiseInterchange
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.StandardCoveringsLimit
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination

/-!
# Extending an h sheaf from a big h site to all schemes over the base

Let `S` be a scheme contained in a big h site and let `𝒞 = (Sch/S)_h` be the big h category over
`S`, presented as a full subcategory of `Sch/S` satisfying conditions (1) and (2) of Stacks 0EUW.
A functor `F : 𝒞ᵒᵖ ⥤ Set` which is an h sheaf and satisfies condition (b) of Stacks 0EUW extends
to `Sch/S`, by `AlgebraicGeometry.ExtendingFunctors.extension`, and the extension `F'` satisfies
the sheaf condition for *all* h coverings of *all* schemes over `S` and takes directed inverse
limits of affine schemes over `S` to filtered colimits, which is the limit preserving condition of
Limits, Remark 05LX.

## The reduction

An object `X` of `Sch/S` is covered by its affine opens lying over affine opens of `S`. Over such
an affine open `U` a given h covering of `X` pulls back to an h covering of `U` — base change along
an open immersion needs no refinement of a composite of standard ph coverings, so this is the
unconditional case of Stacks 0ETY part (3) — and Stacks 0ETU refines it there by a *standard* h
covering. The restricted sheaf condition then produces a section over `U`, characterized by
agreeing with the given family on every morphism into `U` factoring through a member of the
covering over `X`. That characterization makes the local sections agree on the pairwise
intersections and makes the glued section restrict correctly; the gluing itself is the Zariski
sheaf condition.

The restricted sheaf condition in turn holds because an affine object of `Sch/S` lying over an
affine open of `S` is a directed limit of affines of finite presentation over an affine open of
`S` (Stacks 00QN) along which a standard h covering descends to a stage (Stacks 0EV2 part (1)):
the stages of the descended covering are affine and of finite presentation over that affine open,
hence objects of `𝒞` up to isomorphism, so the h sheaf property of `F` gives the sheaf condition
at each stage, and the filtered-colimit interchange passes it to the limit.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsHCoveringOver`: a family of morphisms of `Sch/S` whose
  underlying family of morphisms of schemes is an h covering.
* `AlgebraicGeometry.ExtendingFunctors.IsHCoveringSheafOnSubcategory`: the h sheaf condition for a
  functor on a full subcategory of `Sch/S`, the hypothesis of the source on `F`.
* `AlgebraicGeometry.ExtendingFunctors.IsHSheaf`: the first conclusion of Stacks 0EV3, the sheaf
  condition for every h covering of every object of `Sch/S`.
* `AlgebraicGeometry.ExtendingFunctors.IsStandardAffineHSheaf`: the restricted sheaf condition,
  for the standard h coverings of the affine objects lying over an affine open of `S`.

## Main results

* `AlgebraicGeometry.IsHCovering.of_iso`: an h covering stays one after replacing each source by
  an isomorphic scheme.
* `AlgebraicGeometry.ExtendingFunctors.IsHCoveringOver.pullback_of_isOpenImmersion` and
  `AlgebraicGeometry.ExtendingFunctors.IsHCoveringOver.pullback_of_isAffine`: the two
  unconditional base change statements for h coverings of `Sch/S`.
* `AlgebraicGeometry.ExtendingFunctors.isHCoveringOver_of_mem_coveringPrecoverage_fppf`: an fppf
  covering of `Sch/S` is an h covering.
* `ExtendingFunctors.isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory`: an h sheaf on
  the subcategory satisfies condition (a) of Stacks 0EUW.
* `AlgebraicGeometry.ExtendingFunctors.exists_isStandardHCovering_refinement_over`: Stacks 0ETU
  for `Sch/S`.
* `AlgebraicGeometry.ExtendingFunctors.isSeparatedFor_of_isStandardAffineHSheaf` and
  `AlgebraicGeometry.ExtendingFunctors.exists_section_of_isStandardAffineHSheaf`: the two halves
  of the reduction.
* `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isHCoveringOver`: the h sheaf
  property of `F` read for the extension, at an h covering of an object of the subcategory by
  objects isomorphic to objects of the subcategory.
* `AlgebraicGeometry.ExtendingFunctors.isStandardAffineHSheaf_extension`: the restricted sheaf
  condition for the extension, deduced from the h sheaf property of `F`.
* `AlgebraicGeometry.ExtendingFunctors.isHSheaf_extension` and
  `AlgebraicGeometry.ExtendingFunctors.isLimitPreserving_extension`: the two conclusions of
  Stacks 0EV3 at the extension.

## Implementation notes

An h covering is a family of morphisms rather than a covering sieve, matching the source, and its
index type lies in an arbitrary universe; the index type of the refining standard h covering is
raised to the universe of the schemes, which is why the restricted sheaf condition is used one
universe higher than the conclusion. Since `Sch/S` has pullbacks,
`CategoryTheory.Presieve.IsSheafFor` for the presieve generated by such a family is the condition
that the value at the target be the equalizer of the two maps between the products over the
members and over their pairwise fibre products.

A standard h covering of an affine scheme is the same thing as a finite h covering of it by
affine schemes along morphisms of finite presentation
(`AlgebraicGeometry.isStandardHCovering_iff_isHCovering`), so the h sheaf property of `F` applies
to the descended covering at a stage with no further comparison of coverings. Stacks 0EV2 part
(1) states the descent as an isomorphism of families,
`CategoryTheory.PreZeroHypercover`, indexed in the universe of the index type of the inverse
system, which is the universe of the schemes; a standard h covering being finite, the given
family is first reindexed by a type in that universe. The isomorphism of families is used only
through its two underlying refinement morphisms, which say that the given family and the base
change of the descended one generate the same sieve of `Sch/S`, and the sheaf condition depends
only on that sieve.

## References

* [Stacks Project, Tag 0EV3](https://stacks.math.columbia.edu/tag/0EV3)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0ETU](https://stacks.math.columbia.edu/tag/0ETU)
* [Stacks Project, Tag 0EV2](https://stacks.math.columbia.edu/tag/0EV2)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe w u v

/-! ### h coverings and isomorphic families -/

/-- An h covering remains an h covering when each of its sources is replaced by an isomorphic
scheme and each of its members is precomposed with that isomorphism. -/
theorem IsHCovering.of_iso {T : Scheme.{u}} {I : Type v} {X X' : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} {f' : ∀ i, X' i ⟶ T} (hf : IsHCovering X f)
    (e : ∀ i, X' i ≅ X i) (he : ∀ i, (e i).hom ≫ f i = f' i) :
    IsHCovering X' f' := by
  have hlfp : ∀ i, LocallyOfFinitePresentation (f' i) := by
    intro i
    have := hf.1 i
    rw [← he i]
    infer_instance
  refine ⟨hlfp, ?_⟩
  rw [isPHCovering_iff]
  refine ⟨fun i ↦ by have := hlfp i; infer_instance, fun U hU ↦ ?_⟩
  obtain ⟨𝒰, h𝒰, ⟨s⟩⟩ := hf.2.2 U hU
  let r : ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T).Hom
      ({ I₀ := I, X := X', f := f' } : PreZeroHypercover.{v} T) :=
    { s₀ := fun i ↦ i
      h₀ := fun i ↦ (e i).inv
      w₀ := fun i ↦ (congrArg (fun k ↦ (e i).inv ≫ k) (he i).symm).trans
        (Iso.inv_hom_id_assoc (e i) (f i)) }
  exact ⟨𝒰, h𝒰, ⟨s.comp (r.pullback₂ U.ι)⟩⟩

namespace ExtendingFunctors

variable {S : Scheme.{u}}

/-! ### h coverings of `Sch/S` -/

/-- A family of morphisms of `Sch/S` is an **h covering** when the underlying family of morphisms
of schemes is one. -/
def IsHCoveringOver {X : Over S} {ι : Type v} {Y : ι → Over S} (f : ∀ i, Y i ⟶ X) : Prop :=
  IsHCovering (fun i ↦ (Y i).left) (fun i ↦ (f i).left)

/-- The underlying scheme of a fibre product in `Sch/S` is a fibre product of the underlying
schemes, the forgetful functor preserving connected limits. -/
theorem isPullback_left_pullback {X Y Z : Over S} (g : Z ⟶ X) (f : Y ⟶ X) :
    IsPullback (pullback.fst g f).left (pullback.snd g f).left g.left f.left :=
  (IsPullback.of_hasPullback g f).map (Over.forget S)

/-- The base change of a family of morphisms of `Sch/S` is an h covering as soon as the base
change of the underlying family of morphisms of schemes is. -/
theorem isHCoveringOver_pullback_of_isHCovering {X : Over S} {ι : Type v} {Y : ι → Over S}
    (f : ∀ i, Y i ⟶ X) {Z : Over S} (g : Z ⟶ X)
    (H : IsHCovering (fun i ↦ pullback (f i).left g.left)
      (fun i ↦ pullback.snd (f i).left g.left)) :
    IsHCoveringOver (fun i ↦ pullback.fst g (f i)) :=
  H.of_iso (fun i ↦ (isPullback_left_pullback g (f i)).flip.isoPullback)
    fun i ↦ (isPullback_left_pullback g (f i)).flip.isoPullback_hom_snd

/-- **The unconditional case of Stacks 0ETY part (3) for `Sch/S`.** The base change of an h
covering of `Sch/S` along a morphism whose underlying morphism of schemes is an open immersion is
an h covering: every affine open of the source maps onto an affine open of the target. -/
theorem IsHCoveringOver.pullback_of_isOpenImmersion {X : Over S} {ι : Type v} {Y : ι → Over S}
    {f : ∀ i, Y i ⟶ X} (hf : IsHCoveringOver f) {Z : Over S} (g : Z ⟶ X)
    [IsOpenImmersion g.left] :
    IsHCoveringOver (fun i ↦ pullback.fst g (f i)) :=
  isHCoveringOver_pullback_of_isHCovering f g
    (isHCovering_pullback_of_forall_exists_isAffineOpen hf g.left fun U' hU' ↦
      ⟨g.left ''ᵁ U', hU'.image_of_isOpenImmersion g.left, by
        rintro _ ⟨z, rfl⟩
        exact ⟨z.1, z.2, rfl⟩⟩)

/-- **Stacks 0ETY part (3) over an affine object of `Sch/S`.** The base change of an h covering of
an affine object of `Sch/S` along an arbitrary morphism is an h covering. -/
theorem IsHCoveringOver.pullback_of_isAffine {X : Over S} [IsAffine X.left] {ι : Type v}
    {Y : ι → Over S} {f : ∀ i, Y i ⟶ X} (hf : IsHCoveringOver f) {Z : Over S} (g : Z ⟶ X) :
    IsHCoveringOver (fun i ↦ pullback.fst g (f i)) :=
  isHCoveringOver_pullback_of_isHCovering f g (isHCovering_pullback_of_isAffine hf g.left)

/-! ### The h sheaf condition on a full subcategory -/

/-- **The h sheaf condition for a functor on a full subcategory of `Sch/S`.** For every h covering
of an object of the subcategory by objects of the subcategory, the sheaf condition holds.

The sheaf condition is `CategoryTheory.Presieve.IsSheafFor` inside the subcategory, so the
compatibility of a family of sections is tested on the objects of the subcategory mapping to two
members of the covering. Taking the subcategory to be the big h category `(Sch/S)_h`, this is the
hypothesis of Stacks 0EV3 on `F`. -/
def IsHCoveringSheafOnSubcategory (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type w) : Prop :=
  ∀ {ι : Type v} (X : P.FullSubcategory) (Y : ι → P.FullSubcategory) (f : ∀ i, Y i ⟶ X),
    IsHCoveringOver (fun i ↦ P.ι.map (f i)) → (Presieve.ofArrows Y f).IsSheafFor F

/-- **Stacks 0DBT for `Sch/S`.** An fppf covering of `Sch/S` is an h covering: its members are
locally of finite presentation, and an fppf covering of schemes is a ph covering. -/
theorem isHCoveringOver_of_mem_coveringPrecoverage_fppf {X : Over S} {ι : Type v}
    (Y : ι → Over S) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ coveringPrecoverage S .fppf X) :
    IsHCoveringOver f := by
  rw [ofArrows_mem_coveringPrecoverage_iff] at hf
  exact ⟨fun i ↦ (hf.2 i).2, IsPHCovering.of_mem_fppfPrecoverage _ _
    ((Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr ⟨hf.1, hf.2⟩)⟩

/-- An h sheaf on a full subcategory of `Sch/S` is an fppf sheaf on it. -/
theorem isCoveringSheafOnSubcategory_fppf_of_isHCoveringSheafOnSubcategory
    {P : ObjectProperty (Over S)} {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (hF : IsHCoveringSheafOnSubcategory.{w, u, v} P F) :
    IsCoveringSheafOnSubcategory.{w, u, v} .fppf P F := fun X Y f hf ↦
  hF X Y f (isHCoveringOver_of_mem_coveringPrecoverage_fppf _ _ hf)

/-- **Condition (a) of Stacks 0EUW holds for an h sheaf on the subcategory.** A jointly surjective
family of open immersions is an fppf covering, and an fppf covering is an h covering, so the
condition follows from the fppf case. -/
theorem isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory
    {P : ObjectProperty (Over S)} (hP1 : HasAffineOpens P) {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (hF : IsHCoveringSheafOnSubcategory.{w, u, u} P F) :
    IsZariskiSheafOnSubcategory P F :=
  isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory .fppf hP1
    (isCoveringSheafOnSubcategory_fppf_of_isHCoveringSheafOnSubcategory hF)

/-! ### The sheaf conditions -/

/-- **The first conclusion of Stacks 0EV3.** A functor on `Sch/S` satisfies the sheaf condition
for every h covering `{Y i ⟶ X}` of every object of `Sch/S`.

Since `Sch/S` has pullbacks, `CategoryTheory.Presieve.IsSheafFor` for the presieve generated by
the family is the condition that `G X` be the equalizer of the two maps
`∏ G (Y i) ⟶ ∏ G (Y i ×_X Y j)`. -/
def IsHSheaf (G : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ {ι : Type v} (X : Over S) (Y : ι → Over S) (f : ∀ i, Y i ⟶ X),
    IsHCoveringOver f → (Presieve.ofArrows Y f).IsSheafFor G

/-- The sheaf condition for a functor on `Sch/S` and the *standard* h coverings of the affine
objects of `Sch/S` whose structure morphism factors through an affine open of `S`.

This is the restricted case of `AlgebraicGeometry.ExtendingFunctors.IsHSheaf` to which the general
case is reduced in `AlgebraicGeometry.ExtendingFunctors.isHSheaf_of_isStandardAffineHSheaf`. -/
def IsStandardAffineHSheaf (G : (Over S)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ {ι : Type v} (V : Over S) (hV : IsAffineOverAffineOpen V) (W : ι → Over S)
    (f : ∀ i, W i ⟶ V),
    @IsStandardHCovering V.left hV.1 ι (fun i ↦ (W i).left) (fun i ↦ (f i).left) →
      (Presieve.ofArrows W f).IsSheafFor G

/-- A standard h covering of an affine object of `Sch/S` is an h covering. -/
theorem isHCoveringOver_of_isStandardHCovering {V : Over S} (hV : IsAffine V.left) {ι : Type v}
    (W : ι → Over S) (f : ∀ i, W i ⟶ V)
    (h : @IsStandardHCovering V.left hV ι (fun i ↦ (W i).left) (fun i ↦ (f i).left)) :
    IsHCoveringOver f :=
  h.isHCovering

/-- The sheaf condition for the standard h coverings of the affine objects lying over an affine
open of `S` is weaker than the sheaf condition for all h coverings: the coverings it tests are h
coverings of a restricted class of objects. -/
theorem isStandardAffineHSheaf_of_isHSheaf {G : (Over S)ᵒᵖ ⥤ Type w}
    (h : IsHSheaf.{w, u, v} G) : IsStandardAffineHSheaf.{w, u, v} G := fun V hV W f hstd ↦
  h V W f (isHCoveringOver_of_isStandardHCovering hV.1 W f hstd)

/-! ### Refinement by standard h coverings -/

/-- **Stacks 0ETU for `Sch/S`.** An h covering of an affine object of `Sch/S` is refined by a
standard h covering, the refinement being recorded as a choice of index and of a morphism over the
target for each member. -/
theorem exists_isStandardHCovering_refinement_over {V : Over S} (hV : IsAffine V.left)
    {ι : Type v} {Y : ι → Over S} (f : ∀ i, Y i ⟶ V) (hf : IsHCoveringOver f) :
    ∃ (κ : Type (max u v)) (W : κ → Over S) (g : ∀ j, W j ⟶ V) (a : κ → ι)
      (c : ∀ j, W j ⟶ Y (a j)),
      (@IsStandardHCovering V.left hV κ (fun j ↦ (W j).left) (fun j ↦ (g j).left)) ∧
        ∀ j, g j = c j ≫ f (a j) := by
  have := hV
  obtain ⟨K, Vs, q, hstd, ⟨φ⟩⟩ :=
    exists_isStandardHCovering_refinement.{u, v, v} (fun i ↦ (Y i).left) (fun i ↦ (f i).left) hf
  refine ⟨K, fun j ↦ Over.mk (q j ≫ V.hom), fun j ↦ Over.homMk (q j) rfl,
    fun j ↦ φ.s₀ j, fun j ↦ Over.homMk (φ.h₀ j) ?_, hstd, fun j ↦ ?_⟩
  · show φ.h₀ j ≫ (Y (φ.s₀ j)).hom = q j ≫ V.hom
    rw [← Over.w (f (φ.s₀ j)), ← Category.assoc]
    exact congrArg (· ≫ V.hom) (φ.w₀ j)
  · refine Over.OverMorphism.ext ?_
    rw [Over.comp_left]
    exact (φ.w₀ j).symm

/-! ### The reduction to the standard affine case -/

/-- A morphism factoring through the first projection of a pullback becomes, after composing with
the base morphism, a morphism factoring through the second projection followed by the other leg. -/
private theorem comp_eq_comp_snd_comp_of_eq_comp_fst {X Y Z A : Over S} (p : Z ⟶ X) (f : Y ⟶ X)
    {g : A ⟶ Z} {c : A ⟶ pullback p f} (h : g = c ≫ pullback.fst p f) :
    g ≫ p = (c ≫ pullback.snd p f) ≫ f := by
  rw [h, Category.assoc, Category.assoc, pullback.condition]

/-- **Separatedness for all h coverings.** A Zariski sheaf on `Sch/S` which satisfies the sheaf
condition for the standard h coverings of the affine objects lying over an affine open of `S` is
separated for every h covering: a section is determined by its restrictions to an affine open
covering of its domain lying over affine opens of `S`, and over each such affine open the given
covering is refined by a standard one. -/
theorem isSeparatedFor_of_isStandardAffineHSheaf {G : (Over S)ᵒᵖ ⥤ Type w}
    (haG : IsZariskiSheaf G) (hG : IsStandardAffineHSheaf.{w, u, max u v} G)
    {ι : Type v} (X : Over S) (Y : ι → Over S) (f : ∀ i, Y i ⟶ X)
    (hf : IsHCoveringOver f) :
    (Presieve.ofArrows Y f).IsSeparatedFor G := by
  intro x u₁ u₂ hu₁ hu₂
  have hagree : ∀ i, G.map (f i).op u₁ = G.map (f i).op u₂ := fun i ↦ by
    rw [hu₁ (f i) (Presieve.ofArrows.mk i), hu₂ (f i) (Presieve.ofArrows.mk i)]
  obtain ⟨κ₀, V, hVcov, hVaff⟩ := exists_isAffineOverAffineOpen_cover X
  refine zariskiSheaf_ext haG V hVcov u₁ u₂ fun k ↦ ?_
  obtain ⟨κ, W, g, a, c, hstd, hgc⟩ := exists_isStandardHCovering_refinement_over (hVaff k).1
    (fun i ↦ pullback.fst (overOpenι X (V k)) (f i))
    (hf.pullback_of_isOpenImmersion (overOpenι X (V k)))
  refine (hG _ (hVaff k) W g hstd).isSeparatedFor.ext ?_
  rintro A h ⟨j⟩
  rw [map_map_apply, map_map_apply, comp_eq_comp_snd_comp_of_eq_comp_fst _ _ (hgc j),
    ← map_map_apply, hagree, map_map_apply]

/-- **The section over an affine object.** Let `{Y i ⟶ X}` be an h covering and let `s` be a
family of sections of `G` over the `Y i` agreeing on every object of `Sch/S` mapping to two
members of the covering. For an affine object `U` of `Sch/S` lying over an affine open of `S`
together with a morphism `U ⟶ X` whose base change of the covering is again an h covering, there
is a section of `G` over `U` which agrees with the given family on every morphism into `U` that
factors through a member of the covering over `X`.

The covering is refined over `U` by a standard h covering, over whose members the family supplies
compatible sections. The characterizing property also discharges the two compatibility
verifications omitted by the source. -/
theorem exists_section_of_isStandardAffineHSheaf {G : (Over S)ᵒᵖ ⥤ Type w}
    (haG : IsZariskiSheaf G) (hG : IsStandardAffineHSheaf.{w, u, max u v} G)
    {ι : Type v} {X : Over S} {Y : ι → Over S} (f : ∀ i, Y i ⟶ X)
    (s : ∀ i, G.obj (op (Y i)))
    (hs : ∀ (i i' : ι) (A : Over S) (α : A ⟶ Y i) (β : A ⟶ Y i'),
      α ≫ f i = β ≫ f i' → G.map α.op (s i) = G.map β.op (s i'))
    {U : Over S} (hU : IsAffineOverAffineOpen U) (p : U ⟶ X)
    (hp : IsHCoveringOver (fun i ↦ pullback.fst p (f i))) :
    ∃ t : G.obj (op U), ∀ (Z : Over S) (q : Z ⟶ U) (i : ι) (r : Z ⟶ Y i),
      q ≫ p = r ≫ f i → G.map q.op t = G.map r.op (s i) := by
  have hUaff : IsAffine U.left := hU.1
  obtain ⟨κ, W, g, a, c, hstd, hgc⟩ :=
    exists_isStandardHCovering_refinement_over hU.1 (fun i ↦ pullback.fst p (f i)) hp
  -- the refinement maps to the members of the covering over `X`
  have hgd : ∀ j, g j ≫ p = c j ≫ pullback.snd p (f (a j)) ≫ f (a j) := fun j ↦ by
    rw [← Category.assoc]
    exact comp_eq_comp_snd_comp_of_eq_comp_fst _ _ (hgc j)
  -- the sections of `G` over the members of the refinement, and their coherence
  have hy : ∀ (j j' : κ) (A : Over S) (α : A ⟶ W j) (β : A ⟶ W j'), α ≫ g j = β ≫ g j' →
      G.map α.op (G.map (c j ≫ pullback.snd p (f (a j))).op (s (a j)))
        = G.map β.op (G.map (c j' ≫ pullback.snd p (f (a j'))).op (s (a j'))) := by
    intro j j' A α β hαβ
    rw [map_map_apply, map_map_apply]
    refine hs _ _ A _ _ ?_
    simp only [Category.assoc]
    rw [← hgd j, ← hgd j', ← Category.assoc, ← Category.assoc, hαβ]
  obtain ⟨t, ht⟩ := exists_section_of_isSheafFor_ofArrows W g (hG _ hU W g hstd)
    (fun j ↦ G.map (c j ≫ pullback.snd p (f (a j))).op (s (a j))) hy
  refine ⟨t, fun Z q i r hqr ↦ ?_⟩
  -- the standard refinement is itself an h covering, so its base change to `Z` separates `G`
  have hWcov : IsHCoveringOver g := isHCoveringOver_of_isStandardHCovering hU.1 W g hstd
  refine (isSeparatedFor_of_isStandardAffineHSheaf haG hG Z _
    (fun j ↦ pullback.fst q (g j)) (hWcov.pullback_of_isAffine q)).ext ?_
  rintro A h ⟨j⟩
  have h₁ : pullback.fst q (g j) ≫ q = pullback.snd q (g j) ≫ g j := pullback.condition
  have h₂ : (pullback.snd q (g j) ≫ (c j ≫ pullback.snd p (f (a j)))) ≫ f (a j)
      = (pullback.fst q (g j) ≫ r) ≫ f i := by
    simp only [Category.assoc]
    rw [← hgd j, ← hqr, ← Category.assoc, ← Category.assoc, ← h₁]
  rw [map_map_apply, map_map_apply, h₁, ← map_map_apply, ht j, map_map_apply]
  exact hs _ _ _ _ _ h₂

/-- **The reduction to the standard affine case.** A Zariski sheaf on `Sch/S` which satisfies the
sheaf condition for the standard h coverings of the affine objects lying over an affine open of
`S` satisfies the sheaf condition for every h covering.

An object of `Sch/S` is covered by its affine opens lying over affine opens of `S`; over each of
them the given covering is refined by a standard h covering, which produces a local section
(`AlgebraicGeometry.ExtendingFunctors.exists_section_of_isStandardAffineHSheaf`); the local
sections agree on the pairwise intersections because both restrictions are computed by the given
family over the base change of the covering to the intersection, and they glue by the Zariski
sheaf condition. -/
theorem isHSheaf_of_isStandardAffineHSheaf {G : (Over S)ᵒᵖ ⥤ Type w}
    (haG : IsZariskiSheaf G) (hG : IsStandardAffineHSheaf.{w, u, max u v} G) :
    IsHSheaf.{w, u, v} G := by
  intro ι X Yc f hf
  refine (isSeparatedFor_of_isStandardAffineHSheaf haG hG X Yc f hf).isSheafFor ?_
  intro x hx
  have hs : ∀ (i i' : ι) (A : Over S) (α : A ⟶ Yc i) (β : A ⟶ Yc i'), α ≫ f i = β ≫ f i' →
      G.map α.op (x (f i) (Presieve.ofArrows.mk i))
        = G.map β.op (x (f i') (Presieve.ofArrows.mk i')) :=
    fun i i' A α β h ↦ hx α β (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk i') h
  obtain ⟨κ₀, V, hVcov, hVaff⟩ := exists_isAffineOverAffineOpen_cover X
  choose tt htt using fun k : κ₀ ↦ exists_section_of_isStandardAffineHSheaf haG hG f
    (fun i ↦ x (f i) (Presieve.ofArrows.mk i)) hs (hVaff k) (overOpenι X (V k))
    (hf.pullback_of_isOpenImmersion (overOpenι X (V k)))
  -- the local sections agree on the pairwise intersections
  have hcompat : ∀ k l : κ₀,
      G.map (overOpenLE X (inf_le_left : V k ⊓ V l ≤ V k)).op (tt k)
        = G.map (overOpenLE X (inf_le_right : V k ⊓ V l ≤ V l)).op (tt l) := by
    intro k l
    refine (isSeparatedFor_of_isStandardAffineHSheaf haG hG (overOpen X (V k ⊓ V l)) _
      (fun i ↦ pullback.fst (overOpenι X (V k ⊓ V l)) (f i))
      (hf.pullback_of_isOpenImmersion (overOpenι X (V k ⊓ V l)))).ext ?_
    intro A h hh
    obtain ⟨i⟩ := hh
    have e₁ : ∀ {W : X.left.Opens} (hW : V k ⊓ V l ≤ W),
        (pullback.fst (overOpenι X (V k ⊓ V l)) (f i) ≫ overOpenLE X hW) ≫ overOpenι X W
          = pullback.snd (overOpenι X (V k ⊓ V l)) (f i) ≫ f i := fun hW ↦ by
      rw [Category.assoc, overOpenLE_comp_overOpenι, pullback.condition]
    rw [map_map_apply, map_map_apply, htt k _ _ i _ (e₁ inf_le_left),
      htt l _ _ i _ (e₁ inf_le_right)]
  obtain ⟨t, hts, -⟩ := haG X κ₀ V hVcov tt hcompat
  refine ⟨t, ?_⟩
  intro A h hh
  obtain ⟨i⟩ := hh
  -- the glued section restricts to the given family over each member of the covering
  refine zariskiSheaf_ext haG (fun k : κ₀ ↦ (f i).left ⁻¹ᵁ V k) ?_ _ _ fun k ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, hVcov, Scheme.Hom.preimage_top]
  have hr : Set.range (⇑(overOpenι (Yc i) ((f i).left ⁻¹ᵁ V k) ≫ f i).left)
      ⊆ ((V k : X.left.Opens) : Set X.left) := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  have hlift := liftOverOpen_comp_overOpenι (overOpenι (Yc i) ((f i).left ⁻¹ᵁ V k) ≫ f i) (V k) hr
  rw [map_map_apply, ← hlift, ← map_map_apply, hts k,
    htt k _ _ i (overOpenι (Yc i) ((f i).left ⁻¹ᵁ V k)) hlift]

/-! ### The h sheaf condition read for the extension -/

/-- **The h sheaf condition read for the extension.** Let `V` be an object of the full subcategory
and let `{f i : W i ⟶ V}` be an h covering of `Sch/S` each of whose members is isomorphic to an
object of the full subcategory. Then the extension satisfies the sheaf condition for `{f i}`.

This is the sheaf condition read off at a stage of the presentation of Stacks 0EV3. Neither the
members of the covering nor, after base change, the fibre products are literally objects of the
subcategory; replacing them by isomorphic objects of the subcategory changes neither the property
of being an h covering (`AlgebraicGeometry.IsHCovering.of_iso`) nor the sheaf condition
(`AlgebraicGeometry.ExtendingFunctors.isSheafFor_ofArrows_of_iso`), after which the h sheaf
condition on the subcategory applies and
`AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isSheafFor` passes from the
subcategory to `Sch/S`. -/
theorem isSheafFor_extension_of_isHCoveringOver
    {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hcF : IsHCoveringSheafOnSubcategory.{max w (u + 1), u, u} P F)
    {V : Over S} (hPV : P V) {ι : Type u} (W : ι → Over S) (f : ∀ i, W i ⟶ V)
    (hWmem : ∀ i, ∃ Z : Over S, P Z ∧ Nonempty (W i ≅ Z))
    (hcov : IsHCoveringOver f) :
    (Presieve.ofArrows W f).IsSheafFor (extension P F) := by
  classical
  choose Z hZ hziso using hWmem
  let ε : ∀ i, W i ≅ Z i := fun i ↦ (hziso i).some
  let V' : P.FullSubcategory := ⟨V, hPV⟩
  let Z' : ι → P.FullSubcategory := fun i ↦ ⟨Z i, hZ i⟩
  let fZ : ∀ i, Z' i ⟶ V' := fun i ↦ ObjectProperty.homMk ((ε i).inv ≫ f i)
  have hcov' : IsHCoveringOver (fun i ↦ P.ι.map (fZ i)) :=
    hcov.of_iso (fun i ↦ ((Over.forget S).mapIso (ε i)).symm) fun i ↦ rfl
  have hshE : (Presieve.ofArrows (fun i ↦ (Z' i).obj) (fun i ↦ (fZ i).hom)).IsSheafFor
      (extension P F) :=
    isSheafFor_extension_of_isSheafFor F hP1 hP2 haF hbF V' Z' fZ (hcF V' Z' fZ hcov')
  refine isSheafFor_ofArrows_of_iso (Iso.refl V) ε f (fun i ↦ (ε i).inv ≫ f i)
    (fun i ↦ ?_) hshE
  rw [Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

/-! ### The restricted sheaf condition for the extension -/

/-- Let `b : B ⟶ X` be a morphism of `Sch/S` and `F` a family of morphisms of schemes into the
underlying scheme of `X`. A family `f` into `B` whose underlying family of schemes is isomorphic to
the base change of `F` along `b` generates the same sieve as the base change along `b` of `F`, read
in `Sch/S`. -/
private theorem generate_ofArrows_pullback_eq_of_iso {X B : Over S} (b : B ⟶ X)
    (F : PreZeroHypercover.{u} X.left) {ι : Type u} {W : ι → Over S} (f : ∀ j, W j ⟶ B)
    (α : F.pullback₂ b.left ≅ { I₀ := ι, X := fun j ↦ (W j).left, f := fun j ↦ (f j).left }) :
    Sieve.generate (Presieve.ofArrows
        (fun k ↦ Limits.pullback b (Over.homMk (U := Over.mk (F.f k ≫ X.hom)) (F.f k) rfl))
        fun k ↦ Limits.pullback.fst b (Over.homMk (U := Over.mk (F.f k ≫ X.hom)) (F.f k) rfl)) =
      Sieve.generate (Presieve.ofArrows W f) := by
  set s : ∀ k, Over.mk (F.f k ≫ X.hom) ⟶ X := fun k ↦ Over.homMk (F.f k) rfl
  -- the fibre product in `Sch/S` computed on the underlying schemes
  have hpb : ∀ k, IsPullback (Limits.pullback.snd b (s k)).left (Limits.pullback.fst b (s k)).left
      (s k).left b.left := fun k ↦ (isPullback_left _ (s k)).flip
  -- the two refinement morphisms of the descent, read in `Sch/S`
  have hγ : ∀ k, ((hpb k).isoPullback.hom ≫ α.hom.h₀ k) ≫ (f (α.hom.s₀ k)).left
      = (Limits.pullback.fst b (s k)).left := fun k ↦
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ (hpb k).isoPullback.hom ≫ z) (α.hom.w₀ k)).trans
        (hpb k).isoPullback_hom_snd)
  have hγ' : ∀ j, (α.inv.h₀ j ≫ (hpb (α.inv.s₀ j)).isoPullback.inv)
      ≫ (Limits.pullback.fst b (s (α.inv.s₀ j))).left = (f j).left := fun j ↦
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ α.inv.h₀ j ≫ z) (hpb (α.inv.s₀ j)).isoPullback_inv_snd).trans
        (α.inv.w₀ j))
  refine le_antisymm ?_ ?_
  · exact generate_ofArrows_le _ _ _ _ α.hom.s₀
      (fun k ↦ Over.homMk ((hpb k).isoPullback.hom ≫ α.hom.h₀ k)
        (comp_hom_of_comp_left (Limits.pullback.fst b (s k)) (f (α.hom.s₀ k)) _ (hγ k)))
      fun k ↦ Over.OverMorphism.ext (hγ k)
  · exact generate_ofArrows_le _ _ _ _ α.inv.s₀
      (fun j ↦ Over.homMk (α.inv.h₀ j ≫ (hpb (α.inv.s₀ j)).isoPullback.inv)
        (comp_hom_of_comp_left (f j) (Limits.pullback.fst b (s (α.inv.s₀ j))) _ (hγ' j)))
      fun j ↦ Over.OverMorphism.ext (hγ' j)

/-- **The restricted sheaf condition for the extension of an h sheaf.** Let `S` be a scheme, let
`𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2) of Stacks 0EUW and let
`F : 𝒞ᵒᵖ ⥤ Set` be an h sheaf satisfying condition (b) of Stacks 0EUW. Then the extension of `F`
to `Sch/S` satisfies the sheaf condition for every standard h covering of every affine object of
`Sch/S` lying over an affine open of `S`.

The affine object is written as a directed inverse limit of affines of finite presentation over an
affine open of `S` (Stacks 00QN,
`AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation_finitePresentation`), the standard h
covering is descended to a stage of that limit (Stacks 0EV2 part (1),
`AlgebraicGeometry.exists_isStandardHCovering_model_of_isLimit`), the sheaf condition is read off
at every stage by `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isHCoveringOver`
and passed to the limit by
`AlgebraicGeometry.ExtendingFunctors.isSheafFor_pullback_fst_of_stagewise`. -/
theorem isStandardAffineHSheaf_extension
    {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hcF : IsHCoveringSheafOnSubcategory.{max w (u + 1), u, u} P F) :
    IsStandardAffineHSheaf.{max w (u + 1), u, v} (extension P F) := by
  classical
  intro ι V hV W₀ f₀ hstd₀
  have hVaff : IsAffine V.left := hV.1
  have hfin₀ : Finite ι := hstd₀.1
  -- reindex the covering by a type in the universe of the schemes
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin ι
  let e : ULift.{u} (Fin n) ≃ ι := Equiv.ulift.trans eqv.symm
  rw [← ofArrows_reindex W₀ f₀ e]
  set W : ULift.{u} (Fin n) → Over S := fun j ↦ W₀ (e j)
  set f : ∀ j, W j ⟶ V := fun j ↦ f₀ (e j)
  obtain ⟨-, haff₀, hfp₀, hh₀⟩ := (isStandardHCovering_iff_isHCovering _).1 hstd₀
  have hstd : @IsStandardHCovering V.left hVaff _ (fun j ↦ (W j).left)
      (fun j ↦ (f j).left) :=
    (isStandardHCovering_iff_isHCovering _).2
      ⟨inferInstance, fun j ↦ haff₀ (e j), fun j ↦ hfp₀ (e j), hh₀.reindex e⟩
  -- the presentation of `V` by affines of finite presentation over an affine open of `S`
  obtain ⟨Λ, _, _, _, D, π₀, hπ₀, U, g₀, haffD, hgUD, hgfpD⟩ :=
    exists_lfpPresentation_finitePresentation hP2 V hV
  have hDaff : ∀ l, IsAffine (((D ⋙ (lfpPart P).ι) ⋙ Over.forget S).obj l) := haffD
  -- the descent of the covering to a stage, Stacks 0EV2 part (1)
  obtain ⟨l, F₀, hF₀, ⟨α⟩⟩ := exists_isStandardHCovering_model_of_isLimit
    ((D ⋙ (lfpPart P).ι) ⋙ Over.forget S) ((Over.forget S).mapCone (Cone.mk V π₀))
    (isLimitMapConeForgetOfDirected hπ₀)
    ({ I₀ := ULift.{u} (Fin n), X := fun j ↦ (W j).left, f := fun j ↦ (f j).left } :
      PreZeroHypercover.{u} V.left) hstd
  have hF₀fin : Finite F₀.I₀ := hF₀.1
  -- the presentation restricted to the stages above `l`
  have hdir : IsDirectedOrder ↥(Set.Ici l.unop) := isDirectedOrder_Ici l.unop
  let _ : OrderBot ↥(Set.Ici l.unop) := Set.Ici.orderBot
  set M := ↥(Set.Ici l.unop)
  set E : Mᵒᵖ ⥤ Over S := (iciIncl l.unop).op ⋙ D ⋙ (lfpPart P).ι
  set cE : Cone E := Cone.whisker (iciIncl l.unop).op (Cone.mk V π₀)
  have hcE : IsLimit cE := isLimitWhiskerIciIncl l.unop (Cone.mk V π₀) hπ₀
  have hPE : ∀ m, lfpPart P (E.obj m) := fun m ↦ (D.obj _).property
  have haffE : ∀ m, IsAffine (E.obj m).left := fun m ↦ haffD _
  have hgUE : ∀ m, g₀ ((iciIncl l.unop).op.obj m) ≫ U.1.ι = (E.obj m).hom := fun m ↦ hgUD _
  have hgfpE : ∀ m, FinitePresentation (g₀ ((iciIncl l.unop).op.obj m)) := fun m ↦ hgfpD _
  have hbotaff : IsAffine (E.obj (op (⊥ : M))).left := haffE _
  -- the descended covering, read in `Sch/S` over the least stage
  set T : F₀.I₀ → Over S := fun k ↦ Over.mk (F₀.f k ≫ (D.obj l).obj.hom)
  set s : ∀ k, T k ⟶ E.obj (op (⊥ : M)) := fun k ↦ Over.homMk (F₀.f k) rfl
  have hTaff : ∀ k, IsAffine (T k).left := fun k ↦ hF₀.2.1 k
  have hTfp : ∀ k, FinitePresentation (s k).left := fun k ↦ hF₀.2.2.1 k
  have hscov : IsHCoveringOver s := hF₀.isHCovering
  -- the sheaf condition at every stage
  have hstage : ∀ m : Mᵒᵖ,
      (Presieve.ofArrows (fun k ↦ Limits.pullback ((toBottom E).app m) (s k))
        (fun k ↦ Limits.pullback.fst ((toBottom E).app m) (s k))).IsSheafFor (extension P F) := by
    intro m
    refine isSheafFor_extension_of_isHCoveringOver F hP1 hP2 haF hbF hcF (hPE m).1 _ _
      (fun k ↦ ?_) (hscov.pullback_of_isAffine ((toBottom E).app m))
    obtain ⟨Y, hY, hYiso⟩ := exists_lfpPart_iso_baseChange hP2 E haffE U
      (fun m ↦ g₀ ((iciIncl l.unop).op.obj m)) hgUE hgfpE (s k) (hTaff k) (hTfp k) m
    exact ⟨Y, hY.1, hYiso⟩
  -- the interchange: the sheaf condition for the base change of the covering to `V`
  exact isSheafFor_of_generate_eq
    (generate_ofArrows_pullback_eq_of_iso (cE.π.app (op (⊥ : M))) F₀ f α)
    (isSheafFor_pullback_fst_of_stagewise F hP1 hP2 haF E haffE cE hcE T s hTaff hstage)

/-! ### The two conclusions at the extension -/

/-- **Stacks 0EV3, the sheaf condition for all h coverings.** Let `S` be a scheme contained in a
big h site, let `𝒞 = (Sch/S)_h` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW and let `F : 𝒞ᵒᵖ ⥤ Set` be an h sheaf satisfying condition (b) of Stacks 0EUW.
Then the extension `F' = AlgebraicGeometry.ExtendingFunctors.extension` of `F` to all schemes
over `S` satisfies the sheaf condition for every h covering of every scheme over `S`.

The reduction to the standard h coverings of the affine objects lying over an affine open of `S`
is `AlgebraicGeometry.ExtendingFunctors.isHSheaf_of_isStandardAffineHSheaf`, and the restricted
sheaf condition is deduced from the h sheaf property of `F` by
`AlgebraicGeometry.ExtendingFunctors.isStandardAffineHSheaf_extension`, through the descent of a
standard h covering along a directed limit of affines, Stacks 0EV2. -/
@[stacks 0EV3 "the sheaf condition for all h coverings"]
theorem isHSheaf_extension (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P)
    (hF : IsHCoveringSheafOnSubcategory.{max w (u + 1), u, u} P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) :
    IsHSheaf.{max w (u + 1), u, v} (extension P F) :=
  isHSheaf_of_isStandardAffineHSheaf (isZariskiSheaf_extension P F hP1 hP2
      (isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory hP1 hF))
    (isStandardAffineHSheaf_extension F hP1 hP2
      (isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory hP1 hF) hbF hF)

/-- **Stacks 0EV3, limit preserving.** For `S` a scheme contained in a big h site, `𝒞 = (Sch/S)_h`
a full subcategory of `Sch/S` satisfying conditions (1) and (2) of Stacks 0EUW and `F : 𝒞ᵒᵖ ⥤ Set`
an h sheaf, the extension `F' = AlgebraicGeometry.ExtendingFunctors.extension` of `F` to all
schemes over `S` is limit preserving in the sense of Limits, Remark 05LX: it carries a directed
inverse limit of affine schemes over `S` to a filtered colimit. -/
@[stacks 0EV3 "limit preserving: the extension carries a directed inverse limit of affine schemes
over the base to a filtered colimit"]
theorem isLimitPreserving_extension (P : ObjectProperty (Over S))
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))) (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P)
    (hF : IsHCoveringSheafOnSubcategory.{max w (u + 1), u, u} P F) :
    PreservesAffineLimits (extension P F) :=
  preservesAffineLimits_extension F hP1 hP2
    (isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory hP1 hF)

end ExtendingFunctors

end AlgebraicGeometry

end
