module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.FibreProductOpenImmersion
public import StacksFrontier.RingTheory.FibreProduct.FilteredColimit

/-!
# The system of fibre products over a filtered colimit of rings

Let `R` be the colimit of a filtered diagram `F` of commutative rings and let `s : B ⟶ R`.
Forming the fibre product with `B` over `R` at every stage gives a new diagram
`j ↦ B ×_R F.obj j`, whose colimit is `B` itself.

`StacksFrontier.RingTheory.FibreProduct.FilteredColimit` proves that colimit statement for *any*
diagram whose stages sit in the relevant cartesian squares, but leaves the diagram itself to
the caller.  This file constructs it, out of Mathlib's concrete pullback cone in `CommRingCat`,
so that the two halves can be used together.

This is the construction the Stacks proof of Tag 07RN performs after identifying
`R = Γ(W, 𝒪_W)` with `colim_i Γ(W_i, 𝒪_{W_i})`: with `B = Γ(U, 𝒪_U)` for the affine open `U`
being added, it sets `B_i = {(b, r) ∈ B × R_i | s(b) = t_i(r)}`, observes that `B = colim_i B_i`,
and then shows that `W_i ⟶ Spec(R_i) ⟶ Spec(B_i)` is an open immersion.  The last step is Tag
01Z9, which is available as
`AlgebraicGeometry.isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback`; the cartesian
square it consumes is supplied here by `RingFibreProduct.isPullback_fibreProductSystem`.

## Main definitions

* `RingFibreProduct.fibreProductSystem`: the diagram `j ↦ B ×_R F.obj j`.
* `RingFibreProduct.fibreProductSystemFst`, `RingFibreProduct.fibreProductSystemSnd`: its two
  projections, onto the constant diagram `B` and onto `F`.

## Main results

* `RingFibreProduct.isPullback_fibreProductSystem`: each stage of the diagram really is the
  fibre product, recorded as a cartesian square.
* `RingFibreProduct.nonempty_isColimit_fibreProductSystem`: `B` is the filtered colimit of the
  fibre products, with the first projections as the colimit cocone.
* `RingFibreProduct.exists_stage_lift_of_isColimit`: finitely many elements of a filtered
  colimit of rings are simultaneously images from a single stage.  This is the step of the
  Stacks proof reading "since `R = colim_i R_i` we can, after shrinking `I`, assume there exist
  `g_{l, i} ∈ R_i` with `s(g_l) = t_i(g_{l, i})`".
* `RingFibreProduct.isOpenImmersion_iSup_basicOpen_comp_specMap_snd`: Tag 01Z9 applied to the
  system, i.e. a finite union of standard opens of `Spec R_i` whose defining elements descend
  from `B` maps by an open immersion to `Spec B_i`.

## Implementation notes

The stages are Mathlib's `CommRingCat.pullbackCone`, and the transition maps are obtained from
its universal property rather than written out on elements; functoriality is then two
applications of `CategoryTheory.IsPullback.hom_ext`.  Keeping the construction at that level of
abstraction is what makes the two coercion round-trips needed to feed Tag 01Z9 — which is
stated for bare types carrying `CommRing` instances — hold by `rfl`, so no bridging lemma and
no transparency lever is required.

No `@[stacks]` attribute is attached to any declaration below.  Tag 01Z9 is carried by
`AlgebraicGeometry.isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback`, and Tag 07RN
asserts the whole of Noetherian approximation, of which this file is one step.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace RingFibreProduct

variable {K : Type u} [Category.{u} K] {F : K ⥤ CommRingCat.{u}} (c : Cocone F)
  {B : CommRingCat.{u}} (s : B ⟶ c.pt)

/-- Mathlib's concrete pullback cone in `CommRingCat`, read as a cartesian square.  Its point
is the fibre product `B ×_R F.obj j`. -/
lemma isPullback_fibreProductCone (j : K) :
    IsPullback (CommRingCat.pullbackCone s (c.ι.app j)).fst
      (CommRingCat.pullbackCone s (c.ι.app j)).snd s (c.ι.app j) :=
  IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit s (c.ι.app j))

/-- **The diagram of fibre products `j ↦ B ×_R F.obj j`.**  Its transition maps are the ones
induced on fibre products by the transition maps of `F`, the first component being left
unchanged. -/
noncomputable def fibreProductSystem : K ⥤ CommRingCat.{u} where
  obj j := (CommRingCat.pullbackCone s (c.ι.app j)).pt
  map {j k} φ := (isPullback_fibreProductCone c s k).lift
    (CommRingCat.pullbackCone s (c.ι.app j)).fst
    ((CommRingCat.pullbackCone s (c.ι.app j)).snd ≫ F.map φ) (by
      rw [Category.assoc, c.w φ]
      exact (CommRingCat.pullbackCone s (c.ι.app j)).condition)
  map_id j := by
    refine (isPullback_fibreProductCone c s j).hom_ext ?_ ?_
    · rw [IsPullback.lift_fst, Category.id_comp]
    · rw [IsPullback.lift_snd, Category.id_comp, F.map_id, Category.comp_id]
  map_comp {j k l} φ ψ := by
    refine (isPullback_fibreProductCone c s l).hom_ext ?_ ?_
    · rw [IsPullback.lift_fst, Category.assoc, IsPullback.lift_fst, IsPullback.lift_fst]
    · rw [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd, ← Category.assoc,
        IsPullback.lift_snd, Category.assoc, F.map_comp]

/-- The projection of the system of fibre products onto `B`. -/
noncomputable def fibreProductSystemFst :
    fibreProductSystem c s ⟶ (Functor.const K).obj B where
  app j := (CommRingCat.pullbackCone s (c.ι.app j)).fst
  naturality _ _ _ := (IsPullback.lift_fst _ _ _ _).trans (Category.comp_id _).symm

/-- The projection of the system of fibre products onto the original system. -/
noncomputable def fibreProductSystemSnd : fibreProductSystem c s ⟶ F where
  app j := (CommRingCat.pullbackCone s (c.ι.app j)).snd
  naturality _ _ _ := IsPullback.lift_snd _ _ _ _

/-- **Each stage of the system is the fibre product `B ×_R F.obj j`**, as a cartesian square.
This is the input that Tag 01Z9 consumes. -/
lemma isPullback_fibreProductSystem (j : K) :
    IsPullback ((fibreProductSystemFst c s).app j) ((fibreProductSystemSnd c s).app j)
      s (c.ι.app j) :=
  isPullback_fibreProductCone c s j

/-- **`B` is the filtered colimit of the fibre products `B ×_R F.obj j`**, the colimit cocone
being given by the first projections. -/
theorem nonempty_isColimit_fibreProductSystem [IsFiltered K] (hc : IsColimit c) :
    Nonempty (IsColimit (Cocone.mk B (fibreProductSystemFst c s))) :=
  nonempty_isColimit_of_isPullback s (fibreProductSystemFst c s) (fibreProductSystemSnd c s) hc
    (isPullback_fibreProductSystem c s)

/-- **Finitely many elements of a filtered colimit of rings are all images from one stage.**
The Stacks proof of Tag 07RN uses this to produce the elements `g_{l, i} ∈ R_i` lifting the
images in `R` of a finite set of elements of `B`. -/
theorem exists_stage_lift_of_isColimit [IsFiltered K] (hc : IsColimit c)
    {ι : Type*} [Finite ι] (x : ι → c.pt) :
    ∃ (j : K) (y : ι → F.obj j), ∀ l, c.ι.app j (y l) = x l := by
  classical
  cases nonempty_fintype ι
  have hcT : IsColimit ((forget CommRingCat.{u}).mapCocone c) := isColimitOfPreserves _ hc
  have hone : ∀ l : ι, ∃ (j : K) (y : F.obj j), c.ι.app j y = x l := fun l => by
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcT (x l)
    exact ⟨j, y, hy⟩
  choose j y hy using hone
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists (Finset.image j Finset.univ)
  have hφ : ∀ l : ι, Nonempty (j l ⟶ S) := fun l =>
    hS (Finset.mem_image_of_mem j (Finset.mem_univ l))
  exact ⟨S, fun l => F.map (hφ l).some (y l), fun l => by simp [hy l]⟩

open AlgebraicGeometry in
/-- **Tag 01Z9 for the system of fibre products.**  A finite union of standard opens of
`Spec (F.obj j)` whose defining elements become, in `R`, the images of elements of `B` on which
`B` and `R` have the same localization, maps by an open immersion to `Spec (B ×_R F.obj j)`.

In the Stacks proof of Tag 07RN this is the sentence "we conclude that the morphism
`W_i ⟶ Spec(R_i) ⟶ Spec(B_i)` is an open immersion", the union being the image of the
quasi-affine open `W_i` in `Spec(R_i)`. -/
theorem isOpenImmersion_iSup_basicOpen_comp_specMap_snd
    (j : K) {n : ℕ} (f : Fin n → F.obj j) (g : Fin n → B)
    (hfg : ∀ l, c.ι.app j (f l) = s (g l))
    (hloc : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l))) :
    IsOpenImmersion
      ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec (F.obj j)).Opens).ι ≫
        Spec.map ((fibreProductSystemSnd c s).app j)) :=
  isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback s.hom
    ((fibreProductSystemFst c s).app j).hom ((fibreProductSystemSnd c s).app j).hom
    (c.ι.app j).hom (by simpa using isPullback_fibreProductSystem c s j) f g hfg hloc

end RingFibreProduct

end
