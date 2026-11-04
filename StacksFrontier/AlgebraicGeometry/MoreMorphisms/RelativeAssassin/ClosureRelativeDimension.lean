module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FibreDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop

/-!
# The reduced closure of a relative associated point over the reduced closure of its image

Let `f : X ⟶ S` be a morphism of schemes and `y` a point of `X`. The reduced closed subscheme `Y`
supported on the closure of `y` maps to the reduced closed subscheme `T` supported on the closure
of `f y`, and that canonical map `h : Y ⟶ T` is dominant. If moreover `f` is locally of finite
type, `F` is a quasi-coherent `𝒪_X`-module of finite type, `y` lies in `Ass_{X/S}(F)` and `F` is
flat over `S` at every component-generic point of every fibre of `h`, then `h` has constant
relative dimension.

## Main results

* `Stacks.RelativeAssassin.isDominant_closureSubschemeMap`
* `Stacks.RelativeAssassin.relativeDimension_closureSubschemeMap`

## Implementation notes

Both closures carry their canonical reduced closed-subscheme structures, cut out by their
vanishing ideal sheaves, and the canonical map between them is Mathlib's
`Scheme.IdealSheafData.subschemeMap`; its commutative square over `f` is
`Scheme.IdealSheafData.subschemeMap_subschemeι`. Dominance holds because the generic point of `T`
is the image of the generic point of `Y`. For the relative dimension, `T` being a closed
subscheme of `S` identifies each fibre of `h` with the corresponding fibre of `Y ⟶ S`, so the
fibre dimension equality of Tag 0GSI applies to each component-generic point and shows every
component of every fibre to have the dimension of the fibre of `Y` over `f y`; that common value
is finite because the fibre is of finite type over a residue field.

## References

* [Stacks Project, Tag 0GSJ](https://stacks.math.columbia.edu/tag/0GSJ)
* [Stacks Project, Tag 0GSI](https://stacks.math.columbia.edu/tag/0GSI)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.RelativeAssassin

/-- The vanishing ideal sheaf of the closure of the image of a point is contained in the pushout
along the morphism of the vanishing ideal sheaf of the closure of that point. -/
private theorem closureMap_le {X S : Scheme.{u}} (f : X ⟶ S) (y : X) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({f y} : Set S)) ≤
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).map f := by
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  refine le_of_eq (congrArg _ (Closeds.ext ?_))
  show closure ({f y} : Set S) = closure (f '' closure ({y} : Set X))
  exact ((closure_image_closure f.continuous).trans (by simp)).symm

/-- A point whose image under an inducing map has closure containing the range is a generic
point of the whole space. -/
private theorem isGenericPoint_univ_of_range_subset_closure {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {e : A → B} (he : Topology.IsInducing e) {a : A}
    (h : Set.range e ⊆ closure {e a}) : IsGenericPoint a Set.univ := by
  rw [isGenericPoint_def, he.closure_eq_preimage_closure_image, Set.image_singleton]
  exact Set.eq_univ_of_forall fun b => h ⟨b, rfl⟩

/-- The reduced closed subscheme supported on the closure of a point has a generic point, lying
over that point. -/
private theorem exists_genericPoint_closureSubscheme {X : Scheme.{u}} (x : X) :
    let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
    ∃ p : I.subscheme, I.subschemeι p = x ∧ IsGenericPoint p Set.univ := by
  intro I
  have hIsup : (I.support : Set X) = closure ({x} : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  obtain ⟨p, hp⟩ : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι, hIsup]
    exact subset_closure rfl
  exact ⟨p, hp, isGenericPoint_univ_of_range_subset_closure I.subschemeι.isEmbedding.isInducing
    (by rw [hp, ← hIsup, ← I.range_subschemeι])⟩

/-- If a morphism factors through an injective one, each of its fibres is homeomorphic to the
fibre of the composite over the image point. -/
public noncomputable def fiberHomeomorphOfFactor
    {Y T S : Scheme.{u}} (h : Y ⟶ T) (i : T ⟶ S) (g : Y ⟶ S)
    (hcomp : h ≫ i = g) (hi : Function.Injective i) (t : T) :
    h.fiber t ≃ₜ g.fiber (i t) := by
  have hset : h ⁻¹' ({t} : Set T) = g ⁻¹' ({i t} : Set S) := by
    rw [← hcomp]
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
    exact hi.eq_iff.symm
  exact (h.fiberHomeo t).trans
    ((Homeomorph.setCongr hset).trans (g.fiberHomeo (i t)).symm)

/-- A homeomorphism carries irreducible components to irreducible components. -/
private theorem homeomorph_image_mem_irreducibleComponents
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {s : Set X} (hs : s ∈ irreducibleComponents X) :
    e '' s ∈ irreducibleComponents Y := by
  have h := preimage_mem_irreducibleComponents hs e.symm.isOpenEmbedding
    (hs.1.nonempty.mono fun x hx => ⟨hx, e.symm.surjective x⟩)
  rwa [Homeomorph.preimage_symm] at h

/-- On a scheme locally of finite type over a field the local dimension at a point is a natural
number. -/
public theorem exists_nat_eq_topologicalKrullDimAt
    (Z : Scheme.{u}) (k : Type u) [Field k]
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] (z : Z) :
    ∃ n : ℕ, topologicalKrullDimAt Z z = (n : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDimAt_le Z k g z
  have hne := topologicalKrullDimAt_ne_bot z
  generalize hd : topologicalKrullDimAt Z z = d at hne hn
  cases d with
  | bot => exact (hne rfl).elim
  | coe d =>
    have hle : d ≤ (n : ℕ∞) := WithBot.coe_le_coe.mp (by simpa [hd] using hn)
    lift d to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle
    exact ⟨d, rfl⟩

add_to_stacks 0GSJ "part (1)"
  Stacks.RelativeAssassin.mem_relativeAssassin_of_isGenericPoint_fibre_closure

/-- The canonical map from the reduced closure of a point to the reduced closure
of its image is dominant. -/
@[stacks 0GSJ "dominance of the canonical map"]
theorem isDominant_closureSubschemeMap
    {X S : Scheme.{u}} (f : X ⟶ S) (y : X) :
    let Y := Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))
    let T := Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({f y} : Set S))
    let h : Y.subscheme ⟶ T.subscheme :=
      Scheme.IdealSheafData.subschemeMap Y T f (by
        rw [Scheme.IdealSheafData.map_vanishingIdeal]
        apply le_of_eq
        apply congrArg Scheme.IdealSheafData.vanishingIdeal
        apply Closeds.ext
        change closure ({f y} : Set S) = closure (f '' closure ({y} : Set X))
        exact ((closure_image_closure f.continuous).trans (by simp)).symm)
    IsDominant h := by
  intro Y T h
  have hcomp : h ≫ T.subschemeι = Y.subschemeι ≫ f :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ f _
  obtain ⟨p, hp, -⟩ := exists_genericPoint_closureSubscheme y
  obtain ⟨q, hq, hqgen⟩ := exists_genericPoint_closureSubscheme (f y)
  have hpq : h p = q := T.subschemeι.isClosedEmbedding.injective <|
    calc
      T.subschemeι (h p) = (h ≫ T.subschemeι) p := rfl
      _ = (Y.subschemeι ≫ f) p := congrArg (fun k => k p) hcomp
      _ = f y := (congrArg (f ·) hp : f (Y.subschemeι p) = f y)
      _ = T.subschemeι q := hq.symm
  refine ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_univ_subset ?_)⟩
  rw [← hqgen.def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨p, hpq⟩)

/-- The fibre of a morphism locally of finite type is locally of finite type over the residue
field. -/
private theorem locallyOfFiniteType_fiberToSpecResidueField {Y S : Scheme.{u}} (g : Y ⟶ S)
    [LocallyOfFiniteType g] (s : S) : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
  inferInstanceAs <|
    LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd g (S.fromSpecResidueField s))

attribute [local instance] locallyOfFiniteType_fiberToSpecResidueField

/-- For a morphism locally of finite type from a scheme with a generic point, the fibre through
that generic point has finite topological Krull dimension. -/
private theorem exists_nat_eq_topologicalKrullDim_fiber_of_isGenericPoint {Y S : Scheme.{u}}
    (g : Y ⟶ S) [LocallyOfFiniteType g] {p : Y} (hp : IsGenericPoint p Set.univ) {s : S}
    (hps : g p = s) : ∃ d : ℕ, topologicalKrullDim (g.fiber s) = d := by
  subst hps
  let η : g.fiber (g p) := (g.fiberHomeo (g p)).symm ⟨p, rfl⟩
  have hη : IsGenericPoint η Set.univ :=
    isGenericPoint_univ_of_range_subset_closure (g.fiberι (g p)).isEmbedding.isInducing
      (fun _ _ => by simp [η, hp.def])
  obtain ⟨d, hd⟩ := exists_nat_eq_topologicalKrullDimAt
    (g.fiber (g p)) (S.residueField (g p)) (g.fiberToSpecResidueField (g p)) η
  refine ⟨d, ((IsHomeomorph.topologicalKrullDim_eq _
    (Homeomorph.Set.univ (g.fiber (g p))).isHomeomorph).symm.trans ?_).trans hd⟩
  exact topologicalKrullDim_eq_at_generic_component (S.residueField (g p)) (g.fiber (g p))
    (g.fiberToSpecResidueField (g p)) η Set.univ
    ⟨hη.isIrreducible, fun _ _ _ => Set.subset_univ _⟩ hη

/-- A morphism locally of finite type all of whose fibre components have dimension `d` has
relative dimension `d`. -/
private theorem relativeDimension_of_forall_mem_irreducibleComponents {Y T : Scheme.{u}} (h : Y ⟶ T)
    [LocallyOfFiniteType h] (d : ℕ)
    (H : ∀ (t : T) (Z : Set (h.fiber t)), Z ∈ irreducibleComponents (h.fiber t) →
      topologicalKrullDim Z = d) :
    RelativeDimension h d := by
  intro t ⟨x⟩
  have hloc : ∀ x : h.fiber t, topologicalKrullDimAt (h.fiber t) x = d := fun x => by
    obtain ⟨Z, hZ, -, hDim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
        (T.residueField t) (h.fiber t) (h.fiberToSpecResidueField t) x
    exact hDim.symm.trans (H t Z hZ)
  refine ⟨fun Z hZ W hW => by rw [H t Z hZ, H t W hW], ?_⟩
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hloc]
  exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup_of_le x le_rfl)

/-- If the module is flat at component-generic fibre points, the canonical map
from the reduced closure of a relative associated point to the reduced closure
of its image has constant relative dimension. -/
@[stacks 0GSJ "part (2)",
  ega "IV 12.1.1.4" "equidimensional Z'→Y'",
  ega "IV 12.1.1.5" "equidimensionality"]
theorem relativeDimension_closureSubschemeMap
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (y : X) (hy : y ∈ Stacks.Divisors.relativeAssassin f F) :
    let Y := Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))
    let T := Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({f y} : Set S))
    let h : Y.subscheme ⟶ T.subscheme :=
      Scheme.IdealSheafData.subschemeMap Y T f (by
        rw [Scheme.IdealSheafData.map_vanishingIdeal]
        apply le_of_eq
        apply congrArg Scheme.IdealSheafData.vanishingIdeal
        apply Closeds.ext
        change closure ({f y} : Set S) = closure (f '' closure ({y} : Set X))
        exact ((closure_image_closure f.continuous).trans (by simp)).symm)
    (∀ t : T.subscheme, ∀ x : h.fiber t,
      (∃ Z : irreducibleComponents (h.fiber t),
        IsGenericPoint x (Z : Set (h.fiber t))) →
      AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F
        (Y.subschemeι (h.fiberι t x))) →
    let hh : LocallyOfFiniteType h := by
      have : LocallyOfFiniteType (h ≫ T.subschemeι) := by
        rw [Scheme.IdealSheafData.subschemeMap_subschemeι]
        infer_instance
      exact locallyOfFiniteType_of_comp h T.subschemeι
    letI : LocallyOfFiniteType h := hh
    ∃ d : ℕ, RelativeDimension h d := by
  intro Y T h hflat _
  let g : Y.subscheme ⟶ S := Y.subschemeι ≫ f
  have hcomp : h ≫ T.subschemeι = g :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ f _
  have : LocallyOfFiniteType g := by
    rw [← hcomp]
    infer_instance
  obtain ⟨p, hp, hpgen⟩ := exists_genericPoint_closureSubscheme y
  have hgp : g p = f y := (congrArg (f ·) hp : f (Y.subschemeι p) = f y)
  obtain ⟨d, hd⟩ := exists_nat_eq_topologicalKrullDim_fiber_of_isGenericPoint g hpgen hgp
  refine ⟨d, relativeDimension_of_forall_mem_irreducibleComponents h d fun t Z hZ => ?_⟩
  let e := fiberHomeomorphOfFactor h T.subschemeι g hcomp
    T.subschemeι.isClosedEmbedding.injective t
  let x : h.fiber t := genericPoints.ofComponent ⟨Z, hZ⟩
  have hxgen : IsGenericPoint x Z := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
  have hι : g.fiberι (T.subschemeι t) (e x) = h.fiberι t x := by
    show ((g.fiberHomeo (T.subschemeι t)) (e x)).1 = ((h.fiberHomeo t) x).1
    simp [e, fiberHomeomorphOfFactor, Homeomorph.setCongr]
  have hegen : IsGenericPoint (e x) (e '' Z) := by
    simpa only [(e.isClosedMap Z (isClosed_of_mem_irreducibleComponents Z hZ)).closure_eq]
      using hxgen.image e.continuous
  have hflatG : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F
      (Y.subschemeι (g.fiberι (T.subschemeι t) (e x))) := by
    rw [hι]
    exact hflat t x ⟨⟨Z, hZ⟩, hxgen⟩
  refine ((topologicalKrullDim_eq_at_generic_component (T.subscheme.residueField t) (h.fiber t)
    (h.fiberToSpecResidueField t) x Z hZ hxgen).trans
    ((topologicalKrullDimAt_eq_of_homeomorph e x).trans ?_)).trans hd
  exact topologicalKrullDimAt_fiber_eq_fiber_of_flat f F y hy (T.subschemeι t) (e x)
    ⟨⟨e '' Z, homeomorph_image_mem_irreducibleComponents e hZ⟩, hegen⟩ hflatG

end Stacks.RelativeAssassin

end
