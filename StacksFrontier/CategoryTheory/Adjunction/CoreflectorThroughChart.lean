module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda

/-!
# A coreflector computed through a chart

Let `i : D ⥤ C` be a functor with a right adjoint `Q`, and let `r : C ⥤ A` be a functor such
that `i ⋙ r` is an equivalence of categories.  This is the formal situation of the coherator
of an algebraic stack (Stacks 0778, 0779): `i` is the inclusion of quasi-coherent modules into
a category of modules, `Q` is the coherator, and `r` is the restriction to a smooth chart
`U → 𝒳`, valued in quasi-coherent modules on the groupoid `(U, R, s, t, c)`, through which the
source computes `Q`.

The one input the source reads off the chart beyond the equivalence is that maps out of a
quasi-coherent module are computed on the chart (Stacks 076S): for an object `M` of `C`,
`f ↦ r f` is a bijection `Hom(i G, M) ≃ Hom(r (i G), r M)` for every `G`.  From that bijection
alone the adjunction map `Q M ⟶ M` becomes an isomorphism after applying `r`
(`CategoryTheory.Adjunction.isIso_map_counit_app_of_bijective`), and everything the source says
about `Q` in Stacks 0779 follows formally:

* `Q M` vanishes exactly when `r M` does
  (`CategoryTheory.Adjunction.isZero_obj_iff_isZero_map_obj_of_isIso`);
* `r` kills the kernel and the cokernel of `Q M ⟶ M`, as soon as `r` preserves them
  (`CategoryTheory.Adjunction.isZero_map_kernelFork_pt_of_isIso`,
  `CategoryTheory.Adjunction.isZero_map_cokernelCofork_pt_of_isIso`);
* `Q` preserves every colimit that `r` preserves, of a diagram whose objects and colimit all
  have that property (`CategoryTheory.Adjunction.isColimit_mapCocone_of_isIso`).

In each statement the isomorphism `r (Q M ⟶ M)` is asked only at the objects involved, so a
consumer may restrict to a full subcategory of `C`, such as the locally quasi-coherent modules
with the flat base change property, on which the bijection is available.

## Main results

* `CategoryTheory.Adjunction.isIso_map_counit_app_of_bijective`
* `CategoryTheory.Adjunction.isZero_obj_iff_isZero_map_obj_of_isIso`
* `CategoryTheory.Adjunction.isZero_map_kernelFork_pt_of_isIso`
* `CategoryTheory.Adjunction.isZero_map_cokernelCofork_pt_of_isIso`
* `CategoryTheory.Adjunction.isColimit_mapCocone_of_isIso`

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ w w'

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {i : D ⥤ C} {Q : C ⥤ D} (adj : i ⊣ Q) (r : C ⥤ A)

/-- **The adjunction map becomes an isomorphism on the chart.**  If `i ⋙ r` is an equivalence
and `f ↦ r f` is a bijection `Hom(i G, M) ≃ Hom(r (i G), r M)` for every `G`, then `r` sends the
adjunction map `i (Q M) ⟶ M` to an isomorphism.

By Yoneda it suffices to test against the objects `r (i G)`, which are all objects of `A` up to
isomorphism; there, composition with `r (i (Q M) ⟶ M)` is the composite of the inverse of the
bijection `g ↦ r (i g)` of the equivalence, the adjunction bijection, and the given bijection. -/
theorem isIso_map_counit_app_of_bijective [(i ⋙ r).IsEquivalence] (M : C)
    (h : ∀ G : D, Function.Bijective (fun f : i.obj G ⟶ M => r.map f)) :
    IsIso (r.map (adj.counit.app M)) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  let e := (i ⋙ r).objObjPreimageIso T
  set G := (i ⋙ r).objPreimage T
  have key : Function.Bijective
      (fun x : (i ⋙ r).obj G ⟶ r.obj (i.obj (Q.obj M)) => x ≫ r.map (adj.counit.app M)) := by
    have h₁ : Function.Bijective (fun g : G ⟶ Q.obj M => (i ⋙ r).map g) :=
      (Functor.FullyFaithful.ofFullyFaithful (i ⋙ r)).map_bijective G (Q.obj M)
    rw [← Function.Bijective.of_comp_iff _ h₁]
    have h₂ : (fun x : (i ⋙ r).obj G ⟶ r.obj (i.obj (Q.obj M)) =>
          x ≫ r.map (adj.counit.app M)) ∘ (fun g : G ⟶ Q.obj M => (i ⋙ r).map g) =
        (fun f : i.obj G ⟶ M => r.map f) ∘ (adj.homEquiv G M).symm := by
      funext g
      simp [Adjunction.homEquiv_counit]
    rw [h₂]
    exact (h G).comp (adj.homEquiv G M).symm.bijective
  have hpre : Function.Bijective (fun x : T ⟶ r.obj (i.obj (Q.obj M)) => e.hom ≫ x) :=
    ⟨fun x y hxy => by simpa using congrArg (e.inv ≫ ·) hxy,
      fun y => ⟨e.inv ≫ y, by simp⟩⟩
  have hpost : Function.Bijective (fun y : (i ⋙ r).obj G ⟶ r.obj M => e.inv ≫ y) :=
    ⟨fun x y hxy => by simpa using congrArg (e.hom ≫ ·) hxy,
      fun y => ⟨e.hom ≫ y, by simp⟩⟩
  simpa [Function.comp_def] using hpost.comp (key.comp hpre)

/-- **`i ⋙ r` is fully faithful when `r` has a fully faithful left adjoint whose counit is
invertible on the image of `i`.**  A map `r (i G) ⟶ r (i G')` is the transpose of a unique map
`L (r (i G)) ⟶ i G'`, that is of a unique map `i G ⟶ i G'`, that is of a unique map
`G ⟶ G'`. -/
noncomputable def fullyFaithfulCompOfLeftAdjoint [i.Full] [i.Faithful] {L : A ⥤ C}
    (adjL : L ⊣ r) [IsIso adjL.unit] (hc : ∀ G : D, IsIso (adjL.counit.app (i.obj G))) :
    (i ⋙ r).FullyFaithful where
  preimage {G G'} g := i.preimage (inv (adjL.counit.app (i.obj G)) ≫
    (adjL.homEquiv _ _).symm g)
  map_preimage {G G'} g := by
    have := hc G
    have t : ∀ N : C, r.map (adjL.counit.app N) = inv (adjL.unit.app (r.obj N)) := fun N => by
      rw [← cancel_epi (adjL.unit.app (r.obj N))]
      simp
    have nat : r.map (L.map g) =
        inv (adjL.unit.app (r.obj (i.obj G))) ≫ g ≫ adjL.unit.app (r.obj (i.obj G')) := by
      have hn : g ≫ adjL.unit.app (r.obj (i.obj G')) =
          adjL.unit.app (r.obj (i.obj G)) ≫ r.map (L.map g) := adjL.unit.naturality g
      rw [hn]
      simp
    simp only [Functor.comp_map, Functor.map_preimage, Functor.map_comp,
      Adjunction.homEquiv_counit, Functor.map_inv, t, nat]
    simp
  preimage_map {G G'} f := by
    apply i.map_injective
    simp only [Functor.comp_map, Functor.map_preimage, Adjunction.homEquiv_counit]
    rw [IsIso.inv_comp_eq]
    exact adjL.counit_naturality (i.map f)

/-- **Composition with the counit of `L ⊣ r` at `M` is bijective on maps out of `X`**, when the
counit is invertible at `X` and `r` inverts it at `M`: through `X ≅ L (r X)` and the adjunction,
it becomes composition with `r (L (r M) ⟶ M)`. -/
theorem bijective_comp_counit_app {L : A ⥤ C} (adjL : L ⊣ r) {X : C} (M : C)
    [IsIso (adjL.counit.app X)] [IsIso (r.map (adjL.counit.app M))] :
    Function.Bijective (fun f : X ⟶ L.obj (r.obj M) => f ≫ adjL.counit.app M) := by
  let d : L.obj (r.obj X) ≅ X := asIso (adjL.counit.app X)
  have h₁ : Function.Bijective
      (fun f : L.obj (r.obj X) ⟶ L.obj (r.obj M) => f ≫ adjL.counit.app M) := by
    have hpost : Function.Bijective
        (fun g : r.obj X ⟶ r.obj (L.obj (r.obj M)) => g ≫ r.map (adjL.counit.app M)) :=
      ⟨fun x y hxy => (cancel_mono (r.map (adjL.counit.app M))).1 hxy,
        fun y => ⟨y ≫ inv (r.map (adjL.counit.app M)), by simp⟩⟩
    have hconj : (fun f : L.obj (r.obj X) ⟶ L.obj (r.obj M) => f ≫ adjL.counit.app M) =
        (adjL.homEquiv _ _).symm ∘
          (fun g : r.obj X ⟶ r.obj (L.obj (r.obj M)) => g ≫ r.map (adjL.counit.app M)) ∘
            adjL.homEquiv _ _ := by
      funext f
      simp only [Function.comp_apply]
      rw [← Adjunction.homEquiv_naturality_right, Equiv.symm_apply_apply]
    rw [hconj]
    exact (adjL.homEquiv _ _).symm.bijective.comp (hpost.comp (adjL.homEquiv _ _).bijective)
  have hpre : Function.Bijective (fun f : X ⟶ L.obj (r.obj M) => d.hom ≫ f) :=
    ⟨fun x y hxy => (cancel_epi d.hom).1 hxy, fun y => ⟨d.inv ≫ y, by simp⟩⟩
  have hpre' : Function.Bijective (fun g : L.obj (r.obj X) ⟶ M => d.inv ≫ g) :=
    ⟨fun x y hxy => (cancel_epi d.inv).1 hxy, fun y => ⟨d.hom ≫ y, by simp⟩⟩
  simpa [Function.comp_def, d] using hpre'.comp (h₁.comp hpre)

/-- **The adjunction map becomes an isomorphism under a right adjoint which builds objects of
`D`.**  Let `L ⊣ r` with invertible unit, so that `L` is fully faithful.  Suppose that the counit
`L (r (i G)) ⟶ i G` is invertible for every `G`, and that `L (r M)` lies in the essential image
of `i`.  Then `r` inverts the adjunction map `i (Q M) ⟶ M`.

This is the formal half of Stacks 07B1: with `r = g⁻¹` the restriction to the flat-fppf site and
`L = g_!`, the coherator of `M` is `g_! g⁻¹ M`.  Indeed the counit `L (r M) ⟶ M` represents
`G ↦ Hom(i G, M)` on `D`: through the isomorphism `i G ≅ L (r (i G))` and the adjunction,
composition with it becomes composition with `r (L (r M) ⟶ M)`, which the triangle identity
makes invertible. -/
theorem isIso_map_counit_app_of_leftAdjoint [i.Full] [i.Faithful] {L : A ⥤ C} (adjL : L ⊣ r)
    [IsIso adjL.unit] (hc : ∀ G : D, IsIso (adjL.counit.app (i.obj G))) (M : C)
    (hM : i.essImage (L.obj (r.obj M))) : IsIso (r.map (adj.counit.app M)) := by
  obtain ⟨G₀, ⟨e⟩⟩ := hM
  have hrκ : IsIso (r.map (adjL.counit.app M)) :=
    isIso_of_hom_comp_eq_id _ (adjL.right_triangle_components M)
  let α : i.obj G₀ ⟶ M := e.hom ≫ adjL.counit.app M
  let γ : G₀ ⟶ Q.obj M := adj.homEquiv G₀ M α
  have hα : i.map γ ≫ adj.counit.app M = α := by
    simp [γ, Adjunction.homEquiv_unit]
  have hγ : IsIso γ := by
    rw [isIso_iff_yoneda_map_bijective]
    intro T
    have := hc T
    have hcomp : (fun x : T ⟶ G₀ => x ≫ γ) =
        adj.homEquiv T M ∘ (fun f : i.obj T ⟶ L.obj (r.obj M) => f ≫ adjL.counit.app M) ∘
          (fun f : i.obj T ⟶ i.obj G₀ => f ≫ e.hom) ∘ (fun x : T ⟶ G₀ => i.map x) := by
      funext x
      simp only [Function.comp_apply, γ, α, Category.assoc,
        Adjunction.homEquiv_naturality_left]
    rw [hcomp]
    refine (adj.homEquiv T M).bijective.comp
      ((bijective_comp_counit_app r adjL (X := i.obj T) M).comp ?_)
    refine Function.Bijective.comp ?_
      ((Functor.FullyFaithful.ofFullyFaithful i).map_bijective T G₀)
    exact ⟨fun x y hxy => (cancel_mono e.hom).1 hxy, fun y => ⟨y ≫ e.inv, by simp⟩⟩
  have hrα : IsIso (r.map α) := by
    simp only [α, Functor.map_comp]
    infer_instance
  rw [← hα, Functor.map_comp] at hrα
  exact IsIso.of_isIso_comp_left (r.map (i.map γ)) _

/-- **An object is killed by `Q` exactly when it is killed by `r`**, at an object where `r`
inverts the adjunction map: the adjunction map identifies `r (i (Q M))` with `r M`, and the
fully faithful functor `i ⋙ r` preserves and reflects zero objects. -/
theorem isZero_obj_iff_isZero_map_obj_of_isIso [HasZeroMorphisms D] [HasZeroMorphisms A]
    [(i ⋙ r).Full] [(i ⋙ r).Faithful] [(i ⋙ r).PreservesZeroMorphisms] (M : C)
    (hM : IsIso (r.map (adj.counit.app M))) : IsZero (Q.obj M) ↔ IsZero (r.obj M) := by
  have e : r.obj (i.obj (Q.obj M)) ≅ r.obj M := asIso (r.map (adj.counit.app M))
  exact ⟨fun h => ((i ⋙ r).map_isZero h).of_iso e.symm,
    fun h => IsZero.of_full_of_faithful_of_isZero (i ⋙ r) (Q.obj M) (h.of_iso e)⟩

/-- **`r` kills the kernel of the adjunction map**, at an object where it inverts that map,
provided it preserves the kernel. -/
theorem isZero_map_kernelFork_pt_of_isIso [HasZeroMorphisms C] [HasZeroMorphisms A]
    [r.PreservesZeroMorphisms] {M : C} (hM : IsIso (r.map (adj.counit.app M)))
    {c : KernelFork (adj.counit.app M)} (hc : IsLimit c)
    [PreservesLimit (parallelPair (adj.counit.app M) 0) r] : IsZero (r.obj c.pt) :=
  KernelFork.IsLimit.isZero_of_mono (KernelFork.mapIsLimit c hc r)

/-- **`r` kills the cokernel of the adjunction map**, at an object where it inverts that map,
provided it preserves the cokernel. -/
theorem isZero_map_cokernelCofork_pt_of_isIso [HasZeroMorphisms C] [HasZeroMorphisms A]
    [r.PreservesZeroMorphisms] {M : C} (hM : IsIso (r.map (adj.counit.app M)))
    {c : CokernelCofork (adj.counit.app M)} (hc : IsColimit c)
    [PreservesColimit (parallelPair (adj.counit.app M) 0) r] : IsZero (r.obj c.pt) :=
  CokernelCofork.IsColimit.isZero_of_epi (CokernelCofork.mapIsColimit c hc r)

/-- **`Q` preserves the colimits `r` preserves**, of a diagram at whose objects and at whose
colimit `r` inverts the adjunction map.

Whiskering the adjunction map by `r` gives a natural transformation `Q ⋙ i ⋙ r ⟶ r` whose
components at the objects of the diagram and at the colimit are isomorphisms; so the image of
the colimit cocone under `Q ⋙ i ⋙ r` is isomorphic to its image under `r`, a colimit cocone,
and the fully faithful functor `i ⋙ r` reflects colimits. -/
theorem isColimit_mapCocone_of_isIso [(i ⋙ r).Full] [(i ⋙ r).Faithful] {J : Type w}
    [Category.{w'} J]
    {K : J ⥤ C} (hK : ∀ j, IsIso (r.map (adj.counit.app (K.obj j)))) {c : Cocone K}
    (hc : IsColimit c) (hpt : IsIso (r.map (adj.counit.app c.pt))) [PreservesColimit K r] :
    Nonempty (IsColimit (Q.mapCocone c)) := by
  let α : K ⋙ Q ⋙ i ⋙ r ≅ K ⋙ r :=
    NatIso.ofComponents (fun j => asIso (r.map (adj.counit.app (K.obj j))))
      fun f => by simp [← Functor.map_comp]
  exact ⟨isColimitOfReflects (i ⋙ r)
    (IsColimit.equivOfNatIsoOfIso α.symm (r.mapCocone c) ((Q ⋙ i ⋙ r).mapCocone c)
      (Cocone.ext (asIso (r.map (adj.counit.app c.pt))).symm fun j => by
        simp [α, ← Functor.map_comp]) (isColimitOfPreserves r hc))⟩

section Subcategory

variable (P : ObjectProperty C)

/-- **`Q` restricted to a full subcategory preserves the colimits `r` preserves**, of shapes
whose colimits the subcategory computes in `C`, as soon as `r` inverts the adjunction map at
every object of the subcategory. -/
theorem preservesColimitsOfShape_ι_comp_of_isIso [(i ⋙ r).Full] [(i ⋙ r).Faithful]
    (hP : ∀ M, P M → IsIso (r.map (adj.counit.app M))) (J : Type w) [Category.{w'} J]
    [PreservesColimitsOfShape J P.ι] [PreservesColimitsOfShape J r] :
    PreservesColimitsOfShape J (P.ι ⋙ Q) where
  preservesColimit {K} := ⟨fun {c} hc =>
    isColimit_mapCocone_of_isIso adj r (K := K ⋙ P.ι) (fun j => hP _ (K.obj j).property)
      (isColimitOfPreserves P.ι hc) (hP _ c.pt.property)⟩

/-- **`Q` restricted to a full subcategory is right exact**, when the subcategory computes its
finite colimits in `C`, `r` is right exact, and `r` inverts the adjunction map at every object
of the subcategory. -/
theorem preservesFiniteColimits_ι_comp_of_isIso [(i ⋙ r).Full] [(i ⋙ r).Faithful]
    (hP : ∀ M, P M → IsIso (r.map (adj.counit.app M))) [PreservesFiniteColimits P.ι]
    [PreservesFiniteColimits r] : PreservesFiniteColimits (P.ι ⋙ Q) where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_ι_comp_of_isIso adj r P hP J

include adj in
/-- **`Q` restricted to a full subcategory is left exact**, when the subcategory computes its
finite limits in `C`: `Q` is a right adjoint. -/
theorem preservesFiniteLimits_ι_comp [PreservesFiniteLimits P.ι] :
    PreservesFiniteLimits (P.ι ⋙ Q) :=
  have : PreservesLimitsOfSize.{0, 0} Q := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits Q := PreservesLimitsOfSize.preservesFiniteLimits Q
  comp_preservesFiniteLimits P.ι Q

end Subcategory

end CategoryTheory.Adjunction

end
