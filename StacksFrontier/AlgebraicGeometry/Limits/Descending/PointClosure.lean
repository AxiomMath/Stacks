module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.Reduced
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Closures of points in inverse limits of schemes

Let `D` be a cofiltered diagram of schemes with affine transition morphisms and let `s` be a
point of a limit of `D`. Two descriptions of the closure of `s` are given here: as a set it is
the inverse limit of the closures of the images of `s` in the stages, and as a reduced closed
subscheme it is the inverse limit of the reduced closures of those images.

A directed inverse system is represented more generally by a diagram on a cofiltered category,
and the limiting scheme may be presented by any limiting cone. The set-level equality is stated
by its universal property: every compatible family of points of the stagewise closures lifts
uniquely to a point of the closure in the limit. The scheme-level statement produces a diagram
and a limiting cone whose terms are identified with the canonical reduced closures and whose
maps commute with their inclusions into the stages; those conditions pin the identification down
independently of any choice of model.

## Main results

* `AlgebraicGeometry.existsUnique_mem_closure_singleton_of_compatible`: the closure of a point
  of the limit is the inverse limit of the closures of its images, as a set.
* `AlgebraicGeometry.exists_isLimit_reducedClosures`: the reduced closure of a point of the
  limit is the inverse limit, as a scheme, of the reduced closures of its images.

## Implementation notes

The reduced closure of a point is realised as the closed subscheme cut out by the vanishing
ideal sheaf of the topological closure. On the limit the relevant ideal sheaf is the supremum of
the pullbacks of the stagewise vanishing ideals; that supremum has the right support by the
set-level statement, and its closed subscheme is reduced by
`AlgebraicGeometry.isReduced_cofilteredLimit_of_isReduced`, so it is the vanishing ideal of the
closure of `s`.

## References

* [Stacks Project, Tag 0CUG](https://stacks.math.columbia.edu/tag/0CUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CUG.** The closure of a point in a cofiltered limit of schemes with
affine transition morphisms is the inverse limit, as a set, of the closures of its images. -/
@[stacks 0CUG "closures_sets"]
theorem existsUnique_mem_closure_singleton_of_compatible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt)
    (x : ∀ i, D.obj i)
    (hx : ∀ ⦃i j : I⦄ (f : i ⟶ j), D.map f (x i) = x j)
    (hx_closure : ∀ i, x i ∈ closure ({c.π.app i s} : Set (D.obj i))) :
    ∃! y : c.pt, y ∈ closure ({s} : Set c.pt) ∧ ∀ i, c.π.app i y = x i := by
  let hlim : IsLimit (Scheme.forget.mapCone c) := isLimitOfPreserves Scheme.forget hc
  let t : Cone (D ⋙ Scheme.forget) :=
    { pt := ULift.{u, 0} Unit
      π :=
        { app := fun i => TypeCat.ofHom (fun _ => x i)
          naturality _ _ f := by
            ext
            exact (hx f).symm } }
  let y : c.pt := hlim.lift t (ULift.up ())
  have hycoord (i : I) : c.π.app i y = x i := by
    simpa [y, t] using congrArg
      (fun f : _ ⟶ Scheme.forget.obj (D.obj i) => f (ULift.up ())) (hlim.fac t i)
  have hyclosure : y ∈ closure ({s} : Set c.pt) := by
    refine mem_closure_iff.2 fun U hUopen hyU => ?_
    obtain ⟨_, ⟨i, V, -, rfl⟩, hyW, hWU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen D c hc))
        (show y ∈ ⟨U, hUopen⟩ from hyU)
    have hsiV : c.π.app i s ∈ (V : Set (D.obj i)) := by
      simpa using (mem_closure_iff.mp (hx_closure i)) V V.2
        (show x i ∈ (V : Set (D.obj i)) by simpa [hycoord i] using hyW)
    exact ⟨s, hWU hsiV, Set.mem_singleton _⟩
  refine ⟨y, ⟨hyclosure, hycoord⟩, ?_⟩
  intro y' hy'
  have heq : TypeCat.ofHom (fun _ : ULift.{u, 0} Unit => y') = hlim.lift t :=
    hlim.uniq t _ fun i => by
      ext
      exact hy'.2 i
  simpa [y] using congrArg (fun f : _ ⟶ Scheme.forget.obj c.pt => f (ULift.up ())) heq

/-- The closure of a point, as a closed subset. -/
abbrev pointClosure (X : Scheme.{u}) (x : X) : Closeds X :=
  Closeds.closure ({x} : Set X)

/-- The vanishing ideal sheaf of the closure of a point: the ideal sheaf cutting out the reduced
closure of that point. -/
noncomputable abbrev reducedPointIdeal (X : Scheme.{u}) (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (pointClosure X x)

private lemma image_pointClosure_le (X Y : Scheme.{u}) (f : X ⟶ Y) (x : X) :
    f '' (pointClosure X x : Set X) ≤ pointClosure Y (f x) := by
  simpa [pointClosure] using
    (image_closure_subset_closure_image f.continuous :
      f '' closure ({x} : Set X) ⊆ closure (f '' ({x} : Set X)))

private lemma stageIdeal_le_map {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {i j : I} (f : i ⟶ j) (s : c.pt) :
    reducedPointIdeal (D.obj j) (c.π.app j s) ≤
      (reducedPointIdeal (D.obj i) (c.π.app i s)).map (D.map f) := by
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  exact Scheme.IdealSheafData.vanishingIdeal_antimono <| by
    rw [show c.π.app j s = D.map f (c.π.app i s) by
      rw [← Scheme.Hom.comp_apply, c.w]]
    exact (pointClosure (D.obj j) (D.map f (c.π.app i s))).closure_le.mpr
      (image_pointClosure_le _ _ (D.map f) _)

/-- The supremum of the pullbacks to the limit of the vanishing ideals of the closures of the
images of a point. -/
private noncomputable abbrev pulledPointIdeal {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (s : c.pt) : c.pt.IdealSheafData :=
  ⨆ i, (reducedPointIdeal (D.obj i) (c.π.app i s)).comap (c.π.app i)

private lemma pulledPointIdeal_le_map {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (s : c.pt) (i : I) :
    reducedPointIdeal (D.obj i) (c.π.app i s) ≤
      (pulledPointIdeal D c s).map (c.π.app i) := by
  rw [Scheme.IdealSheafData.le_map_iff_comap_le]
  exact le_iSup_of_le i le_rfl

/-- The diagram of the reduced closures of the images of a point of the limit. -/
private noncomputable abbrev reducedClosureDiagram {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (s : c.pt) : I ⥤ Scheme.{u} where
  obj i := (reducedPointIdeal (D.obj i) (c.π.app i s)).subscheme
  map {i j} f := Scheme.IdealSheafData.subschemeMap
    (reducedPointIdeal (D.obj i) (c.π.app i s))
    (reducedPointIdeal (D.obj j) (c.π.app j s)) (D.map f)
    (stageIdeal_le_map D c f s)
  map_id i := by
    apply (cancel_mono ((reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι)).1
    simp
  map_comp {i j k} f g := by
    apply (cancel_mono ((reducedPointIdeal (D.obj k) (c.π.app k s)).subschemeι)).1
    simp [Functor.map_comp]

/-- The inclusion of the diagram of reduced closures into the original diagram. -/
private noncomputable abbrev reducedClosureInclusion {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (s : c.pt) :
    reducedClosureDiagram D c s ⟶ D where
  app i := (reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι
  naturality i j f := by simp [reducedClosureDiagram]

/-- The candidate limiting cone over the diagram of reduced closures. -/
private noncomputable abbrev reducedClosureCone {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (s : c.pt) :
    Cone (reducedClosureDiagram D c s) where
  pt := (pulledPointIdeal D c s).subscheme
  π :=
    { app i := Scheme.IdealSheafData.subschemeMap
        (pulledPointIdeal D c s)
        (reducedPointIdeal (D.obj i) (c.π.app i s)) (c.π.app i)
        (pulledPointIdeal_le_map D c s i)
      naturality i j f := by
        apply (cancel_mono ((reducedPointIdeal (D.obj j) (c.π.app j s)).subschemeι)).1
        simp [reducedClosureDiagram] }

private lemma point_eq_of_projection_eq {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) {x y : c.pt}
    (h : ∀ i, c.π.app i x = c.π.app i y) : x = y := by
  suffices H : ∀ {x y : c.pt}, (∀ i, c.π.app i x = c.π.app i y) →
      ∀ U, IsOpen U → x ∈ U → y ∈ U from
    (inseparable_iff_forall_isOpen.2 fun U hU =>
      ⟨H h U hU, H (fun i => (h i).symm) U hU⟩).eq
  intro x y h U hU hxU
  obtain ⟨_, ⟨i, V, -, rfl⟩, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen D c hc)
      (show x ∈ (⟨U, hU⟩ : c.pt.Opens) from hxU)
  apply hVU
  change c.π.app i y ∈ V
  rw [← h i]
  exact hxV

private lemma support_pulledPointIdeal {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt) :
    (pulledPointIdeal D c s).support = pointClosure c.pt s := by
  apply SetLike.coe_injective
  rw [pulledPointIdeal, Scheme.IdealSheafData.support_iSup]
  simp_rw [Scheme.IdealSheafData.support_comap]
  ext x
  simp only [reducedPointIdeal]
  change x ∈ (⨅ i, (pointClosure (D.obj i) (c.π.app i s)).preimage
      (c.π.app i).continuous : Closeds c.pt) ↔ x ∈ pointClosure c.pt s
  simp only [Closeds.mem_iInf]
  refine ⟨fun hx => ?_, fun hx i => ?_⟩
  · obtain ⟨y, ⟨hy, hycoord⟩, -⟩ :=
      existsUnique_mem_closure_singleton_of_compatible D c hc s (fun i => c.π.app i x)
        (fun i j f => by rw [← Scheme.Hom.comp_apply, c.w]) hx
    exact (point_eq_of_projection_eq D c hc fun i => by simpa using hycoord i) ▸ hy
  · change c.π.app i x ∈ pointClosure (D.obj i) (c.π.app i s)
    exact (image_pointClosure_le c.pt (D.obj i) (c.π.app i) s) ⟨x, hx, rfl⟩

/-- The lift of a cone over the reduced closures to the limit, composed with a projection. -/
private lemma lift_comp_app_eq_comp_subschemeι {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (s : c.pt)
    (t : Cone (reducedClosureDiagram D c s)) (i : I) :
    hc.lift ((Cone.postcompose (reducedClosureInclusion D c s)).obj t) ≫ c.π.app i =
      t.π.app i ≫ (reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι :=
  hc.fac _ i

private noncomputable def isLimitReducedClosureCone
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c) (s : c.pt) :
    IsLimit (reducedClosureCone D c s) where
  lift t := IsClosedImmersion.lift (pulledPointIdeal D c s).subschemeι
    (hc.lift ((Cone.postcompose (reducedClosureInclusion D c s)).obj t)) (by
      suffices ∀ i, reducedPointIdeal (D.obj i) (c.π.app i s) ≤
          (t.π.app i ≫ (reducedClosureInclusion D c s).app i).ker by
        simpa [pulledPointIdeal, Scheme.IdealSheafData.ker_subschemeι,
          ← Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.Hom.ker_comp]
      intro i
      refine le_trans ?_ (Scheme.Hom.le_ker_comp _ _)
      change reducedPointIdeal (D.obj i) (c.π.app i s) ≤
        (reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι.ker
      rw [Scheme.IdealSheafData.ker_subschemeι])
  fac t i := by
    apply (cancel_mono (reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι).mp
    rw [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      ← Category.assoc, IsClosedImmersion.lift_fac]
    exact lift_comp_app_eq_comp_subschemeι D c hc s t i
  uniq t m hm := by
    apply (cancel_mono (pulledPointIdeal D c s).subschemeι).mp
    rw [IsClosedImmersion.lift_fac]
    apply hc.hom_ext
    intro i
    dsimp only [reducedClosureCone, reducedClosureInclusion] at hm
    calc
      m ≫ (pulledPointIdeal D c s).subschemeι ≫ c.π.app i =
          t.π.app i ≫ (reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι := by
        simpa only [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
          IsClosedImmersion.lift_fac] using
          congrArg (fun f => f ≫ (reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι)
            (hm i)
      _ = _ := (lift_comp_app_eq_comp_subschemeι D c hc s t i).symm

private lemma subscheme_eqToIso_hom_ι {X : Scheme.{u}} {J K : X.IdealSheafData}
    (h : J = K) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ K.subschemeι =
      J.subschemeι := by
  subst K
  simp

/-- **Stacks Project, Tag 0CUG.** The reduced closure of a point of a cofiltered limit of
schemes is the limit, as a scheme, of the reduced closures of its images. -/
@[stacks 0CUG "closures_schemes"]
theorem exists_isLimit_reducedClosures
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt) :
    ∃ (E : I ⥤ Scheme.{u}) (ι : E ⟶ D) (c' : Cone E)
      (e : c'.pt ≅ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({s} : Set c.pt))).subscheme),
      (∀ i, ∃ eᵢ : E.obj i ≅ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({c.π.app i s} : Set (D.obj i)))).subscheme,
        eᵢ.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({c.π.app i s} : Set (D.obj i)))).subschemeι = ι.app i) ∧
      (∀ i, c'.π.app i ≫ ι.app i =
        e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({s} : Set c.pt))).subschemeι ≫ c.π.app i) ∧
      Nonempty (IsLimit c') := by
  let E := reducedClosureDiagram D c s
  let ι := reducedClosureInclusion D c s
  let c' := reducedClosureCone D c s
  have (i : I) : IsClosedImmersion (ι.app i) :=
    inferInstanceAs (IsClosedImmersion (reducedPointIdeal (D.obj i) (c.π.app i s)).subschemeι)
  have {i j : I} (f : i ⟶ j) : IsAffineHom (E.map f) := by
    have : IsAffineHom (E.map f ≫ ι.app j) := by
      rw [ι.naturality]
      infer_instance
    exact IsAffineHom.of_comp (E.map f) (ι.app j)
  have (i : I) : IsReduced (E.obj i) := by
    dsimp only [E, reducedClosureDiagram, reducedPointIdeal]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hc' : IsLimit c' := isLimitReducedClosureCone D c hc s
  have : IsReduced (pulledPointIdeal D c s).subscheme :=
    isReduced_cofilteredLimit_of_isReduced E c' hc'
  have heq : pulledPointIdeal D c s = reducedPointIdeal c.pt s :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _
      (support_pulledPointIdeal D c hc s)
  let e : c'.pt ≅ (reducedPointIdeal c.pt s).subscheme :=
    eqToIso (congrArg Scheme.IdealSheafData.subscheme heq)
  refine ⟨E, ι, c', e, fun _ => ⟨Iso.refl _, Category.id_comp _⟩, fun i => ?_, ⟨hc'⟩⟩
  change _ = e.hom ≫ (reducedPointIdeal c.pt s).subschemeι ≫ c.π.app i
  dsimp only [e]
  rw [← Category.assoc, subscheme_eqToIso_hom_ι heq]
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ (pulledPointIdeal_le_map D c s i)

end AlgebraicGeometry

end
