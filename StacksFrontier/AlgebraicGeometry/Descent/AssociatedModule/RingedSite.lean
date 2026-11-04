module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness

/-!
# The small Zariski site of a scheme inside its big fppf site

An open `U` of a scheme `S` is a scheme over `S` by its open immersion, and an inclusion of
opens is a morphism of schemes over `S`. This makes the small Zariski site of `S` — the
category of opens of the underlying space of `S` — a subcategory of the big fppf category of
schemes over `S`, and the inclusion is a continuous functor of sites. It is therefore a
morphism of sites in the direction `(Sch/S)_fppf → S_Zar`, whose direct image is restriction
along the inclusion.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.opensObj` and `AlgebraicGeometry.BigFppfOver.opensHom`: an open
  of `S`, and an inclusion of opens, as an object and a morphism of the big fppf category over
  `S`.
* `AlgebraicGeometry.BigFppfOver.opensToBig`: the resulting functor from the small Zariski site
  of `S` to the big fppf category over `S`.
* `AlgebraicGeometry.BigFppfOver.opensHypercover`: the covering family of the big fppf category
  cut out by a covering sieve of the small Zariski site.

## Main results

* `AlgebraicGeometry.BigFppfOver.representablyFlat_opensToBig`: the functor is representably
  flat.
* `AlgebraicGeometry.BigFppfOver.coverPreserving_opensToBig`: the functor is cover preserving
  from the small Zariski topology of `S` to the localized fppf topology of the big site.
* `AlgebraicGeometry.BigFppfOver.isContinuous_opensToBig`: the functor is continuous.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.BigFppfOver

/-- An open subscheme of a scheme contained in a big fppf site is contained in it. -/
public theorem contains_opens (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    (U : S.Opens) : B.Contains (U : Scheme.{u}) :=
  Scheme.size_lt_of_isOpenImmersion U.ι hS

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open of `S` as an object of the big fppf category over `S`, via its open immersion. -/
@[implicit_reducible]
public def opensObj (U : S.Opens) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj (contains_opens B hS U)) U.ι)

/-- The structure morphism of `AlgebraicGeometry.BigFppfOver.opensObj B S hS U` is the open
immersion of `U`. -/
@[simp]
public theorem opensObj_hom_hom (U : S.Opens) :
    (opensObj B S hS U).hom.hom = U.ι := rfl

/-- The inclusion of one open of `S` into a larger one, as a morphism of the big fppf category
over `S`. -/
@[implicit_reducible]
public noncomputable def opensHom {U V : S.Opens} (h : U ≤ V) :
    opensObj B S hS U ⟶ opensObj B S hS V :=
  Over.homMk (ObjectProperty.homMk (X := B.obj (contains_opens B hS U))
    (Y := B.obj (contains_opens B hS V)) (S.homOfLE h))
    (ObjectProperty.hom_ext _ (S.homOfLE_ι h))

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigFppfOver.opensHom B S hS h` is
the inclusion of opens. -/
@[simp]
public theorem opensHom_left_hom {U V : S.Opens} (h : U ≤ V) :
    (opensHom B S hS h).left.hom = S.homOfLE h := rfl

/-- The small Zariski site of `S` inside the big fppf category of schemes over `S`. -/
public noncomputable def opensToBig : S.Opens ⥤ BigFppfOver B S hS where
  obj U := opensObj B S hS U
  map {_ _} h := opensHom B S hS (leOfHom h)
  map_id U := by
    apply Over.OverMorphism.ext; apply ObjectProperty.hom_ext
    rw [opensHom_left_hom, Over.id_left, ObjectProperty.FullSubcategory.id_hom,
      Scheme.homOfLE_rfl]
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext; apply ObjectProperty.hom_ext
    rw [opensHom_left_hom, Over.comp_left, ObjectProperty.FullSubcategory.comp_hom,
      opensHom_left_hom, opensHom_left_hom, Scheme.homOfLE_homOfLE]

/-- `AlgebraicGeometry.BigFppfOver.opensToBig` sends an open `U` to
`AlgebraicGeometry.BigFppfOver.opensObj B S hS U`. -/
@[simp]
public theorem opensToBig_obj (U : S.Opens) :
    (opensToBig B S hS).obj U = opensObj B S hS U := rfl

/-- `AlgebraicGeometry.BigFppfOver.opensToBig` sends an inclusion of opens to
`AlgebraicGeometry.BigFppfOver.opensHom`. -/
@[simp]
public theorem opensToBig_map {U V : S.Opens} (h : U ⟶ V) :
    (opensToBig B S hS).map h = opensHom B S hS (leOfHom h) := rfl

/-- The structure morphism of an object of the big fppf category over `S` factors through the
open immersion of `U` whenever the object has a morphism to `U`. -/
public theorem hom_hom_eq {Z : BigFppfOver B S hS} {U : S.Opens}
    (f : Z ⟶ opensObj B S hS U) : Z.hom.hom = f.left.hom ≫ U.ι := by
  rw [← opensObj_hom_hom B S hS U, ← ObjectProperty.FullSubcategory.comp_hom]
  exact congrArg (fun k : Z.left ⟶ B.obj hS ↦ k.hom) (Over.w f).symm

/-- The range of the structure morphism of an object of the big fppf category over `S` lies in
an open `U` as soon as the object has a morphism to `U`. -/
public theorem range_le_of_hom {Z : BigFppfOver B S hS} {U : S.Opens}
    (f : Z ⟶ opensObj B S hS U) : Set.range ⇑Z.hom.hom ⊆ (U : Set S) := by
  rw [← Scheme.Opens.range_ι U]
  rintro x ⟨y, rfl⟩
  exact ⟨f.left.hom y, by rw [hom_hom_eq B S hS f]; simp⟩

/-- An object of the big fppf category over `S` whose structure morphism has range inside an
open `U` factors through `U`. -/
public noncomputable def homOfRangeLe {Z : BigFppfOver B S hS} (U : S.Opens)
    (h : Set.range ⇑Z.hom.hom ⊆ (U : Set S)) : Z ⟶ opensObj B S hS U :=
  Over.homMk (ObjectProperty.homMk
      (IsOpenImmersion.lift U.ι Z.hom.hom (by rwa [Scheme.Opens.range_ι])))
    (ObjectProperty.hom_ext _ (IsOpenImmersion.lift_fac U.ι Z.hom.hom _))

/-- There is at most one morphism from an object of the big fppf category over `S` to an open
of `S`. -/
public theorem subsingleton_hom_opensObj (Z : BigFppfOver B S hS) (U : S.Opens) :
    Subsingleton (Z ⟶ opensObj B S hS U) :=
  ⟨fun f g ↦ Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <| by
    rw [← cancel_mono U.ι, ← hom_hom_eq B S hS f, ← hom_hom_eq B S hS g]⟩

/-- There is at most one morphism from an object of the big fppf category over `S` into the
image of an open of `S`. -/
public instance subsingleton_hom_opensToBig (Z : BigFppfOver B S hS) (U : S.Opens) :
    Subsingleton (Z ⟶ (opensToBig B S hS).obj U) :=
  subsingleton_hom_opensObj B S hS Z U

/-- The small Zariski site of `S` is representably flat in the big fppf category over `S`. -/
public instance representablyFlat_opensToBig : RepresentablyFlat (opensToBig B S hS) := by
  refine ⟨fun Z ↦
    { cone_objs := fun A C ↦ ?_
      cone_maps := fun A C f g ↦ ⟨A, 𝟙 _, ?_⟩
      nonempty := ⟨StructuredArrow.mk (Y := ⊤) (homOfRangeLe B S hS ⊤ (by simp))⟩ }⟩
  · exact ⟨StructuredArrow.mk (Y := A.right ⊓ C.right) (homOfRangeLe B S hS _
      (Set.subset_inter (range_le_of_hom B S hS A.hom) (range_le_of_hom B S hS C.hom))),
      StructuredArrow.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _),
      StructuredArrow.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _), trivial⟩
  · simpa using StructuredArrow.hom_ext f g (Subsingleton.elim _ _)

/-- The covering family of the big fppf category over `S` cut out by a covering sieve of the
small Zariski site of `S`: the open immersions of the members of the sieve. -/
public noncomputable def opensHypercover {U : S.Opens} (R : Sieve U) :
    PreZeroHypercover.{u + 1} ((opensObj B S hS U).left) where
  I₀ := ULift.{u + 1} (Σ V : S.Opens, { h : V ⟶ U // R.arrows h })
  X i := (opensObj B S hS i.down.1).left
  f i := ((opensToBig B S hS).map i.down.2.1).left

/-- The members of `AlgebraicGeometry.BigFppfOver.opensHypercover B S hS R` are the inclusions of
opens. -/
@[simp]
public theorem opensHypercover_f_hom {U : S.Opens} (R : Sieve U)
    (i : (opensHypercover B S hS R).I₀) :
    ((opensHypercover B S hS R).f i).hom = S.homOfLE (leOfHom i.down.2.1) := rfl

/-- A covering sieve of the small Zariski site of `S` cuts out an fppf covering family of the
chosen category of schemes. -/
public theorem isFppfCovering_opensHypercover {U : S.Opens} (R : Sieve U)
    (hR : R ∈ Opens.grothendieckTopology ↥S U) :
    IsFppfCovering (κ := B.cutoff) ⟨_, opensHypercover B S hS R⟩ := by
  show Presieve.map B.inclusion (opensHypercover B S hS R).presieve₀ ∈
    Scheme.fppfPrecoverage.coverings _
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
  refine Scheme.zariskiPrecoverage_le_fppfPrecoverage _ ?_
  rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ inferInstanceAs (IsOpenImmersion (S.homOfLE (leOfHom i.down.2.1)))⟩
  obtain ⟨V, g, hg, hV⟩ := hR x.1 x.2
  refine ⟨⟨⟨V, g, hg⟩⟩, ⟨⟨x.1, hV⟩, ?_⟩⟩
  show B.inclusion.map (((opensToBig B S hS).map g).left) _ = x
  rw [ObjectProperty.ι_map, opensToBig_map, opensHom_left_hom]
  exact (Scheme.homOfLE_apply' (leOfHom g) x.1 hV).trans (Subtype.ext rfl)

/-- The small Zariski site of `S` is cover preserving in the big fppf category over `S`. -/
public theorem coverPreserving_opensToBig :
    CoverPreserving (Opens.grothendieckTopology ↥S) (topology B S hS) (opensToBig B S hS) := by
  refine ⟨fun {U R} hR ↦ ?_⟩
  rw [GrothendieckTopology.mem_over_iff]
  obtain ⟨⟨W, F⟩, hE', hobj, hce⟩ := B.fppf_has_representative ⟨_, opensHypercover B S hS R⟩
    (isFppfCovering_opensHypercover B S hS R hR)
  cases hobj
  dsimp only at hce
  have hgen : Sieve.generate F.presieve₀ ∈ B.topology _ :=
    Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE'⟩
  rw [← PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hce] at hgen
  refine B.topology.superset_covering ((Sieve.generate_le_iff _ _).2 ?_) hgen
  rintro Y g ⟨i⟩
  refine (Sieve.overEquiv_iff _ _).2 ⟨i.down.1, i.down.2.1, Over.homMk (𝟙 _) ?_, i.down.2.2, ?_⟩
  · exact (Category.id_comp _).trans
      (ObjectProperty.hom_ext _ (S.homOfLE_ι (leOfHom i.down.2.1)).symm)
  · exact Over.OverMorphism.ext (Category.id_comp _).symm

/-- The small Zariski site of `S` is continuous in the big fppf category over `S`. -/
public instance isContinuous_opensToBig : (opensToBig B S hS).IsContinuous
    (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  CategoryTheory.Functor.isContinuous_iff_coverPreserving.2 (coverPreserving_opensToBig B S hS)

end AlgebraicGeometry.BigFppfOver

end
