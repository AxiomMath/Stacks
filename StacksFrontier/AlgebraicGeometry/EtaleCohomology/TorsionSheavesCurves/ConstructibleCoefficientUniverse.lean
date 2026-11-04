module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CoefficientUniverseReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLocallyConstantUlift

/-!
# Constructible sheaves at every coefficient universe are universe lifts

An abelian sheaf `F` on Mathlib's small étale site of `X` at the coefficients
`AddCommGrpCat.{max (u + 1) v}` which is constructible (read on a big étale site `B` containing
`X`) is the universe lift of a sheaf at the coefficients `AddCommGrpCat.{u + 1}`, and that sheaf
is constructible on every big étale site.

* The groups of sections of `F` are `(u + 1)`-small. The strata `p : T ⟶ X` of the
  stratifications of the affine opens of `X` jointly cover `X`, so the family of inverse images
  `p⁻¹` reflects isomorphisms; hence `F` embeds into the product of the `p_* p⁻¹ F`, since the
  kernel of that map is killed by every `p⁻¹` (the image under `p⁻¹` of the unit
  `F ⟶ p_* p⁻¹ F` is split by the counit). Each `p⁻¹ F` is finite locally constant on the site of
  Tag 021B, so has small sections there, and so on Mathlib's site, of which that site is a dense
  subsite.
* A sheaf with small sections is a universe lift
  (`Stacks.Cohomology.CoefficientLift.exists_sheafCompose_iso_of_small`); inverse image commutes
  with the lift, and finite local constancy reflects along it, so the sheaf one universe down is
  constructible on `B`, hence on every big étale site.

## Main results

* `Stacks.EtaleCohomology.mono_piLift_unit_etaleAbelianInverseImage`: a jointly surjective
  family of morphisms embeds a sheaf into the product of its pushed-forward inverse images.
* `Stacks.EtaleCohomology.small_of_isConstructibleEtaleAbelianSheaf`: a constructible sheaf at
  the coefficients `AddCommGrpCat.{max (u + 1) v}` has `(u + 1)`-small sections.
* `Stacks.EtaleCohomology.exists_etaleUlift_iso_isConstructibleOnEveryBigSite`: such a sheaf is
  the universe lift of a sheaf at `AddCommGrpCat.{u + 1}` constructible on every big étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.ConstantSheaf

universe v u

namespace Stacks.EtaleCohomology

/-- **A jointly surjective family of morphisms embeds a sheaf into the product of its
pushed-forward inverse images.** For morphisms `g a : T a ⟶ X` whose images cover `X`, the map
from an abelian sheaf `F` to `∏ₐ (g a)_* (g a)⁻¹ F` given by the units is a monomorphism: its
kernel `K` has `(g a)⁻¹ K = 0` for every `a`, because the inverse image of the unit is split by the
counit, and the inverse images jointly reflect isomorphisms. -/
theorem mono_piLift_unit_etaleAbelianInverseImage {X : Scheme.{u}} {ι : Type u}
    {T : ι → Scheme.{u}} (g : ∀ a, T a ⟶ X) (hg : ⋃ a, Set.range (g a).base = Set.univ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Mono (Pi.lift fun a ↦ (etaleAbelianInverseImageDirectImageAdj.{u, v} (g a)).unit.app F) := by
  set φ := Pi.lift fun a ↦ (etaleAbelianInverseImageDirectImageAdj.{u, v} (g a)).unit.app F
    with hφ
  have hK : ∀ a, IsZero ((etaleAbelianInverseImage.{u, v} (g a)).obj (kernel φ)) := by
    intro a
    let adj := etaleAbelianInverseImageDirectImageAdj.{u, v} (g a)
    let L := etaleAbelianInverseImage.{u, v} (g a)
    have h1 : kernel.ι φ ≫ adj.unit.app F = 0 := by
      have h : kernel.ι φ ≫ φ ≫ Pi.π _ a = 0 := by
        rw [← Category.assoc, kernel.condition, zero_comp]
      simpa [hφ] using h
    have h0 : L.map (kernel.ι φ) = 0 := by
      calc L.map (kernel.ι φ)
          = L.map (kernel.ι φ) ≫ L.map (adj.unit.app F) ≫ adj.counit.app (L.obj F) := by
            rw [adj.left_triangle_components F]
            exact (Category.comp_id _).symm
        _ = 0 := by rw [← Category.assoc, ← L.map_comp, h1, L.map_zero, zero_comp]
    have hm : Mono (L.map (kernel.ι φ)) := inferInstance
    rw [h0] at hm
    exact IsZero.of_mono_zero _ (L.obj F)
  have hiso : IsIso (0 : kernel φ ⟶ kernel φ) :=
    isIso_of_isIso_etaleAbelianInverseImage_family.{u, v} g hg _ fun a ↦ by
      rw [Functor.map_zero, (hK a).eq_of_src 0 (𝟙 _)]
      infer_instance
  refine Preadditive.mono_of_isZero_kernel _ ?_
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : kernel φ ⟶ kernel φ), zero_comp]

/-- The sections of a product of abelian sheaves on the small étale site, indexed by a `u`-small
type, are small when those of the factors are. -/
theorem small_piObj_obj_obj {X : Scheme.{u}} {ι : Type u}
    (G : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (V : X.Etaleᵒᵖ)
    (h : ∀ a, Small.{u + 1} ((G a).obj.obj V)) : Small.{u + 1} ((∏ᶜ G).obj.obj V) := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
    (evaluation _ _).obj V
  let e := PreservesProduct.iso E G
  refine (small_congr (e.addCommGroupIsoToAddEquiv.toEquiv.trans
    (Concrete.productEquiv _))).2 ?_
  have : ∀ a, Small.{u + 1} (ToType (E.obj (G a))) := h
  infer_instance

/-- **Smallness of sections read on the site of Tag 021B.** A sheaf on Mathlib's small étale site
whose restriction to the size-bounded small étale site has small sections has small sections:
the latter site is a dense subsite. -/
theorem small_of_small_sheafEquiv_inverse (B : BigEtaleSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ W : SmallEtale B S hS, Small.{u + 1}
      (((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).inverse.obj F).obj.obj
        (op W)))
    (V : S.Etale) : Small.{u + 1} (F.obj.obj (op V)) := by
  have : (SmallEtale.toEtaleSite B S hS).IsCoverDense S.smallEtaleTopology :=
    Functor.IsDenseSubsite.isCoverDense (SmallEtale.topology B S hS) S.smallEtaleTopology _
  exact small_of_isCoverDense (SmallEtale.toEtaleSite B S hS) S.smallEtaleTopology F h V

/-- The universe-lift functor on abelian groups preserves sheafification on the topology of every
small étale site over an object of a big étale site. -/
private theorem preservesSheafification_over_uliftFunctor (B : BigEtaleSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (V' : SmallEtale B S hS) :
    ((SmallEtale.topology B S hS).over V').PreservesSheafification
      AddCommGrpCat.uliftFunctor.{v, u + 1} :=
  preservesSheafification_uliftFunctor_of_max.{v} _

section Constructible

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **A constructible sheaf has small sections.** An abelian sheaf at the coefficients
`AddCommGrpCat.{max (u + 1) v}` which is constructible on a big étale site has `(u + 1)`-small
groups of sections: it embeds into the product of the `p_* p⁻¹ F` over the strata `p` of the
stratifications of the affine opens, and each `p⁻¹ F` is finite locally constant. -/
theorem small_of_isConstructibleEtaleAbelianSheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F) (V : X.Etale) :
    Small.{u + 1} (F.obj.obj (op V)) := by
  choose s hs using hF
  let ι := Σ U : X.affineOpens, Fin (s U).n
  let T : ι → Scheme.{u} := fun a ↦ ((s a.1).piece a.2).obj
  let g : ∀ a, T a ⟶ X := fun a ↦ B.inclusion.map ((s a.1).inclusion a.2)
  have hg : ⋃ a, Set.range (g a).base = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
      X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
    have hx : x ∈ ⋃ i, Set.range (B.inclusion.map ((s ⟨U, hU⟩).inclusion i)).base := by
      rw [← (s ⟨U, hU⟩).covers]
      exact hxU
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨⟨⟨U, hU⟩, i⟩, hi⟩
  have hsmall : ∀ a (W : (T a).Etale),
      Small.{u + 1} (((etaleAbelianInverseImage.{u, v} (g a)).obj F).obj.obj (op W)) := by
    intro a W
    have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B ((s a.1).inclusion a.2)
    have := preservesSheafification_over_uliftFunctor.{v} B ((s a.1).piece a.2).property
    let e := (SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{max (u + 1) v}
      ((s a.1).inclusion a.2) (etaleAbelianInverseImageDirectImageAdj.{u, v} (g a))
      (Functor.sheafAdjunctionContinuous _ _ _ _)).app F
    refine small_of_small_sheafEquiv_inverse B ((s a.1).piece a.2).property _ (fun W' ↦ ?_) W
    exact small_obj_of_iso e.symm _
      (small_of_isFiniteLocallyConstant.{u + 1, v} _ _ (hs a.1 a.2) W')
  have hφ := mono_piLift_unit_etaleAbelianInverseImage g hg F
  refine Stacks.Cohomology.CoefficientLift.small_of_mono.{u + 1, v} X.smallEtaleTopology
    (Pi.lift fun a ↦ (etaleAbelianInverseImageDirectImageAdj.{u, v} (g a)).unit.app F)
    (fun W ↦ ?_) (op V)
  exact small_piObj_obj_obj _ W fun a ↦ hsmall a _

/-- **A constructible sheaf at every coefficient universe is the universe lift of a sheaf
constructible on every big étale site.** An abelian sheaf at the coefficients
`AddCommGrpCat.{max (u + 1) v}` constructible on a big étale site `B` containing `X` is
isomorphic to the universe lift of a sheaf at the coefficients `AddCommGrpCat.{u + 1}` which is
constructible on every big étale site. -/
theorem exists_etaleUlift_iso_isConstructibleOnEveryBigSite
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F) :
    ∃ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Nonempty ((etaleUlift.{v} X).obj G ≅ F) ∧ IsConstructibleOnEveryBigSite G := by
  obtain ⟨G, ⟨e⟩⟩ := Stacks.Cohomology.CoefficientLift.exists_sheafCompose_iso_of_small.{u + 1, v}
    X.smallEtaleTopology F
    (fun U ↦ small_of_isConstructibleEtaleAbelianSheaf B hX F hF U.unop)
  refine ⟨G, ⟨e⟩, IsConstructibleOnEveryBigSite.of_contains hX ?_⟩
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i ↦ ?_⟩
  let P := s.piece i
  let g := B.inclusion.map (s.inclusion i)
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B (s.inclusion i)
  have := preservesSheafification_over_uliftFunctor.{v} B P.property
  let e₁ := (SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{u + 1} (s.inclusion i)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
    (Functor.sheafAdjunctionContinuous _ _ _ _)).app G
  let e₂ := (SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{max (u + 1) v}
    (s.inclusion i) (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (Functor.sheafAdjunctionContinuous _ _ _ _)).app F
  let ρ := (SmallEtale.sheafEquiv B P.obj P.property AddCommGrpCat.{max (u + 1) v}).inverse
  let e₃ : (sheafCompose (SmallEtale.topology B P.obj P.property)
        AddCommGrpCat.uliftFunctor.{v, u + 1}).obj
        ((SmallEtale.sheafEquiv B P.obj P.property AddCommGrpCat.{u + 1}).inverse.obj
          ((etaleAbelianInverseImage.{u, 0} g).obj G)) ≅
      ρ.obj ((etaleAbelianInverseImage.{u, v} g).obj F) :=
    ρ.mapIso (((etaleAbelianInverseImageUliftIso.{v} g).app G).symm ≪≫
      (etaleAbelianInverseImage.{u, v} g).mapIso e)
  have h₂ := isFiniteLocallyConstant_congr _ e₂ (hF := hs i)
  have h₃ := isFiniteLocallyConstant_congr _ e₃.symm (hF := h₂)
  exact isFiniteLocallyConstant_congr _ e₁.symm
    (hF := isFiniteLocallyConstant_of_sheafCompose_uliftFunctor.{u + 1, v} _ _ h₃)

end Constructible

end Stacks.EtaleCohomology
