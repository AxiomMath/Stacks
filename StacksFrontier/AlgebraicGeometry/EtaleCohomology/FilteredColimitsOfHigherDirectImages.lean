module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsAtQcqsObjects
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing

/-!
# Higher direct images along a quasi-compact quasi-separated morphism and filtered colimits

Let `h : Y ⟶ X` be a quasi-compact and quasi-separated morphism of schemes, with `X` and `Y`
arbitrary. For a filtered system `G` of abelian sheaves on the small étale site of `Y`, if
`R^p h_* G_i = 0` for every `i` then `R^p h_* (colim_i G_i) = 0`. This is the vanishing half of
the commutation of higher direct images with filtered colimits, the case of a constant tower in
[Stacks, Tag 09Z1].

The higher direct image is the sheafification of the presheaf `V ↦ H^p(Y ×_X V, -)`
([Stacks, Tag 072W]), so it vanishes as soon as every section of that presheaf dies locally on
`V`. Locally on `V` one may take `V` affine; then `Y ×_X V` is a quasi-compact and
quasi-separated scheme, and cohomology over such an object of the small étale site of `Y`
commutes with filtered colimits ([Stacks, Tag 0739]). So a section over an affine `V` comes from
some `G_i`, where it dies locally because `R^p h_* G_i = 0`.

[Stacks, Tag 0739] is used in the form
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_of_qcqs`, for
objects of the small étale site of `Y` with quasi-compact and quasi-separated underlying scheme;
it needs no finiteness of `Y` itself, which is what allows `X` and `Y` to be arbitrary.

## Main results

* `Stacks.EtaleCohomology.equalizerSieve_mem_of_isZero_presheafToSheaf` — a section of a
  presheaf whose sheafification vanishes dies locally.
* `Stacks.EtaleCohomology.isZero_rightDerived_smallEtalePushforwardAb_colimit` — a filtered
  colimit of sheaves with vanishing `R^p h_*` has vanishing `R^p h_*`, for `h` quasi-compact and
  quasi-separated.

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities etale_respectsIso

variable {X : Scheme.{u}}

/-! ### Higher direct images -/

open Stacks.Cohomology.SheafifiedHigherDirectImage

/-- **A section of a presheaf whose sheafification vanishes dies locally.** The sheafification
map is locally injective, and it carries every section to zero. -/
theorem equalizerSieve_mem_of_isZero_presheafToSheaf {C : Type*} [Category* C]
    (J : GrothendieckTopology C) [HasSheafify J Ab.{u + 1}]
    [J.WEqualsLocallyBijective Ab.{u + 1}] (P : Cᵒᵖ ⥤ Ab.{u + 1})
    (hP : IsZero ((presheafToSheaf J Ab.{u + 1}).obj P)) (U : C) (x : ToType (P.obj (op U))) :
    Presheaf.equalizerSieve (F := P) (X := op U) x 0 ∈ J U := by
  refine Presheaf.equalizerSieve_mem J (toSheafify J P) x 0 ?_
  have h0 : (toSheafify J P).app (op U) = 0 := by
    rw [((sheafToPresheaf J Ab.{u + 1}).map_isZero hP).eq_of_tgt (toSheafify J P) 0]
    rfl
  rw [h0, map_zero]
  rfl

/-- **Local vanishing of a section on the small étale site reduces to affine objects.** If every
section over an affine object of a presheaf on `X.Etale` dies locally, then so does every
section. -/
theorem equalizerSieve_mem_smallEtaleTopology_of_isAffine {F : X.Etaleᵒᵖ ⥤ Ab.{u + 1}}
    (V : X.Etale) (ξ : ToType (F.obj (op V)))
    (H : ∀ (W : X.Etale) [IsAffine W.left] (η : ToType (F.obj (op W))),
      Presheaf.equalizerSieve (X := op W) η 0 ∈ X.smallEtaleTopology W) :
    Presheaf.equalizerSieve (X := op V) ξ 0 ∈ X.smallEtaleTopology V := by
  let C := V.left.affineCover
  let W (k : C.I₀) : X.Etale := .mk (C.f k ≫ V.hom)
  let a (k : C.I₀) : W k ⟶ V := MorphismProperty.Over.homMk (C.f k)
  have ha : Sieve.ofArrows _ a ∈ X.smallEtaleTopology V := by
    refine (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨k, y, hy⟩ := C.exists_eq x
    exact Set.mem_iUnion.mpr ⟨k, y, hy⟩
  refine X.smallEtaleTopology.transitive ha _ ?_
  rintro Z f ⟨T, c, _, ⟨k⟩, rfl⟩
  have : IsAffine (W k).left := inferInstanceAs (IsAffine (C.X k))
  refine X.smallEtaleTopology.superset_covering ?_
    (X.smallEtaleTopology.pullback_stable c (H (W k) (F.map (a k).op ξ)))
  intro Z' g hg
  change F.map (g ≫ c ≫ a k).op ξ = F.map (g ≫ c ≫ a k).op 0
  have hg' : F.map (g ≫ c).op (F.map (a k).op ξ) = F.map (g ≫ c).op 0 := hg
  rw [map_zero] at hg' ⊢
  rwa [← Category.assoc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **Higher direct images of a filtered colimit vanish if they vanish on the members.** Let
`h : Y ⟶ X` be quasi-compact and quasi-separated and let `G` be a filtered system of abelian
sheaves on the small étale site of `Y`. If `R^p h_* G_i = 0` for every `i`, then
`R^p h_* (colim_i G_i) = 0`.

By [Stacks, Tag 072W] it suffices that every class in `H^p(Y ×_X V, colim G)` die locally on
`V`. Locally on `V` one may take `V` affine; then `Y ×_X V` has quasi-compact and
quasi-separated underlying scheme, so the class comes from some `H^p(Y ×_X V, G_i)`
(`isIso_colimit_post_rightDerived_sheafSections_of_qcqs`), where it dies locally
because `R^p h_* G_i = 0`. -/
theorem isZero_rightDerived_smallEtalePushforwardAb_colimit {Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (p : ℕ) {I : Type (u + 1)} [SmallCategory I]
    [IsFiltered I] (G : I ⥤ Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (hG : ∀ i, IsZero (((smallEtalePushforwardAb h).rightDerived p).obj (G.obj i))) :
    IsZero (((smallEtalePushforwardAb h).rightDerived p).obj (colimit G)) := by
  let u := smallEtaleBaseChange h
  let P := (pushforwardCohomologyPresheaf (K := Y.smallEtaleTopology) Ab.{u + 1} u).rightDerived p
  have hloc : ∀ i (V : X.Etale) (ξ : ToType ((P.obj (G.obj i)).obj (op V))),
      Presheaf.equalizerSieve (X := op V) ξ 0 ∈ X.smallEtaleTopology V := fun i V ξ ↦
    equalizerSieve_mem_of_isZero_presheafToSheaf _ _
      ((hG i).of_iso ((rightDerivedPushforwardIso Ab.{u + 1} u p).app (G.obj i)).symm) V ξ
  have hstage : ∀ (V : X.Etale) [IsAffine V.left] (ξ : ToType ((P.obj (colimit G)).obj (op V))),
      ∃ i, ∃ ξ' : ToType ((P.obj (G.obj i)).obj (op V)),
        ((P.map (colimit.ι G i)).app (op V)) ξ' = ξ := by
    intro V _ ξ
    have hW : u.obj V ∈ qcqsEtaleObjects Y :=
      ⟨compactSpace_smallEtaleBaseChange_obj h V inferInstance,
        quasiSeparatedSpace_smallEtaleBaseChange_obj h V inferInstance⟩
    let E := pushforwardCohomologyPresheafEvaluationIso (K := Y.smallEtaleTopology)
      Ab.{u + 1} u p V
    let H := (pushforwardCohomologyPresheaf (K := Y.smallEtaleTopology) Ab.{u + 1} u ⋙
      (evaluation X.Etaleᵒᵖ Ab.{u + 1}).obj (op V)).rightDerived p
    have hpost : IsIso (colimit.post G H) :=
      isIso_colimit_post_rightDerived_sheafSections_of_qcqs.{0} p (u.obj V) hW G
    obtain ⟨z, hz⟩ : ∃ z, (colimit.post G H) z = E.inv.app (colimit G) ξ :=
      ⟨(inv (colimit.post G H)) (E.inv.app (colimit G) ξ), by simp⟩
    obtain ⟨i, z', rfl⟩ := Concrete.colimit_exists_rep (G ⋙ H) z
    refine ⟨i, E.hom.app (G.obj i) z', ?_⟩
    have h1 : (colimit.post G H) ((colimit.ι (G ⋙ H) i) z') = H.map (colimit.ι G i) z' := by
      rw [← ConcreteCategory.comp_apply, colimit.ι_post]
    have h3 : E.hom.app (colimit G) (H.map (colimit.ι G i) z') =
        ((P.map (colimit.ι G i)).app (op V)) (E.hom.app (G.obj i) z') :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans ((congrArg (fun φ ↦ φ z')
        (E.hom.naturality (colimit.ι G i))).trans (ConcreteCategory.comp_apply _ _ _))
    rw [← h3, ← h1, hz]
    simp
  have haffloc : ∀ (V : X.Etale) [IsAffine V.left] (ξ : ToType ((P.obj (colimit G)).obj (op V))),
      Presheaf.equalizerSieve (X := op V) ξ 0 ∈ X.smallEtaleTopology V := by
    intro V _ ξ
    obtain ⟨i, ξ', rfl⟩ := hstage V ξ
    refine X.smallEtaleTopology.superset_covering ?_ (hloc i V ξ')
    intro Z f hf
    change (P.obj (colimit G)).map f.op ((P.map (colimit.ι G i)).app (op V) ξ') =
      (P.obj (colimit G)).map f.op 0
    have hf' : (P.obj (G.obj i)).map f.op ξ' = (P.obj (G.obj i)).map f.op 0 := hf
    rw [map_zero] at hf' ⊢
    rw [← ConcreteCategory.comp_apply, ← (P.map (colimit.ι G i)).naturality,
      ConcreteCategory.comp_apply, hf', map_zero]
  exact isZero_rightDerived_pushforward_of_locallyZero u p (colimit G) fun V ξ ↦
    equalizerSieve_mem_smallEtaleTopology_of_isAffine V ξ haffloc

end Stacks.EtaleCohomology

end
