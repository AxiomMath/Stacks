module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.RepresentedBy
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability

/-!
# Affineness of the representing object of a relative morphism functor

Let `Z ⟶ S` be finite locally free and `X ⟶ S` affine. The functor of `S`-morphisms from `Z` to
`X` is then represented by a scheme *affine over `S`*.

## Main results

* `Stacks.Morphisms.exists_isAffineOpen_fibre_of_isAffineHom`: an affine morphism satisfies the
  fibrewise hypothesis on the target asked by Stacks Tag 0BL4.
* `Stacks.Morphisms.relativeHom_representableBy_affineHom`: for `Z ⟶ S` finite locally free and
  `X ⟶ S` affine, the relative morphism functor is represented by a scheme affine over `S`.

## References

* [Stacks Project, Tag 0BL3](https://stacks.math.columbia.edu/tag/0BL3)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Morphisms

/-- Pushing a product forward along `j` turns the pullback of `Z` into `Z` itself: for `A` an
object of the slice over `U`, the `S`-object `(Z ×_U A)` pushed forward is `Z ×_S (A pushed
forward)`. -/
private noncomputable def prodMapPullbackIso {S U : Scheme.{u}} (j : U ⟶ S) (Z : Over S)
    (A : Over U) :
    (Over.map j).obj ((Over.pullback j).obj Z ⨯ A) ≅ Z ⨯ (Over.map j).obj A := by
  let e := Over.prodLeftIsoPullback ((Over.pullback j).obj Z) A ≪≫
    pullbackLeftPullbackSndIso Z.hom j A.hom ≪≫
    (Over.prodLeftIsoPullback Z ((Over.map j).obj A)).symm
  refine Over.isoMk e ?_
  change e.hom ≫ (Z ⨯ (Over.map j).obj A).hom =
    ((Over.pullback j).obj Z ⨯ A).hom ≫ j
  rw [← Over.w (prod.snd : Z ⨯ (Over.map j).obj A ⟶ _)]
  simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Over.prodLeftIsoPullback_inv_snd_assoc, Over.map_obj_hom]
  rw [pullbackLeftPullbackSndIso_hom_snd_assoc]
  change ((Over.prodLeftIsoPullback ((Over.pullback j).obj Z) A).hom ≫
    pullback.snd ((Over.pullback j).obj Z).hom A.hom) ≫ A.hom ≫ j = _
  rw [Over.prodLeftIsoPullback_hom_snd, Over.w_assoc]

private lemma prodMapPullbackIso_hom_fst {S U : Scheme.{u}} (j : U ⟶ S) (Z : Over S)
    (A : Over U) :
    (prodMapPullbackIso j Z A).hom ≫ prod.fst =
      (Over.map j).map prod.fst ≫ (Over.mapPullbackAdj j).counit.app Z := by
  ext
  simp only [prodMapPullbackIso, Over.map_obj_left, Over.comp_left, Functor.id_obj,
    Over.mapPullbackAdj_counit_app, Over.pullback_obj_left, Over.map_map_left, Over.homMk_left,
    Over.isoMk_hom_left, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Over.prodLeftIsoPullback_inv_fst, Over.map_obj_hom]
  rw [pullbackLeftPullbackSndIso_hom_fst]
  exact Over.prodLeftIsoPullback_hom_fst_assoc ((Over.pullback j).obj Z) A _

private lemma prodMapPullbackIso_hom_snd {S U : Scheme.{u}} (j : U ⟶ S) (Z : Over S)
    (A : Over U) :
    (prodMapPullbackIso j Z A).hom ≫ prod.snd = (Over.map j).map prod.snd := by
  ext
  simp only [prodMapPullbackIso, Over.map_obj_left, Over.comp_left, Over.map_map_left,
    Over.isoMk_hom_left, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Over.prodLeftIsoPullback_inv_snd, Over.map_obj_hom]
  rw [pullbackLeftPullbackSndIso_hom_snd]
  exact Over.prodLeftIsoPullback_hom_snd ((Over.pullback j).obj Z) A

/-- `Stacks.Morphisms.prodMapPullbackIso` as an isomorphism of functors. -/
private noncomputable def prodMapPullbackNatIso {S U : Scheme.{u}} (j : U ⟶ S) (Z : Over S) :
    prod.functor.obj ((Over.pullback j).obj Z) ⋙ Over.map j ≅
      Over.map j ⋙ prod.functor.obj Z :=
  NatIso.ofComponents (prodMapPullbackIso j Z) (by
    intro A B a
    -- The two component equations are stated separately so that they are elaborated with the
    -- canonical instances of the slice category, which is what lets the rewrites below fire.
    have h₁ : ((Over.map j).map (prod.map (𝟙 ((Over.pullback j).obj Z)) a) ≫
          (prodMapPullbackIso j Z B).hom) ≫ prod.fst =
        ((prodMapPullbackIso j Z A).hom ≫
          prod.map (𝟙 Z) ((Over.map j).map a)) ≫ prod.fst := by
      rw [Category.assoc, Category.assoc, prodMapPullbackIso_hom_fst, prod.map_fst,
        Category.comp_id, ← Functor.map_comp_assoc, prod.map_fst, Category.comp_id,
        prodMapPullbackIso_hom_fst]
    have h₂ : ((Over.map j).map (prod.map (𝟙 ((Over.pullback j).obj Z)) a) ≫
          (prodMapPullbackIso j Z B).hom) ≫ prod.snd =
        ((prodMapPullbackIso j Z A).hom ≫
          prod.map (𝟙 Z) ((Over.map j).map a)) ≫ prod.snd := by
      rw [Category.assoc, Category.assoc, prodMapPullbackIso_hom_snd, prod.map_snd,
        ← Category.assoc, prodMapPullbackIso_hom_snd, ← Functor.map_comp, ← Functor.map_comp,
        prod.map_snd]
    exact prod.hom_ext h₁ h₂)

/-- **The relative morphism functor base changes.** Restricting the relative morphism functor of
`Z` and `X` over `S` to the slice over `U` is the relative morphism functor of the pullbacks of
`Z` and `X` to `U`. -/
private noncomputable def relativeHomBaseChangeIso {S U : Scheme.{u}} (j : U ⟶ S)
    (Z X : Over S) :
    (Over.map j).op ⋙ ((prod.functor.obj Z).op ⋙ yoneda.obj X) ≅
      (prod.functor.obj ((Over.pullback j).obj Z)).op ⋙
        yoneda.obj ((Over.pullback j).obj X) :=
  Functor.isoWhiskerRight (NatIso.op (prodMapPullbackNatIso j Z)) (yoneda.obj X) ≪≫
    Functor.isoWhiskerLeft (prod.functor.obj ((Over.pullback j).obj Z)).op
      ((Over.mapPullbackAdj j).compYonedaIso.app X).symm

/-- A representing object of a presheaf on the slice over `S` pulls back to a representing object
of its restriction to the slice over `U`, by the adjunction `Over.map j ⊣ Over.pullback j`. -/
private noncomputable def representableByPullback {S U : Scheme.{u}} (j : U ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type u} {W : Over S} (e : F.RepresentableBy W) :
    ((Over.map j).op ⋙ F).RepresentableBy ((Over.pullback j).obj W) :=
  ((Over.mapPullbackAdj j).representableBy W).ofIso
    (Functor.isoWhiskerLeft (Over.map j).op e.toIso)

/-- **The fibrewise hypothesis of Stacks 0BL4 holds for an affine morphism.** A finite set of
points of `X` lying in one fibre of an affine `g : X ⟶ S` lies in the preimage of any affine open
of `S` containing the image point, and that preimage is affine. -/
theorem exists_isAffineOpen_fibre_of_isAffineHom {S X : Scheme.{u}} (g : X ⟶ S) [IsAffineHom g]
    (s : S) (t : Set X) (_ht : t.Finite) (hts : ∀ x ∈ t, g.base x = s) :
    ∃ U : X.Opens, IsAffineOpen U ∧ t ⊆ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  refine ⟨g ⁻¹ᵁ V, IsAffineHom.isAffine_preimage (f := g) V hV, fun x hx => ?_⟩
  change g.base x ∈ V
  exact (hts x hx).symm ▸ hsV

/-- If `Z ⟶ S` is finite locally free and `X ⟶ S` is affine, then the relative morphism functor
`Mor_S(Z, X)` is represented by a scheme affine over `S`. -/
@[stacks 0BL3]
theorem relativeHom_representableBy_affineHom {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f] [IsAffineHom g] :
    ∃ W : Over S, IsAffineHom W.hom ∧
      Nonempty
        (((prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)).RepresentableBy W) := by
  set F := (prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)
  have _i : F.IsRepresentable :=
    homFromFiniteLocallyFree_isRepresentable f g (exists_isAffineOpen_fibre_of_isAffineHom g)
  refine ⟨F.reprX, ?_, ⟨F.representableBy⟩⟩
  choose U hU hmem hff using fun s : S => exists_isAffineOpen_module_finite_and_free f s
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun s => ⟨U s, hmem s, hU s, ?_⟩
  have _ : IsAffine (U s).toScheme := hU s
  obtain ⟨W', hW', ⟨r⟩⟩ := AlgebraicGeometry.relativeHom_representableBy_affine
    (U s).toScheme (pullback (U s).ι f) (pullback (U s).ι g)
    (pullback.fst (U s).ι f) (pullback.fst (U s).ι g) (hff s).1 (hff s).2
  have _ : IsAffine W'.left := hW'
  have e₂ := (representableByPullback (U s).ι F.representableBy).ofIso
    (relativeHomBaseChangeIso (U s).ι (Over.mk f) (Over.mk g))
  let e : ∀ {T : Scheme.{u}} (h : T ⟶ S), Over.mk (pullback.fst (U s).ι h) ≅
      (Over.pullback (U s).ι).obj (Over.mk h) := fun h =>
    Over.isoMk (pullbackSymmetry (U s).ι h) (by simp)
  have r' := r.ofIso
    (Functor.isoWhiskerRight (NatIso.op (prod.functor.mapIso (e f)).symm)
        (yoneda.obj (Over.mk (pullback.fst (U s).ι g))) ≪≫
      Functor.isoWhiskerLeft (prod.functor.obj ((Over.pullback (U s).ι).obj (Over.mk f))).op
        (yoneda.mapIso (e g)))
  have _aff : IsAffine (pullback F.reprX.hom (U s).ι) :=
    IsAffine.of_isIso (Y := W'.left)
      ((Over.forget ((U s).toScheme)).mapIso (e₂.uniqueUpToIso r')).hom
  exact IsAffine.of_isIso (pullbackRestrictIsoRestrict F.reprX.hom (U s)).inv

end Stacks.Morphisms
