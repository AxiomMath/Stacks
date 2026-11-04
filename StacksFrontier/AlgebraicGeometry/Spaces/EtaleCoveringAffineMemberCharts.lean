module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# Affine charts of the members of an étale covering refining an affine chart

Let `{f i : Y i ⟶ X}` be a family of étale morphisms of algebraic spaces which is jointly
surjective on points, and `T` an étale chart of `X` with affine underlying scheme. Then `T` is
covered, in the small étale topology, by finitely many charts of the form `f_b(E)` with `E` an
affine étale chart of a member `Y b`. This is the finiteness input of the glueing step of the
induction [Stacks, Tag 08GP] for the module form of [Stacks, Tag 0829]: a section of a module over
`T` lies in a sheaf submodule as soon as its restrictions to finitely many affine charts of the
members do.

## Main results

* `AlgebraicGeometry.Space.exists_finite_affine_member_charts_covering`: the covering.
* `AlgebraicGeometry.Space.mem_of_forall_mem_etaleSubmoduleRestrict`: a section over a chart lies
  in a submodule `G` when its restrictions to a covering by charts of the members lie in the
  restrictions of `G`.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
  {I : Type v} (Yi : I → AlgebraicSpaces B S hS) (f : ∀ i, Yi i ⟶ X)

/-- **An affine étale chart of `X` is covered by finitely many affine charts of the members of a
jointly surjective étale family.** There are finitely many affine étale charts `E k` of members
`Y (b k)` and morphisms `g k : f_{b k}(E k) ⟶ T` generating a covering sieve of `T`. The charts
of the members refining `T` (`AlgebraicGeometry.Space.exists_refinement_of_jointlySurjective`)
are refined by finitely many affine charts of `X`
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`), each of which is read as a
chart of a member through its factorization. -/
theorem exists_finite_affine_member_charts_covering (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Yi i).1,
      pointsMap B S hS (Yi i).1 (f i).hom y = x)
    (T : SmallEtale B S hS X.1)
    (hT : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj T)) :
    ∃ (κ : Type) (_ : Finite κ) (b : κ → I) (E : ∀ k, SmallEtale B S hS (Yi (b k)).1)
      (g : ∀ k, (smallEtalePostcomp B S hS (f (b k)) (hf (b k))).obj (E k) ⟶ T),
      (∀ k, IsAffine ((SmallEtale.toOver B S hS (Yi (b k)).1 ⋙
        BigFppfOver.toScheme B S hS).obj (E k))) ∧
      Sieve.ofArrows (fun k => (smallEtalePostcomp B S hS (f (b k)) (hf (b k))).obj (E k)) g ∈
        SmallEtale.topology B S hS X.1 T := by
  obtain ⟨V, q, hcov⟩ := exists_refinement_of_jointlySurjective B S hS Yi f hf hsurj T
  obtain ⟨κ, hκ, A, r, hA, hle, hAcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS X.1 T hT _ hcov
  have hfac : ∀ k, ∃ (i : I) (h : A k ⟶ (smallEtalePostcomp B S hS (f i) (hf i)).obj (V i)),
      r k = h ≫ q i := fun k => by
    obtain ⟨i, h, e⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 (hle _ (Sieve.ofArrows_mk _ _ k))
    exact ⟨i, h, e⟩
  choose b h hh using hfac
  let E : ∀ k, SmallEtale B S hS (Yi (b k)).1 := fun k =>
    ⟨CostructuredArrow.mk (yoneda.map (h k).hom.left ≫ (V (b k)).1.hom),
      etale_comp_of_scheme B S hS _ _ (etale_toScheme_toOver_map B S hS X.1 (h k))
        (V (b k)).property⟩
  have hw : ∀ k, yoneda.map (h k).hom.left ≫ (V (b k)).1.hom ≫ (f (b k)).hom = (A k).1.hom :=
    fun k => CostructuredArrow.w (h k).hom
  let ι : ∀ k, (smallEtalePostcomp B S hS (f (b k)) (hf (b k))).obj (E k) ⟶ A k := fun k =>
    ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _)
      ((congrArg (· ≫ (A k).1.hom) (yoneda.map_id _)).trans
        ((Category.id_comp _).trans (hw k).symm)))
  let ι' : ∀ k, A k ⟶ (smallEtalePostcomp B S hS (f (b k)) (hf (b k))).obj (E k) := fun k =>
    ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _)
      ((congrArg (· ≫ _) (yoneda.map_id _)).trans
        ((Category.id_comp _).trans ((hw k).symm.trans (Category.assoc _ _ _).symm).symm)))
  have hιι : ∀ k, ι' k ≫ ι k = 𝟙 _ := fun k =>
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (Category.comp_id _))
  refine ⟨κ, hκ, b, E, fun k => ι k ≫ r k, hA, ?_⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hAcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro k
  refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨k, ι' k, ?_⟩
  rw [← Category.assoc, hιι, Category.id_comp]

/-- **Membership in a submodule is detected on charts of the members of an étale family.** A
section `s` of `M` over a chart `T` lies in a submodule `G ⊆ M` when, for a family of charts
`E k` of members whose postcomposites `g k : f_{b k}(E k) ⟶ T` generate a covering sieve, every
restriction `s|_{E k}` lies in the restriction `f_{b k}^* G`. -/
theorem mem_of_forall_mem_etaleSubmoduleRestrict (hf : ∀ i, IsEtale B S hS (f i).hom)
    {M : Modules.{u, u} B S hS X.1 X.2} (G : M.Submodule) {T : SmallEtale B S hS X.1}
    {κ : Type*} (b : κ → I) (E : ∀ k, SmallEtale B S hS (Yi (b k)).1)
    (g : ∀ k, (smallEtalePostcomp B S hS (f (b k)) (hf (b k))).obj (E k) ⟶ T)
    (hcov : Sieve.ofArrows (fun k => (smallEtalePostcomp B S hS (f (b k)) (hf (b k))).obj (E k))
      g ∈ SmallEtale.topology B S hS X.1 T) (s : M.val.obj (Opposite.op T))
    (hs : ∀ k, M.val.map (g k).op s ∈
      (etaleSubmoduleRestrict B S hS (f (b k)) (hf (b k)) G).obj (Opposite.op (E k))) :
    s ∈ G.obj (Opposite.op T) := by
  refine G.isSheaf s ((SmallEtale.topology B S hS X.1).superset_covering ?_ hcov)
  rintro Z _ ⟨Y, h, _, ⟨k⟩, rfl⟩
  have hk := G.map_mem h.op
    ((mem_etaleSubmoduleRestrict_obj B S hS (f (b k)) (hf (b k)) G (E k) _).1 (hs k))
  change M.val.map ((g k).op ≫ h.op) s ∈ G.obj (Opposite.op Z)
  have e := ConcreteCategory.congr_hom (M.val.map_comp (g k).op h.op) s
  exact (congrArg (· ∈ G.obj (Opposite.op Z)) e).mpr hk

end AlgebraicGeometry.Space

end
