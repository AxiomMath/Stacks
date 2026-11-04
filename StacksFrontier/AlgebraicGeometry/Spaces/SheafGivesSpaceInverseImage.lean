module

public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceBoundedCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A sheaf whose inverse image is representable is representable

Let `Y` and `X` be algebraic spaces over `S` and let `F` be a faithful functor from sheaves of
sets on the spaces-étale site of `Y` to those on the spaces-étale site of `X` which has a right
adjoint — the inverse image along a morphism `X ⟶ Y` along which descent of sheaves is
effective, say. If `M` is a sheaf on `Y` with `F M ≅ h_U` for an algebraic space `U` étale
over `X`, then `M ≅ h_W` for an algebraic space `W` étale over `Y`.

This is the set-theoretic condition of Stacks 0GF6 for the sheaves arising in Stacks 0GG0: one
has to find a single étale chart `V ⟶ Y` together with a section of `M` over it which induces an
epimorphism `h_V ⟶ M`, after which the core of Stacks 0GF6,
`AlgebraicGeometry.Space.SheafGivesSpace.nonempty_iso_quotObj`, applies. The proof:

* the sections of `M` over the étale charts of `Y` of size at most a fixed cardinal `κ` below the
  cutoff jointly cover `M` (`AlgebraicGeometry.Space.SpacesEtale.sheaf_hom_ext_of_boundedSieve`);
* since `F` is a left adjoint, their images jointly cover `F M ≅ h_U`: the morphisms `T ⟶ U`
  which lift through `F` of one of these sections form a covering sieve of `U`
  (`AlgebraicGeometry.Space.SheafGivesSpace.chartImageSieve_mem`), because the subsheaf of
  `h_U` which they generate locally is the whole of `h_U`;
* hence every point of `U` is hit by one of them, and the points of a scheme atlas of `U`
  index a family of charts, each of size at most `κ`, which suffices; the index set has fewer
  points than the cutoff, so the disjoint union `V` of this family is an étale chart of `Y`
  (`AlgebraicGeometry.Space.SmallEtale.exists_sigma_of_size_le`), and the sections glue to a
  section `s` of `M` over `V`;
* `F (h_V ⟶ M)` is surjective onto `h_U` by construction, and `F` reflects epimorphisms, being
  faithful.

## Main results

* `AlgebraicGeometry.Space.SheafGivesSpace.exists_iso_yoneda_of_inverseImage_iso`: the
  statement above.

## References

* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/-- A morphism of sheaves of sets into the sheaf represented by `U` is an epimorphism as soon as
the identity of `U` lifts locally, that is, as soon as the morphisms `T ⟶ U` which lift form a
covering sieve of `U`. -/
@[sga "3 IV 6.7.3" "Clause (i)(2)",
  sga "3 VIB 10.15" "partial",
  sga "3 VIIA 8.1.4" "special case",
  sga "4 II 5.1" "special case"]
theorem epi_of_imageSieve_id_mem {E : Sheaf J (Type v)} {U : C} (ψ : E ⟶ J.yoneda.obj U)
    (h : Presheaf.imageSieve ψ.hom (show (CategoryTheory.yoneda.obj U).obj (op U) from 𝟙 U) ∈
      J U) :
    Epi ψ := by
  have : Sheaf.IsLocallySurjective ψ := ⟨fun {T} g ↦ by
    have := J.pullback_stable (show T ⟶ U from g) h
    rw [Presheaf.pullback_imageSieve] at this
    convert this using 2
    simp⟩
  infer_instance

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace SheafGivesSpace

variable {X Y : AlgebraicSpaces B S hS}
  (F : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)) ⥤
    Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
  {M : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))} {U : SpacesEtale B S hS X}
  (i : F.obj M ≅ (SpacesEtale.topology B S hS X).yoneda.obj U)

/-- The sieve of `U` of the morphisms `T ⟶ U` which lift through `F` of the morphism
`h_A ⟶ M` given by a section of `M` over an étale chart `A` of `Y` of size at most `κ`. -/
def chartImageSieve (κ : Cardinal.{u}) : Sieve U where
  arrows T g := ∃ (A : SmallEtale B S hS Y.1) (_ : SmallEtale.chartSize B S hS A ≤ κ)
    (t : M.obj.obj (op ((comparisonFunctor B S hS Y).obj A))),
    Presheaf.imageSieve (F.map ((SpacesEtale.topology B S hS Y).yonedaEquiv.symm t) ≫ i.hom).hom
      (show (yoneda.obj U).obj (op U) from 𝟙 U) g
  downward_closed := by
    rintro T T' g ⟨A, hA, t, hg⟩ e
    exact ⟨A, hA, t, Sieve.downward_closed _ hg e⟩

/-- **The images of the bounded charts cover `U`.** If the charts of size at most `κ` cover
every object of the spaces-étale site of `Y` and `F` is a left adjoint, then
`AlgebraicGeometry.Space.SheafGivesSpace.chartImageSieve` is a covering sieve of `U`. Let
`Q ⊆ h_U` be the subsheaf which it generates locally. Each `F (h_A ⟶ M) ≫ i` factors through
`Q`, so two morphisms out of `h_U` agreeing on `Q` agree after composing with every one of
them; transposing along the adjunction, they agree on every bounded chart of `M`, hence are
equal. So `Q ⟶ h_U` is an epimorphism, hence locally surjective, and the sieve is covering. -/
theorem chartImageSieve_mem {P : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))} (adj : F ⊣ P) {κ : Cardinal.{u}}
    (hκ : ∀ Z : SpacesEtale B S hS Y,
      SpacesEtale.boundedSieve κ Z ∈ SpacesEtale.topology B S hS Y Z) :
    chartImageSieve F i κ ∈ SpacesEtale.topology B S hS X U := by
  let J := SpacesEtale.topology B S hS X
  let JY := SpacesEtale.topology B S hS Y
  let R := chartImageSieve F i κ
  let Q : Subfunctor (yoneda.obj U) :=
    { obj := fun T ↦ {g | R g}
      map := fun {_ _} e g hg ↦ R.downward_closed hg e.unop }
  let Qs : Sheaf J (Type (u + 1)) := ⟨(Q.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2
      (Q.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).1 (J.yoneda.obj U).property))⟩
  let ι : Qs ⟶ J.yoneda.obj U := ⟨(Q.sheafify J).ι⟩
  have hfac : ∀ (A : SmallEtale B S hS Y.1) (hA : SmallEtale.chartSize B S hS A ≤ κ)
      (t : M.obj.obj (op ((comparisonFunctor B S hS Y).obj A))),
      ∃ l : F.obj (JY.yoneda.obj _) ⟶ Qs, l ≫ ι = F.map (JY.yonedaEquiv.symm t) ≫ i.hom := by
    intro A hA t
    refine ⟨⟨Subfunctor.lift (F.map (JY.yonedaEquiv.symm t) ≫ i.hom).hom ?_⟩, rfl⟩
    rintro T _ ⟨e, rfl⟩
    exact Q.le_sheafify J T ⟨A, hA, t, e, by simp [JY]⟩
  have hepi : Epi ι := ⟨fun {N} a b hab ↦ by
    apply (cancel_epi i.hom).1
    apply (adj.homEquiv _ _).injective
    refine SpacesEtale.sheaf_hom_ext_of_boundedSieve hκ fun A hA t ↦ ?_
    obtain ⟨l, hl⟩ := hfac A hA t
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left,
      ← Category.assoc, ← hl, Category.assoc, hab, ← Category.assoc, hl, Category.assoc]⟩
  have hls := (Sheaf.isLocallySurjective_iff_epi ι).2 hepi
  refine J.transitive (Presheaf.imageSieve_mem J ι.hom
    (show (yoneda.obj U).obj (op U) from 𝟙 U)) R ?_
  rintro T g ⟨q, hq⟩
  obtain rfl : q.1 = g := hq.trans (by simp)
  exact J.superset_covering (fun _ _ he ↦ he) q.2

include i in
/-- **A sheaf whose inverse image is representable is representable.** Let `F` be a faithful
left adjoint from sheaves of sets on the spaces-étale site of `Y` to sheaves of sets on the
spaces-étale site of `X`, and let `M` be a sheaf on `Y` with `F M ≅ h_U` for an algebraic space
`U` étale over `X`. Then `M ≅ h_W` for an algebraic space `W` étale over `Y`.

This is the set-theoretic condition of Stacks 0GF6 for `M`, which the proof of Stacks 0GG0
needs for the inverse image along a morphism of effective descent for spaces-étale sheaves. -/
theorem exists_iso_yoneda_of_inverseImage_iso
    {P : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))} (adj : F ⊣ P) [F.Faithful] :
    ∃ W : SpacesEtale B S hS Y,
      Nonempty (M ≅ (SpacesEtale.topology B S hS Y).yoneda.obj W) := by
  let JY := SpacesEtale.topology B S hS Y
  obtain ⟨κ, hκlt, hκ⟩ := SpacesEtale.exists_boundedSieve_mem Y
  have hR := chartImageSieve_mem F i adj hκ
  rw [SpacesEtale.mem_topology_iff_sievePointwiseCover] at hR
  have hU := ((SpacesEtale.toSpaces B S hS X).obj U).property
  obtain ⟨T, a, hasurj, -⟩ := hU.exists_atlas
  have hpts := (presheafSurjective_iff_isSurjective_yoneda B S hS _ hU T a).1 hasurj
  let I := (BigFppfOver.toScheme B S hS).obj T
  let w : I → points B S hS (yoneda.obj T) := fun τ ↦
    (surjective_pointsToScheme B S hS T τ).choose
  choose V f hf y hy using fun τ : I ↦ hR (pointsMap B S hS (yoneda.obj T) a (w τ))
  choose A hA t ht using hf
  obtain ⟨V', j, hmono, hcov, hdisj⟩ := SmallEtale.exists_sigma_of_size_le A
    (max_lt hκlt (mk_points_lt_cutoff B S hS T)) (le_max_right _ _)
    (fun τ ↦ (hA τ).trans (le_max_left _ _))
  have hM' : Presieve.IsSheaf (SmallEtale.topology B S hS Y.1)
      ((comparisonFunctor B S hS Y).op ⋙ M.obj) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Functor.op_comp_isSheaf _ (SmallEtale.topology B S hS Y.1) JY M)
  obtain ⟨s, hs, -⟩ := hM'.existsUnique_section_of_disjoint_arrows j hcov hmono hdisj t
  have hψ : ∀ τ, F.map (JY.yonedaEquiv.symm (t τ)) ≫ i.hom =
      F.map (JY.yoneda.map ((comparisonFunctor B S hS Y).map (j τ))) ≫
        F.map (JY.yonedaEquiv.symm s) ≫ i.hom := by
    intro τ
    rw [← hs τ, ← Category.assoc, ← F.map_comp]
    exact congrArg (fun k ↦ F.map k ≫ i.hom)
      (GrothendieckTopology.yonedaEquiv_symm_naturality_left _ _ _ _).symm
  have hepi : Epi (F.map (JY.yonedaEquiv.symm s) ≫ i.hom) := by
    refine GrothendieckTopology.epi_of_imageSieve_id_mem _ _ ?_
    rw [SpacesEtale.mem_topology_iff_sievePointwiseCover]
    intro x
    obtain ⟨w₀, rfl⟩ := hpts x
    have hw : w (pointsToScheme B S hS T w₀) = w₀ := injective_pointsToScheme B S hS T
      (surjective_pointsToScheme B S hS T (pointsToScheme B S hS T w₀)).choose_spec
    refine ⟨V (pointsToScheme B S hS T w₀), f (pointsToScheme B S hS T w₀), ?_,
      y (pointsToScheme B S hS T w₀), (hy _).trans (by rw [hw])⟩
    obtain ⟨e, he⟩ := ht (pointsToScheme B S hS T w₀)
    refine ⟨(F.map (JY.yoneda.map ((comparisonFunctor B S hS Y).map
      (j (pointsToScheme B S hS T w₀))))).hom.app _ e, ?_⟩
    rw [← he, hψ]
    rfl
  have : Epi (F.map (JY.yonedaEquiv.symm s)) := (epi_comp_iff_of_isIso _ _).1 hepi
  have : Epi (JY.yonedaEquiv.symm s) := F.epi_of_epi_map this
  exact ⟨quotObj s, nonempty_iso_quotObj s⟩

end SheafGivesSpace

end AlgebraicGeometry.Space

end
