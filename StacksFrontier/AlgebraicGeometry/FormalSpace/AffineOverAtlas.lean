module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine

/-!
# The affine étale atlas of an algebraic space, presented by spectra of rings

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an algebraic space over `S`.
Definition 025Y gives `X` an étale atlas `U ⟶ X` by a single object of the site; refining `U` by
its affine open covering gives an atlas by *affine* objects of the site, which is the form
**Stacks 03FR** gives it.

The affine charts produced this way are affine objects of the site, whereas the statements about
completions of affine schemes — Stacks 0AIY and Stacks 0GBA — consume an affine scheme in the
shape `Spec A` with a structure morphism to `S`, namely
`AlgebraicGeometry.FormalSpace.affineOver`. Every affine object `V` of the site is of that shape
up to isomorphism, with `A = Γ(V, 𝒪)`, and this file records that identification so that the
atlas can be handed over in the shape those statements want.

## Main definitions

* `AlgebraicGeometry.FormalSpace.globalSectionsStructureMap`: the structure morphism to `S` of
  the spectrum of the ring of global sections of an affine object of the site.
* `AlgebraicGeometry.FormalSpace.affineOverGlobalSectionsIso`: the identification of an affine
  object of the site with the `affineOver` presentation of that spectrum.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_etale_atlas_presheaf`: **Stacks 03FR**, an
  algebraic space over `S` has an affine étale atlas by objects of the site; joint surjectivity
  is recorded as a covering sieve, which is the form a consumer of the atlas uses.

## Implementation notes

Joint surjectivity is stated sectionwise — every section of `X` restricts, along the arrows of a
covering sieve, to a section coming from one of the charts — rather than as local surjectivity of
the morphism out of a coproduct of sheaves. That is what the proof produces, by transitivity from
the covering sieve on which a section lifts to the atlas `U` and the affine open covering of `U`;
and it is what the sheaf-level statement is proved *from*, through
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff`.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Presentation

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- The structure morphism to `S` of the spectrum of the ring of global sections. -/
def globalSectionsStructureMap :
    Spec (.of ↥Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ⟶ S :=
  ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map V.hom

/-- An affine object of the site is isomorphic to the `affineOver` presentation of the
spectrum of its ring of global sections. -/
def affineOverGlobalSectionsIso :
    affineOver B S hS (contains_spec_globalSections B S hS V)
        (globalSectionsStructureMap B S hS V) ≅ V :=
  Over.isoMk
    { hom := ObjectProperty.homMk
        (show Spec Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⟶
          B.inclusion.obj V.left from ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv)
      inv := ObjectProperty.homMk
        (show B.inclusion.obj V.left ⟶
          Spec Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) from
          ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom)
      hom_inv_id :=
        ObjectProperty.hom_ext _ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv_hom_id
      inv_hom_id :=
        ObjectProperty.hom_ext _ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom_inv_id }
    (ObjectProperty.hom_ext _ rfl)

end Presentation
section Atlas

attribute [local instance] MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- A morphism out of a representable presheaf is compatible with restriction along `k`. -/
private theorem app_comp_eq_map_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A W W' V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ X) (k : W' ⟶ W) (t : W ⟶ V)
    {g : W ⟶ A} {s : X.obj (op A)} (h : φ.app (op W) t = X.map g.op s) :
    φ.app (op W') (k ≫ t) = X.map (k ≫ g).op s := by
  have hnat := NatTrans.naturality_apply φ k.op t
  change φ.app (op W') (k ≫ t) = _ at hnat
  rw [hnat, h, op_comp, X.map_comp]
  rfl

/-- **Every algebraic space over `S` has an affine étale atlas by objects of the site.** The
étale scheme atlas `U ⟶ X` of Definition 025Y is refined by the affine open covering of `U`;
étaleness is recorded as the relative étale property of a morphism of presheaves, and joint
surjectivity in the form a covering sieve takes: every section of `X` restricts, along the
arrows of a covering sieve, to a section coming from one of the charts. -/
theorem exists_affine_etale_atlas_presheaf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      ∃ a : ∀ i, yoneda.obj (V i) ⟶ X,
        (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (a i)) ∧
        ∀ (U : BigFppfOver B S hS) (s : X.obj (op U)),
          ∃ R : Sieve U, R ∈ BigFppfOver.topology B S hS U ∧
            ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ U), R g →
              ∃ (i : I) (t : W ⟶ V i), (a i).app (op W) t = X.map g.op s := by
  classical
  let J := BigFppfOver.topology B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  obtain ⟨U₀, f, hfsurj, hfet⟩ := hX.exists_atlas
  obtain ⟨I, V, π, hVaff, hπ, hcovU, -⟩ := BigFppfOver.exists_affine_open_cover' B S hS U₀
  refine ⟨I, V, hVaff, fun i ↦ yoneda.map (π i) ≫ f, fun i ↦ ?_, ?_⟩
  · have := hπ i
    exact MorphismProperty.comp_mem P.presheaf _ _
      ((Space.presheaf_yoneda_map_etale_iff B S hS (π i)).2 inferInstance) hfet
  intro U s
  let R : Sieve U :=
    { arrows := fun W g ↦ (∃ (i : I) (t : W ⟶ V i),
        (yoneda.map (π i) ≫ f).app (op W) t = X.map g.op s)
      downward_closed := by
        rintro W W' g ⟨i, t, ht⟩ k
        exact ⟨i, k ≫ t, app_comp_eq_map_comp B S hS _ k t ht⟩ }
  refine ⟨R, ?_, fun _ _ hg ↦ hg⟩
  · apply J.transitive
      ((Space.isLocallySurjective_of_surjective_etale B S hS f hfsurj hfet).imageSieve_mem s)
    rintro W g ⟨t₀, ht₀⟩
    refine J.superset_covering ?_ (J.pullback_stable t₀ hcovU)
    rintro W' k ⟨Z, c, d, ⟨i⟩, hfac⟩
    refine ⟨i, c, ?_⟩
    change f.app (op W') (c ≫ π i) = X.map (k ≫ g).op s
    rw [show c ≫ π i = k ≫ t₀ from hfac]
    exact app_comp_eq_map_comp B S hS f k t₀ ht₀

end Atlas
end AlgebraicGeometry.FormalSpace

end
