module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite coproduct of representable sheaves on the small étale site

Let `U_0, …, U_{n-1}` be finitely many objects of the small étale site of a scheme `S` inside a
big étale site. The coproduct of the underlying schemes, with the induced morphism to `S`, is
an object `⊔ U_k` of the small étale site, the *disjoint union* of the family, and the
tautological inclusions `U_k ⟶ ⊔ U_k` form a covering family. The sheaf represented by `⊔ U_k`
is the coproduct of the sheaves represented by the `U_k`:

    ∐_k h_{U_k}  ≅  h_{⊔ U_k}.

## Main definitions

* `Stacks.EtaleCohomology.disjointUnionObj` — the disjoint union `⊔ U_k`, an object of the site.
* `Stacks.EtaleCohomology.disjointUnionHom` — the tautological inclusion `U_k ⟶ ⊔ U_k`.
* `Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion` — the isomorphism
  `∐_k h_{U_k} ≅ h_{⊔ U_k}`.

## Main results

* `Stacks.EtaleCohomology.ofArrows_disjointUnionHom_mem_topology` — the tautological inclusions
  cover the disjoint union.
* `Stacks.EtaleCohomology.isColimit_cofan_sheafifiedYoneda_disjointUnion` — **the sheaf
  represented by the disjoint union is the coproduct of the sheaves represented by the members**,
  with the tautological inclusions as the coproduct injections.
* `Stacks.EtaleCohomology.existsUnique_hom_disjointUnionObj_of_hom_sigma` — a morphism between
  two finite coproducts of representable sheaves on the small étale site is induced by a unique
  morphism of the site between the two disjoint unions.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {S : AlgebraicGeometry.Scheme.{u}}
  (hS : B.Contains S) {n : ℕ} (U : Fin n → SmallEtale B S hS)

/-! ### The disjoint union of a finite family of objects of the site -/

/-- The coproduct of the underlying schemes of a finite family of objects of the small étale
site lies below the size cutoff. -/
public theorem contains_sigma_toScheme_obj :
    B.Contains (∐ fun k => (SmallEtale.toScheme B S hS).obj (U k)) := by
  have h : (∐ ((fun k => (SmallEtale.toScheme B S hS).obj (U k)) ∘
      (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n))).size < B.cutoff :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 _
      fun i => contains_toScheme_obj B hS (U (Equiv.ulift i))
  have he := Scheme.size_congr (Sigma.reindex (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)
    fun k => (SmallEtale.toScheme B S hS).obj (U k))
  show (∐ fun k => (SmallEtale.toScheme B S hS).obj (U k)).size < B.cutoff
  rwa [← he]

/-- **The disjoint union of a finite family of objects of the small étale site**: the coproduct
of the underlying schemes, with the structure morphism induced by the universal property of the
coproduct. -/
@[ega "IV 11.10.3" "special case"]
public def disjointUnionObj : SmallEtale B S hS :=
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  mkObj B hS (∐ fun k => (SmallEtale.toScheme B S hS).obj (U k))
    (Sigma.desc fun k => B.inclusion.map (U k).obj.hom)
    (contains_sigma_toScheme_obj B hS U)
    (IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun k => etale_hom B hS (U k))

/-- The underlying scheme of the disjoint union is the coproduct of the underlying schemes. -/
@[simp]
public theorem toScheme_obj_disjointUnionObj :
    (SmallEtale.toScheme B S hS).obj (disjointUnionObj B hS U) =
      ∐ fun k => (SmallEtale.toScheme B S hS).obj (U k) :=
  rfl

/-- The tautological inclusion of a member of the family into the disjoint union. -/
public def disjointUnionHom (k : Fin n) : U k ⟶ disjointUnionObj B hS U :=
  mkHom B hS (Sigma.ι (fun j => (SmallEtale.toScheme B S hS).obj (U j)) k) (Sigma.ι_desc _ k)

/-- The underlying morphism of schemes of a tautological inclusion is the coproduct
injection. -/
@[simp]
public theorem toScheme_map_disjointUnionHom (k : Fin n) :
    (SmallEtale.toScheme B S hS).map (disjointUnionHom B hS U k) =
      Sigma.ι (fun j => (SmallEtale.toScheme B S hS).obj (U j)) k :=
  rfl

/-- The tautological inclusions cover the disjoint union. -/
public theorem ofArrows_disjointUnionHom_mem_topology :
    Sieve.ofArrows U (disjointUnionHom B hS U) ∈
      SmallEtale.topology B S hS (disjointUnionObj B hS U) :=
  ofArrows_mem_topology B hS U (disjointUnionHom B hS U) fun x =>
    (sigmaOpenCover fun k => (SmallEtale.toScheme B S hS).obj (U k)).exists_eq x

/-! ### The representable sheaf of the disjoint union -/

/-- A sheaf of sets on the small étale site has at most one section over an object whose
underlying scheme is empty. -/
private theorem subsingleton_sections_of_isEmpty
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) (Z : SmallEtale B S hS)
    (hZ : IsEmpty ((SmallEtale.toScheme B S hS).obj Z)) :
    Subsingleton (F.obj.obj (op Z)) := by
  have hcov : Sieve.ofArrows (fun _ : PEmpty.{1} => Z) (fun i => PEmpty.elim i) ∈
      SmallEtale.topology B S hS Z :=
    ofArrows_mem_topology B hS (fun _ : PEmpty.{1} => Z) (fun i => PEmpty.elim i) fun x =>
      hZ.elim x
  have hsf : Presieve.IsSheafFor F.obj
      (Presieve.ofArrows (fun _ : PEmpty.{1} => Z) (fun i => PEmpty.elim i)) :=
    ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS) F.obj).1 F.property).isSheafFor _
      hcov
  have h := (Presieve.isSheafFor_arrows_iff F.obj (fun i : PEmpty.{1} => PEmpty.elim i)).1 hsf
    (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)
  exact ⟨fun _ _ => h.unique (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)⟩

/-- A family of morphisms out of the representable sheaves of the members of a finite family of
objects of the small étale site extends uniquely over the disjoint union. -/
public theorem existsUnique_hom_disjointUnion
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (s : ∀ k, (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (U k) ⟶ F) :
    ∃! m : (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj
        (disjointUnionObj B hS U) ⟶ F,
      ∀ k, (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).map
        (disjointUnionHom B hS U k) ≫ m = s k := by
  classical
  have hcomp : Presieve.Arrows.Compatible F.obj (disjointUnionHom B hS U)
      fun k => Sheaf.sectionEquiv (SmallEtale.topology B S hS) (s k) := by
    intro i j Z a b hab
    by_cases hij : i = j
    · subst hij
      have hu : (SmallEtale.toScheme B S hS).map a = (SmallEtale.toScheme B S hS).map b :=
        (cancel_mono (Sigma.ι (fun k => (SmallEtale.toScheme B S hS).obj (U k)) i)).mp
          (congrArg (SmallEtale.toScheme B S hS).map hab)
      rw [hom_ext B hS hu]
    · have hempty : IsEmpty ((SmallEtale.toScheme B S hS).obj Z) :=
        AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
          (g := fun k => (SmallEtale.toScheme B S hS).obj (U k))
          ⟨congrArg (SmallEtale.toScheme B S hS).map hab⟩ hij
      have := subsingleton_sections_of_isEmpty B hS F Z hempty
      exact Subsingleton.elim _ _
  have hsf : Presieve.IsSheafFor F.obj (Presieve.ofArrows U (disjointUnionHom B hS U)) :=
    ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS) F.obj).1 F.property).isSheafFor _
      (ofArrows_disjointUnionHom_mem_topology B hS U)
  obtain ⟨t, ht, htu⟩ :=
    (Presieve.isSheafFor_arrows_iff F.obj (disjointUnionHom B hS U)).1 hsf _ hcomp
  refine ⟨(Sheaf.sectionEquiv (SmallEtale.topology B S hS)).symm t, fun k => ?_, fun y hy => ?_⟩
  · apply (Sheaf.sectionEquiv (SmallEtale.topology B S hS)).injective
    rw [Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply]
    exact ht k
  · have hy' : ∀ k, F.obj.map (disjointUnionHom B hS U k).op
        (Sheaf.sectionEquiv (SmallEtale.topology B S hS) y) =
          Sheaf.sectionEquiv (SmallEtale.topology B S hS) (s k) := by
      intro k
      rw [← Sheaf.sectionEquiv_map_comp, hy k]
    rw [← htu _ hy', Equiv.symm_apply_apply]

/-- **A finite coproduct of representable sheaves on the small étale site is represented by the
disjoint union.** The sheaf represented by `⊔ U_k` is the coproduct of the sheaves represented by
the `U_k`, with the tautological inclusions as the coproduct injections. -/
public def isColimit_cofan_sheafifiedYoneda_disjointUnion :
    IsColimit (Cofan.mk
      (f := fun k => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (U k))
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (disjointUnionObj B hS U))
      fun k => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).map
        (disjointUnionHom B hS U k)) :=
  Cofan.IsColimit.mk _
    (fun t => (existsUnique_hom_disjointUnion B hS U t.pt t.inj).choose)
    (fun t k => (existsUnique_hom_disjointUnion B hS U t.pt t.inj).choose_spec.1 k)
    (fun t m hm => (existsUnique_hom_disjointUnion B hS U t.pt t.inj).choose_spec.2 m hm)

/-- **The coproduct of the representable sheaves of a finite family of objects of the small étale
site is the representable sheaf of their disjoint union.** -/
public def sigmaSheafifiedYonedaIsoDisjointUnion
    [HasColimitsOfShape (Discrete (Fin n))
      (Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))] :
    (∐ fun k => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (U k)) ≅
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (disjointUnionObj B hS U) :=
  (colimit.isColimit (Discrete.functor
      fun k => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj
        (U k))).coconePointUniqueUpToIso
    (isColimit_cofan_sheafifiedYoneda_disjointUnion B hS U)

/-- The identification of the coproduct with the representable sheaf of the disjoint union
carries the `k`-th coproduct injection to the tautological inclusion of `U k`. -/
@[simp]
public theorem ι_comp_sigmaSheafifiedYonedaIsoDisjointUnion_hom
    [HasColimitsOfShape (Discrete (Fin n))
      (Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))] (k : Fin n) :
    Sigma.ι (fun j => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (U j)) k ≫
        (sigmaSheafifiedYonedaIsoDisjointUnion B hS U).hom =
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).map (disjointUnionHom B hS U k) :=
  (colimit.isColimit (Discrete.functor
    fun j => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj
      (U j))).comp_coconePointUniqueUpToIso_hom
    (isColimit_cofan_sheafifiedYoneda_disjointUnion B hS U) ⟨k⟩

/-- **A morphism between two finite coproducts of representable sheaves on the small étale site
is induced by a unique morphism of the site between the two disjoint unions.** -/
public theorem existsUnique_hom_disjointUnionObj_of_hom_sigma
    [HasColimitsOfShape (Discrete (Fin n))
      (Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))]
    {m : ℕ} (V : Fin m → SmallEtale B S hS)
    [HasColimitsOfShape (Discrete (Fin m))
      (Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))]
    (φ : (∐ fun j => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (V j)) ⟶
      ∐ fun k => (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj (U k)) :
    ∃! f : disjointUnionObj B hS V ⟶ disjointUnionObj B hS U,
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).map f =
        (sigmaSheafifiedYonedaIsoDisjointUnion B hS V).inv ≫ φ ≫
          (sigmaSheafifiedYonedaIsoDisjointUnion B hS U).hom := by
  have hsub : (SmallEtale.topology B S hS).Subcanonical :=
    AlgebraicGeometry.smallEtaleTopology_subcanonical' B (B.obj S hS)
  have hff := Sheaf.fullyFaithfulSheafifiedYoneda (SmallEtale.topology B S hS)
  refine ⟨hff.preimage ((sigmaSheafifiedYonedaIsoDisjointUnion B hS V).inv ≫ φ ≫
      (sigmaSheafifiedYonedaIsoDisjointUnion B hS U).hom), hff.map_preimage _, fun f hf => ?_⟩
  apply hff.map_injective
  rw [hf, hff.map_preimage]

end Stacks.EtaleCohomology

end
