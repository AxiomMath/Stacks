module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.FiniteEtaleLimit
public import StacksFrontier.AlgebraicGeometry.Limits.GermOpensLimit

/-!
# Cohomology at a point as the colimit over its neighbourhoods

Let `X = lim X_i` be the limit of a directed system of schemes over `S`, `ι_i : X_i ⟶ S`,
`g : X ⟶ S`, and `G` an abelian sheaf on `S`. When the cohomology of `g⁻¹G` is the colimit of the
cohomology of the `ι_i⁻¹G` (Theorem 09YQ,
`Stacks.EtaleCohomology.EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback`), every class on
`X` comes from a stage and a class of `S` dying on `X` dies at some stage. These elementwise
consequences are applied to the clopen neighbourhoods `V e`, `e ∉ P`, of a point of a scheme cut
out by the idempotents of a ring, and to their preimages under a morphism.

## Main definitions

* `Stacks.EtaleCohomology.IsOfCoconeCohomologyColimit`: the cohomology of `g⁻¹G` is the colimit of
  the cohomology of the `ι_i⁻¹G`.
* `Stacks.EtaleCohomology.IsGermCohomologyColimit`: the same for the neighbourhoods of a point.

## Main results

* `Stacks.EtaleCohomology.isGermCohomologyColimit`: Theorem 09YQ for the affine neighbourhoods of a
  point which is their limit.
* `Stacks.EtaleCohomology.IsGermCohomologyColimit.exists_eq_zero`,
  `Stacks.EtaleCohomology.IsGermCohomologyColimit.surjective`: a class dying at the point dies on a
  neighbourhood; every class at the point comes from the scheme when restriction to the
  neighbourhoods is surjective.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology

section Elements

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}}
  (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
  (c : Cone D) (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ ι i = g)
  (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ)

/-- The cohomology of the inverse image of `G` on the vertex of a cone is the colimit of the
cohomology of its inverse images to the stages, along the pullback maps. -/
abbrev IsOfCoconeCohomologyColimit : Prop :=
  IsSystemColimit
    (fun i => AddCommGrpCat.of (Sheaf.H.{u + 1} ((EtaleSheafSystem.ofCocone ι hι G).obj i) q))
    (fun a => AddCommGrpCat.ofHom
      (etaleCohomologyPullback (D.map a) ((EtaleSheafSystem.ofCocone ι hι G).map a) q))
    (AddCommGrpCat.of (Sheaf.H.{u + 1} ((smallEtalePullbackAb g).obj G) q))
    (fun i => AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i)
      (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i) q))

variable {ι hι c g hg G q}

include hι in
/-- The cohomology maps of the system of inverse images of one sheaf compose. -/
theorem IsOfCoconeCohomologyColimit.transition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map (a ≫ b))
        ((EtaleSheafSystem.ofCocone ι hι G).map (a ≫ b)) q) =
      AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map b)
        ((EtaleSheafSystem.ofCocone ι hι G).map b) q) ≫
      AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a)
        ((EtaleSheafSystem.ofCocone ι hι G).map a) q) := by
  ext y
  exact etaleCohomologyPullback_ofCocone_map_comp ι hι a b G q y

include hι hg in
/-- The cohomology maps of the system of inverse images of one sheaf are compatible with the
pullbacks to the limit. -/
theorem IsOfCoconeCohomologyColimit.transition_comp_leg {i j : Iᵒᵖ} (a : i ⟶ j) :
    AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a)
        ((EtaleSheafSystem.ofCocone ι hι G).map a) q) ≫
      AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i)
        (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i) q) =
    AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app j)
        (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G j) q) := by
  ext y
  exact etaleCohomologyPullback_ofCoconeLeg_comp ι hι c g hg a G q y

/-- **A class dying on the limit dies at a stage.** -/
theorem IsOfCoconeCohomologyColimit.exists_eq_zero [IsDirected I (· ≤ ·)] [Nonempty I]
    (hcoh : IsOfCoconeCohomologyColimit ι hι c g hg G q) (x : Sheaf.H.{u + 1} G q)
    (hx : etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj G)) q x = 0) :
    ∃ i, etaleCohomologyPullback (ι i) (𝟙 ((smallEtalePullbackAb (ι i)).obj G)) q x = 0 := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty I)
  obtain ⟨j, a, ha⟩ := IsSystemColimit.exists_eq_zero
    (fun a b => IsOfCoconeCohomologyColimit.transition_comp a b)
    (fun a => IsOfCoconeCohomologyColimit.transition_comp_leg a) hcoh
    (i := op i₀) (etaleCohomologyPullback (ι (op i₀)) (𝟙 _) q x)
    ((etaleCohomologyPullback_π_app_etaleCohomologyPullback ι c g hg (op i₀) G q x).trans hx)
  have ha' : etaleCohomologyPullback (D.map a) ((EtaleSheafSystem.ofCocone ι hι G).map a) q
      (etaleCohomologyPullback (ι (op i₀)) (𝟙 _) q x) = 0 := ha
  rw [etaleCohomologyPullback_ofCocone_map ι hι a G q x] at ha'
  exact ⟨j, ha'⟩

/-- **Every class on the limit comes from a stage.** -/
theorem IsOfCoconeCohomologyColimit.exists_eq [IsDirected I (· ≤ ·)] [Nonempty I]
    (hcoh : IsOfCoconeCohomologyColimit ι hι c g hg G q)
    (y : Sheaf.H.{u + 1} ((smallEtalePullbackAb g).obj G) q) :
    ∃ (i : Iᵒᵖ) (z : Sheaf.H.{u + 1} ((smallEtalePullbackAb (ι i)).obj G) q),
      etaleCohomologyPullback (c.π.app i) (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i) q z = y :=
  IsSystemColimit.exists_eq
    (fun a b => IsOfCoconeCohomologyColimit.transition_comp a b)
    (fun a => IsOfCoconeCohomologyColimit.transition_comp_leg a) hcoh y

end Elements

section Germs

open StacksDraft.IdempotentGluing OrderDual

variable {Y Z : Scheme.{u}} {C : Type u} [CommRing C] {V : Idem C → Y.Opens} (hmono : Monotone V)
  (P : Ideal C) [P.IsPrime] (s : Z ⟶ Y) (hs : ∀ e : GermIdx P, Set.range s.base ⊆ V (ofDual e.1))
  (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (q : ℕ)

/-- The cohomology at a point is the colimit of the cohomology of its neighbourhoods `V e`,
`e ∉ P`, along restriction. -/
abbrev IsGermCohomologyColimit : Prop :=
  IsOfCoconeCohomologyColimit (germOpensι hmono P) (germOpensDiagram_map_germOpensι hmono P)
    (germOpensCone hmono P s hs) s (germOpensCone_π_app_germOpensι hmono P s hs) G q

/-- **The cohomology at a point is the colimit of the cohomology of its neighbourhoods**
([Stacks, Tag 09YQ]), when the point is the limit of its neighbourhoods and these are affine. -/
theorem isGermCohomologyColimit [∀ e : GermIdx P, IsAffine (V (ofDual e.1))]
    (hc : IsLimit (germOpensCone hmono P s hs)) : IsGermCohomologyColimit hmono P s hs G q := by
  have : ∀ e : (GermIdx P)ᵒᵖ, IsAffine ((germOpensDiagram hmono P).obj e) := fun e =>
    inferInstanceAs (IsAffine (V (ofDual e.unop.1)))
  exact EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback hc q _ _ _
    (EtaleSheafSystem.isPullbackCocone_ofCocone _ _ _ _ _ G)
    (EtaleSheafSystem.isPullbackColimitPresentation_ofCocone _ _ _ _ _ G)

variable {hmono P s hs G q}

/-- **A class dying at the point dies on a neighbourhood.** -/
theorem IsGermCohomologyColimit.exists_eq_zero (h : IsGermCohomologyColimit hmono P s hs G q)
    (y : Sheaf.H.{u + 1} G q)
    (hy : etaleCohomologyPullback s (𝟙 ((smallEtalePullbackAb s).obj G)) q y = 0) :
    ∃ e : Idem C, (e : C) ∉ P ∧ etaleCohomologyPullback (V e).ι (𝟙 _) q y = 0 := by
  obtain ⟨j, hj⟩ := IsOfCoconeCohomologyColimit.exists_eq_zero h y hy
  have hj' : etaleCohomologyPullback (V (ofDual j.unop.1)).ι (𝟙 _) q y = 0 := hj
  exact ⟨ofDual j.unop.1, j.unop.2, hj'⟩

/-- **Every class at the point comes from the whole scheme**, when restriction to every
neighbourhood is surjective. -/
theorem IsGermCohomologyColimit.surjective (h : IsGermCohomologyColimit hmono P s hs G q)
    (hres : ∀ e : Idem C, Function.Surjective
      (etaleCohomologyPullback (V e).ι (𝟙 ((smallEtalePullbackAb (V e).ι).obj G)) q)) :
    Function.Surjective (etaleCohomologyPullback s (𝟙 ((smallEtalePullbackAb s).obj G)) q) := by
  intro y
  obtain ⟨i, z, rfl⟩ := IsOfCoconeCohomologyColimit.exists_eq h y
  obtain ⟨w, hw⟩ := hres (ofDual i.unop.1) z
  have hw' : etaleCohomologyPullback (germOpensι hmono P i) (𝟙 _) q w = z := hw
  rw [← hw']
  exact ⟨w, (etaleCohomologyPullback_π_app_etaleCohomologyPullback (germOpensι hmono P)
    (germOpensCone hmono P s hs) s (germOpensCone_π_app_germOpensι hmono P s hs) i G q w).symm⟩

end Germs


end Stacks.EtaleCohomology
