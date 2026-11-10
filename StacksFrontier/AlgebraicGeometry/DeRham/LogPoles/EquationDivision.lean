module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.Defs
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.IdealTrivialization
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Division by a local equation of a divisor on the sheaves of differential forms

Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be cut out by `I`, with the de Rham
complex of log poles defined for `Y ⊆ X` over `S` in the sense of [Stacks, Tag 0FMV]. Let `t` be
the local equation of `Y` on an open `U` attached to a trivialization of the ideal sheaf
(`Stacks.Divisors.IdealTrivialization`).

The second condition of Tag 0FMV says that `Ω^p_{X/S, y}` is `t`-torsion free at every point `y`
of `Y`; off `Y` the germ of `t` is a unit. Hence multiplication by `t` is injective on the
sections of `Ω^p_{X/S}` over every open `W ≤ U`
(`Stacks.Divisors.IdealTrivialization.eq_zero_of_equationAt_smul_eq_zero`), and a section which is
locally divisible by `t` is divisible by `t` (`Stacks.Divisors.IdealTrivialization.divide`).
The latter is an instance of a general principle for a sheaf of modules, recorded first: a
property of local sections which is stable under restriction, determines a section uniquely and
is satisfiable locally, is satisfied by a section over the whole open
(`TopCat.Sheaf.exists_of_local`).

This is the division `η = t⁻¹ (dt ∧ κ)` that the differential of the de Rham complex of log poles
performs in the proof of [Stacks, Tag 0FMW]; the source divides inside `Ω^p_{X/S}(Y)`, and the
torsion-freeness is what makes the quotient unique, hence glueable.

## References

* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}} {N : PresheafOfModules.{u} 𝒪}

/-- **A local property with unique local solutions has a global solution.** Let `Q` be a property
of sections of a sheaf of modules `N` over opens contained in `V`, stable under restriction, with
at most one solution over each open, and with a solution near every point of `V`. Then some
section over `V` satisfies `Q` near every point of `V`. -/
theorem exists_of_local
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    (V : Opens X) (Q : ∀ W : Opens X, N.obj (op W) → Prop)
    (hres : ∀ {W W' : Opens X} (h : W' ≤ W) (s : N.obj (op W)), W ≤ V → Q W s →
      Q W' (N.resLE h s))
    (huniq : ∀ {W : Opens X} (s s' : N.obj (op W)), W ≤ V → Q W s → Q W s' → s = s')
    (hex : ∀ x ∈ V, ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧ ∃ s, Q W s) :
    ∃ s : N.obj (op V), ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧ Q W (N.resLE hW s) := by
  choose W hWV hxW s hs using fun x : V => hex x.1 x.2
  have hcov : V ≤ ⨆ x, W x := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩
  obtain ⟨g, hg, -⟩ := existsUnique_gluing_of_isSheafPresheaf hN W hWV hcov s fun k l =>
    huniq _ _ (inf_le_left.trans (hWV k)) (hres inf_le_left _ (hWV k) (hs k))
      (hres inf_le_right _ (hWV l) (hs l))
  exact ⟨g, fun y hy => ⟨W ⟨y, hy⟩, hWV ⟨y, hy⟩, hxW ⟨y, hy⟩, (hg ⟨y, hy⟩).symm ▸ hs ⟨y, hy⟩⟩⟩

end TopCat.Sheaf

namespace Stacks.Divisors.IdealTrivialization

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- **Multiplication by a local equation is injective on differential forms.** If the de Rham
complex of log poles is defined, then on every open `W ≤ U` multiplication by the local
equation `t` kills no nonzero section of `Ω^p_{X/S}`: at a point of `Y` this is the torsion
freeness of [Stacks, Tag 0FMV], off `Y` the germ of `t` is a unit. -/
theorem eq_zero_of_equationAt_smul_eq_zero (h : f.HasLogPolesDeRhamComplex I) {W : X.Opens}
    (hW : W ≤ U) (p : ℕ) (ω : (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.obj (op W))
    (hω : e.equationAtR hW • ω = 0) : ω = 0 := by
  refine TopCat.Presheaf.section_ext
    ⟨(Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.presheaf,
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).isSheaf⟩ W ω 0 fun x hx => ?_
  have hg := PresheafOfModules.germ_smul (R := X.presheaf)
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val x W hx (e.equationAtR hW) ω
  have h0 : (X.presheaf.germ W x hx).hom (e.equationAt hW) •
      TopCat.Presheaf.germ (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.presheaf W x hx ω
        = 0 :=
    hg.symm.trans ((congrArg (fun z => TopCat.Presheaf.germ
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.presheaf W x hx z) hω).trans
        (map_zero _))
  change TopCat.Presheaf.germ (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.presheaf W x hx
      ω = TopCat.Presheaf.germ (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.presheaf W x hx
        0
  rw [map_zero]
  by_cases hxY : x ∈ I.support
  · have hxY' : x ∈ Set.range I.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hxY
    obtain ⟨y, rfl⟩ := hxY'
    exact (h.isSMulRegular y W hx (e.equationAt hW)
      (e.ker_stalkMap_eq_span_germ_equation hW y hx) p) (h0.trans (smul_zero _).symm)
  · obtain ⟨u, hu⟩ := e.isUnit_germ_equation_of_not_mem hW x hx hxY
    have h1 := congrArg (fun z => (↑u⁻¹ : X.presheaf.stalk x) • z) h0
    simp only [smul_zero] at h1
    rw [← h1, ← hu, smul_smul, Units.inv_mul, one_smul]

end Stacks.Divisors.IdealTrivialization

end
