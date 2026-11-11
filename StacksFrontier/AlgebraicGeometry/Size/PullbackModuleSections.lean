module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Pullback

/-!
# Size of the sections of the pullback of a quasi-coherent module

Let `g : Y ⟶ X` be a morphism of schemes and `𝒩` a quasi-coherent `𝒪_X`-module. If the
sections of `𝒩` over the members of an affine open cover `{Oᵢ}` of `X` are bounded by a single
cardinal `c`, then the sections of `g^*𝒩` over *every* open of `Y` are bounded by
`(max (size Y) c) ^ size Y`, a cardinal depending on `Y` and `c` only.

Over an affine open `Z ⊆ Y` mapping into some `Oᵢ` the sections of `g^*𝒩` are
`Γ(Y, Z) ⊗_{Γ(X, Oᵢ)} Γ(𝒩, Oᵢ)`, of cardinality at most `max (size Y) c`; such affine opens
cover any open `W` of `Y`, and they are at most `size Y` in number, so the sheaf property embeds
the sections over `W` into a product of at most `size Y` factors each of that size.

The second ingredient is the elementary fact that the sections over one of two disjoint opens
are a quotient of the sections over their union, a sheaf over a disjoint union being the product
of its restrictions.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mk_sections_le_of_inf_eq_bot`: the sections over one of two
  disjoint opens are at most as many as those over their union.
* `AlgebraicGeometry.Scheme.Modules.mk_sections_pullback_le`: the bound on the sections of a
  pullback described above.

## References

* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **The sections over one of two disjoint opens are a quotient of those over their union.** A
sheaf over a disjoint union is the product of its restrictions, and a projection out of a product
of abelian groups is split by the inclusion with zero second component. -/
theorem mk_sections_le_of_inf_eq_bot (N : X.Modules) {U V : X.Opens} (h : U ⊓ V = ⊥) :
    #Γ(N, U) ≤ #Γ(N, U ⊔ V) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨N.presheaf, N.isSheaf⟩
  obtain ⟨l, hl, -⟩ :=
    BinaryFan.IsLimit.lift' (F.isProductOfDisjoint U V h) (𝟙 (F.1.obj (op U))) 0
  exact Cardinal.mk_le_of_surjective (f := N.presheaf.map (homOfLE le_sup_left).op) fun a =>
    ⟨l a, congrArg (fun φ => φ a) (congrArg (fun ψ => (ConcreteCategory.hom ψ : _ → _)) hl)⟩

/-- **Sections of a pullback over an affine open mapping into an affine open.** If `Z` is an
affine open of `Y` with `Z ⊆ g⁻¹U` for an affine open `U` of `X`, the sections of `g^*𝒩` over `Z`
are at most `max (size Y) #Γ(𝒩, U)`. -/
theorem mk_sections_pullback_le_of_le_preimage (g : Y ⟶ X) (N : X.Modules) [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (Z : Y.affineOpens) (hZ : Z.1 ≤ g ⁻¹ᵁ U) :
    #Γ((Scheme.Modules.pullback g).obj N, Z.1) ≤ max Y.size #Γ(N, U) :=
  calc #Γ((Scheme.Modules.pullback g).obj N, Z.1)
      = #((ModuleCat.extendScalars (g.appLE U Z.1 hZ).hom).obj
          (ModuleCat.of Γ(X, U) Γ(N, U))) :=
        (Cardinal.mk_congr
          (affinePullbackSectionsBaseChangeIso g N hU Z.2 hZ).toLinearEquiv.toEquiv).symm
    _ ≤ max ℵ₀ (max #Γ(Y, Z.1) #Γ(N, U)) := Cardinal.mk_tensorProduct_le
    _ ≤ max Y.size #Γ(N, U) :=
        max_le (Y.aleph0_le_size.trans (le_max_left _ _))
          (max_le_max (Y.mk_sections_le_size Z) le_rfl)

/-- **A bound on the sections of a pullback, uniform over the opens of the source.** Let
`g : Y ⟶ X` be a morphism of schemes and `𝒩` a quasi-coherent `𝒪_X`-module whose sections over
the members of an affine open cover `{Oᵢ}` of `X` are at most `c`. Then the sections of `g^*𝒩`
over every open of `Y` are at most `(max (size Y) c) ^ size Y`.

Over an affine open `Z` of `Y` inside some `g⁻¹Oᵢ` the sections of `g^*𝒩` are
`Γ(Y, Z) ⊗_{Γ(X, Oᵢ)} Γ(𝒩, Oᵢ)` by `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`,
hence at most `max (size Y) c`; such affine opens cover every open `W` of `Y`, and there are at
most `size Y` of them, so the sections over `W` embed in a product of at most `size Y` such
factors. -/
theorem mk_sections_pullback_le (g : Y ⟶ X) (N : X.Modules) [N.IsQuasicoherent]
    {ι : Type*} (O : ι → X.Opens) (hO : ∀ i, IsAffineOpen (O i)) (hcov : ⨆ i, O i = ⊤)
    {c : Cardinal.{u}} (hc : ∀ i, #Γ(N, O i) ≤ c) (W : Y.Opens) :
    #Γ((Scheme.Modules.pullback g).obj N, W) ≤ max Y.size c ^ Y.size := by
  set P := (Scheme.Modules.pullback g).obj N
  let J := {Z : Y.affineOpens // Z.1 ≤ W ∧ ∃ i, Z.1 ≤ g ⁻¹ᵁ O i}
  have hcoverJ : W ≤ ⨆ z : J, z.1.1 := by
    intro y hy
    have hgy : g y ∈ ⨆ i, O i := by
      rw [hcov]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hgy
    obtain ⟨_, ⟨Z, hZ, rfl⟩, hyZ, hZW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (a := y) (show y ∈ ((W ⊓ g ⁻¹ᵁ O i : Y.Opens) : Set Y) from ⟨hy, hi⟩)
      (W ⊓ g ⁻¹ᵁ O i).2
    have hZW : Z ≤ W ⊓ g ⁻¹ᵁ O i := hZW
    exact Opens.mem_iSup.mpr
      ⟨⟨⟨Z, hZ⟩, hZW.trans inf_le_left, i, hZW.trans inf_le_right⟩, hyZ⟩
  let F : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨P.presheaf, P.isSheaf⟩
  have hinj : Function.Injective
      (fun s : Γ(P, W) => fun z : J => P.presheaf.map (homOfLE z.2.1).op s) := fun s t hst =>
    TopCat.Sheaf.eq_of_locally_eq' F (fun z : J => z.1.1) W (fun z => homOfLE z.2.1)
      hcoverJ s t (congrFun hst)
  have hfactor : ∀ z : J, #Γ(P, z.1.1) ≤ max Y.size c := by
    intro z
    obtain ⟨i, hi⟩ := z.2.2
    exact (mk_sections_pullback_le_of_le_preimage g N (hO i) z.1 hi).trans
      (max_le_max le_rfl (hc i))
  have hJ : #J ≤ Y.size :=
    (Cardinal.mk_le_of_injective (f := fun z : J => z.1) fun _ _ h => Subtype.ext h).trans
      Y.mk_affineOpens_le_size
  have hD : max Y.size c ≠ 0 :=
    ((aleph0_pos.trans_le Y.aleph0_le_size).trans_le (le_max_left _ _)).ne'
  calc #Γ(P, W) ≤ #(∀ z : J, Γ(P, z.1.1)) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.prod fun z : J => #Γ(P, z.1.1) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod fun _ : J => max Y.size c := Cardinal.prod_le_prod _ _ hfactor
    _ = max Y.size c ^ #J := by rw [Cardinal.prod_const, lift_id, lift_id]
    _ ≤ max Y.size c ^ Y.size := Cardinal.power_le_power_left hD hJ

end AlgebraicGeometry.Scheme.Modules

end
