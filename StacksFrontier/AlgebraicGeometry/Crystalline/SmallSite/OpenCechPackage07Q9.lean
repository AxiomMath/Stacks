module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineSubsite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechPullback07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionOpen07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechFunctorial07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechLocal07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechProducts07Q9

/-!
# The Čech system of an affine open, packaged for the local step of [Stacks, Tag 07Q9]

The system `...SmallSite.openSystem07Q9` of the finite levels of the completed divided power
envelopes `D(n)` of a presentation of `Γ(W, 𝒪_X)`, for an affine open `W ⊆ X` lying over an affine
open of `S`, satisfies the hypotheses under which its Čech complexes compute cohomology over `W`:
`...SmallSite.IsOpenProCovering` (the objects lie over `W`, objects with affine ambient scheme
cover, every such object over `W` maps to a level of `T(0)`, and the levels of `T(n)` are
pro-products) and `...SmallSite.HasAffineMonoLevels` (affine ambient schemes and monomorphic
tower maps).  A morphism of presentations over `f : X' ⟶ X` gives a morphism of systems over `f`,
`...SmallSite.CechSystemHom`.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-- **The objects with affine ambient scheme cover every object of `Cris(X/S)`**: the affine
subsite is cover-dense. -/
theorem generate_hasAffineAmbient_mem (S : GlobalCrystallineSituation.{u})
    (B : CrystallineThickening S) :
    Sieve.generate (fun (B' : CrystallineThickening S) (_ : B' ⟶ B) => HasAffineAmbient S B') ∈
      smallTopology S B := by
  refine (smallTopology S).superset_covering ?_
    ((affineι_isCoverDense S).is_cover B)
  rintro B' g ⟨⟨Y, h, k, rfl⟩⟩
  exact ⟨_, h, k, Y.property.2, rfl⟩

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {ι : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A
    →ₐ[(openAffineSituation07Q9 S hW hVW).A] (openAffineSituation07Q9 S hW hVW).C)
  (hg : Function.Surjective g)

/-- **The Čech system of an affine open covers it**, in the sense of
`...SmallSite.IsOpenProCovering`. -/
theorem isOpenProCovering_openSystem07Q9 :
    IsOpenProCovering S W (openSystem07Q9 S hV hW hVW g hg) where
  liesOver n e := by
    intro x hx
    have := range_toX_openSystem07Q9 S hV hW hVW g hg n e
    change x ∈ (W : Set S.X)
    rw [← this]
    exact hx
  affine_covers B := generate_hasAffineAmbient_mem S B
  reach B hB hBW := by
    have : IsAffine B.obj.thickening.target.scheme := hB
    exact exists_hom_to_openSystem07Q9_level S hV hW hVW g hg B hB
      (fun x hx => hBW (by obtain ⟨y, rfl⟩ := hx; exact ⟨y, rfl⟩))
  isProProductAt B hB :=
    { exists_hom := fun n e φ => exists_openSystem07Q9_desc S hV hW hVW g hg B hB n e φ
      eventually_eq := fun n e ψ ψ' h =>
        ⟨e, le_rfl, by rw [openSystem07Q9_hom_ext S hV hW hVW g hg B hB ψ ψ' h]⟩ }

/-- **The Čech system of an affine open has affine ambient schemes and monomorphic tower
maps.** -/
theorem hasAffineMonoLevels_openSystem07Q9 :
    HasAffineMonoLevels (openSystem07Q9 S hV hW hVW g hg) where
  mono n e := mono_openSystem07Q9_map S hV hW hVW g hg n (Nat.le_succ e)
  isAffine n e := isAffine_target_openSystem07Q9 S hV hW hVW g hg n e

variable {X' : Scheme.{u}} (f : X' ⟶ S.X) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {κ : Type u}
  (g₂ : MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A
    →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A] (openAffineSituation₂07Q9 S hVW f hW₂).C)
  (hg₂ : Function.Surjective g₂)
  (r : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →+*
    MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A)
  (hr : g₂.toRingHom.comp r = (restrictMap07Q9 S hVW f).appTop.hom.comp g.toRingHom)

/-- **The morphism of Čech systems over `f`** attached to a morphism of presentations, as a
`...SmallSite.CechSystemHom`. -/
def openCechSystemHom07Q9 :
    CechSystemHom (S := overSituation S f) (S' := S) (𝟙 S.S) f (overSituation_compat S f)
      (openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
        g₂ hg₂)
      (openSystem07Q9 S hV hW hVW g hg) where
  k := openSystemShift07Q9 S hVW f hW₂
  τ n e := openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n.len e
  naturality_level n {_ _} h := openSystemMap07Q9_naturality_tower S hV hW hVW f hW₂ g hg g₂
    hg₂ r hr n.len (leOfHom h)
  naturality_simplicial {_ _} φ e := openSystemMap07Q9_naturality_simplicial S hV hW hVW f hW₂
    g hg g₂ hg₂ r hr φ e

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
