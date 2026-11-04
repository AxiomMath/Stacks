module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BasicOpenSmulRegular
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBaseChange

/-!
# Operators on a principal-open refinement of a chart which agree after restriction

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `c` be an affine chart of the fibre
product `X ×_S Y` and let `e` be a chart whose range is the principal open of a section `s` of the
structure sheaf over the range of `c`. For a quasi-coherent module `M` on `X ×_S Y` the sections
over the range of `e` are then the localization of the sections over the range of `c` away from
`s`, and multiplication by a power of `s` is injective on the sections of any module over the range
of `e`. Two differential operators of order at most `k` on `X ×_S Y / Y` defined over the opens of
`e` consequently agree as soon as they agree on the sections restricted from the range of `c`: the
order bound makes an operator on a localized module determined by its values on the image of the
localization map.

## Main results

* `AlgebraicGeometry.order_section_of_isDiffOpOfOrder`: an operator of order at most `k` on `X/Z`
  over the opens of `U₀`, read on the sections over an open `V`, is a differential operator of
  order at most `k` for the action of the sections of the structure sheaf over any open `U`
  containing `V` by restriction of scalars.
* `AlgebraicGeometry.isLocalizedModule_restriction_of_eq_basicOpen` and
  `AlgebraicGeometry.injective_smul_powers_of_eq_basicOpen`: the localization and the injectivity,
  stated for an open which is merely equal to the principal open of the section.
* `Stacks.FibreProductAffineChart.Chart.rawOp_ext_of_restriction`: **two differential operators of
  order at most `k` on `X ×_S Y / Y` over the opens of a chart whose range is a principal open of
  the range of a second chart, and which agree on the sections restricted from the second chart,
  are equal.**

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CommRingCat

universe u

namespace AlgebraicGeometry

/-- **The order of a differential operator on the sections over a smaller open, read over a larger
one.** An operator of order at most `k` on `X/Z` defined over the opens of `U₀`, evaluated on the
sections over an open `V ⊆ U₀`, is a differential operator of order at most `k` relative to the
sections of the structure sheaf over any open `U` containing `V`, acting by restriction of
scalars. -/
theorem order_section_of_isDiffOpOfOrder {X Z : Scheme.{u}} (p : X ⟶ Z) {M M' : X.Modules}
    {U₀ : X.Opens} {k : ℕ} (D : DiffOp.RawOp M M' U₀)
    (hD : DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D) {V U : X.Opens}
    (i₀ : V ⟶ U₀) (i : V ⟶ U)
    (P : Γ(M, V) →ₗ[ℤ] Γ(M', V)) (hP : ∀ x, P x = D (Over.mk i₀) x) :
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
    letI : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
    letI : Module Γ(X, U) Γ(M', V) := Module.compHom _ (X.presheaf.map i.op).hom
    P.IsDifferentialOperatorOfOrderLE Γ(X, U) k := by
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map i.op).hom.toAlgebra
  let : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
  let : Module Γ(X, U) Γ(M', V) := Module.compHom _ (X.presheaf.map i.op).hom
  have : IsScalarTower Γ(X, U) Γ(X, V) Γ(M, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(X, U) Γ(X, V) Γ(M', V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine AffineDiffOp.order_restrict (T := Γ(X, V)) ?_
  obtain rfl : P = (D (Over.mk i₀)).toIntLinearMap := LinearMap.ext hP
  exact AffineDiffOp.rawOrder_section p.relativeStructureSheafMap D hD (Over.mk i₀)

/-- **Restriction to an open equal to a principal open is a localization.** On a quasi-compact,
quasi-separated open `U`, restriction of the sections of a quasi-coherent module to an open `V`
which is the principal open of `s : Γ(X, U)` realizes them as the localization away from `s`. -/
theorem isLocalizedModule_restriction_of_eq_basicOpen {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (s : Γ(X, U)) {V : X.Opens} (hV : X.basicOpen s = V) (i : V ⟶ U) :
    letI : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
    IsLocalizedModule.Away s (Scheme.Modules.restrictionLinearMap M i) := by
  subst hV
  obtain rfl := Subsingleton.elim i (homOfLE (X.basicOpen_le s))
  exact isLocalizedModule_restriction_basicOpen_of_qcqs M hU hU' s

/-- **Multiplication by a power of a section is injective on the sections over an open equal to its
principal open.** -/
theorem injective_smul_powers_of_eq_basicOpen {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (f : Γ(X, U)) {V : X.Opens} (hV : X.basicOpen f = V) (i : V ⟶ U)
    (r : Submonoid.powers f) :
    letI : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
    Function.Injective fun x : Γ(M, V) ↦ (r : Γ(X, U)) • x := by
  subst hV
  obtain rfl := Subsingleton.elim i (homOfLE (X.basicOpen_le f))
  exact injective_smul_powers_basicOpen M f r

end AlgebraicGeometry

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **Two differential operators on a chart refining another chart in a principal open which agree
after restriction are equal.** Let `c` and `e` be charts of `X ×_S Y` with the range of `e` the
principal open of a section `s` over the range of `c`. Two differential operators of order at most
`k` on `X ×_S Y / Y` defined over the opens of `e` which agree on the sections of a quasi-coherent
module restricted from the range of `c` are equal. -/
theorem rawOp_ext_of_restriction (c e : Chart a b) (s : Γ(pullback a b, c.ι.opensRange))
    (hle : e.ι.opensRange ≤ c.ι.opensRange)
    (he : (pullback a b).basicOpen s = e.ι.opensRange)
    (M M' : (pullback a b).Modules) [M.IsQuasicoherent] (k : ℕ)
    (P Q : {D : DiffOp.RawOp M M' e.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D})
    (hres : ∀ x : Γ(M, c.ι.opensRange),
      P.1 (Over.mk (𝟙 _)) (M.presheaf.map (homOfLE hle).op x) =
        Q.1 (Over.mk (𝟙 _)) (M.presheaf.map (homOfLE hle).op x)) :
    P.1 = Q.1 := by
  let : Algebra Γ(pullback a b, c.ι.opensRange) Γ(pullback a b, e.ι.opensRange) :=
    ((pullback a b).presheaf.map (homOfLE hle).op).hom.toAlgebra
  let : Module Γ(pullback a b, c.ι.opensRange) Γ(M, e.ι.opensRange) :=
    Module.compHom _ ((pullback a b).presheaf.map (homOfLE hle).op).hom
  let : Module Γ(pullback a b, c.ι.opensRange) Γ(M', e.ι.opensRange) :=
    Module.compHom _ ((pullback a b).presheaf.map (homOfLE hle).op).hom
  have : IsLocalizedModule.Away s
      (Scheme.Modules.restrictionLinearMap M (homOfLE hle)) :=
    isLocalizedModule_restriction_of_eq_basicOpen M
      c.isAffineOpen_opensRange_ι.isCompact c.isAffineOpen_opensRange_ι.isQuasiSeparated
      s he (homOfLE hle)
  have key : (P.1 (Over.mk (𝟙 _))).toIntLinearMap = (Q.1 (Over.mk (𝟙 _))).toIntLinearMap :=
    AffineDiffOp.order_ext_localized (Submonoid.powers s)
      (Scheme.Modules.restrictionLinearMap M (homOfLE hle))
      (fun r ↦ injective_smul_powers_of_eq_basicOpen M' s he (homOfLE hle) r)
      (order_section_of_isDiffOpOfOrder (pullback.snd a b) P.1 P.2 (𝟙 _) (homOfLE hle) _
        fun _ ↦ rfl)
      (order_section_of_isDiffOpOfOrder (pullback.snd a b) Q.1 Q.2 (𝟙 _) (homOfLE hle) _
        fun _ ↦ rfl)
      hres
  have gen : ∀ (T : Over e.ι.opensRange),
      T.left = e.ι.opensRange → ∀ x, P.1 T x = Q.1 T x := by
    rintro ⟨W, ⟨⟩, j⟩ hW x
    subst hW
    obtain rfl : j = 𝟙 _ := Subsingleton.elim _ _
    exact LinearMap.congr_fun key x
  let := e.algebraLeft
  let := e.algebraRight
  have himg : ((e.specIso (Chart.ofHom_algebraMap_left e)
      (Chart.ofHom_algebraMap_right e)).inv ≫ e.ι) ''ᵁ ⊤ = e.ι.opensRange := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso]
  exact Chart.rawOp_ext_of_chart_sections e (Chart.ofHom_algebraMap_left e)
    (Chart.ofHom_algebraMap_right e) M M' k P Q himg.le
    (gen (Over.mk (homOfLE himg.le)) himg)

end Chart

end Stacks.FibreProductAffineChart

end
