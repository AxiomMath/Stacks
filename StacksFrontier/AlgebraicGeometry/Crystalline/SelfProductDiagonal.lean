module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SheafComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiComparison

/-!
# The diagonal of a self-product in the crystalline category

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `(U, T, δ)` of the big
crystalline category `CRIS(X/S)`.  Suppose `(U(1), T(1), δ(1))` is a product of `(U, T, δ)` with
itself, presented by a limit binary fan with projections `p₀, p₁`.  The *diagonal* is the morphism
`(U, T, δ) ⟶ (U(1), T(1), δ(1))` determined by the two identities, and `Δ : T ⟶ T(1)` is its
ambient component.  On an open `W` of `T(1)` the *diagonal ideal* `K` is the kernel of `Δ` on
sections.

The product is supplied as limit data, `IsLimit (BinaryFan.mk p₀ p₁)`.  When `U ⟶ X` is an
open immersion, so that `(U, T, δ)` lies in the small crystalline site `Cris(X/S)`, the thickened
schemes of the two objects agree, `U(1) = U`, and the diagonal ideal is contained in the divided
power ideal `J_{T(1)}`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.selfProductDiagonal` — the diagonal
  `(U, T, δ) ⟶ (U(1), T(1), δ(1))` of a self-product presented by a limit binary fan.
* `Crystalline.GlobalCrystallineSituation.selfProductAmbientDiagonal` — its ambient component
  `Δ : T ⟶ T(1)`, as a morphism of divided power schemes.
* `Crystalline.GlobalCrystallineSituation.selfProductDiagonalIdeal` — the diagonal ideal `K` on
  an open of `T(1)`, the kernel of `Δ` on sections.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDiagonal`,
  `smallSelfProductAmbientDiagonal` and `smallSelfProductDiagonalIdeal` — the same three for a
  self-product taken in the small crystalline site `Cris(X/S)` itself.

## Main results

* `Crystalline.GlobalCrystallineSituation.selfProductDiagonalIdeal_inf_isSubDPIdeal` — on every
  open of `T(1)`, the intersection of the diagonal ideal with the divided power ideal
  `J_{T(1)}` is stable under the divided powers of `J_{T(1)}`.
* `Crystalline.GlobalCrystallineSituation.sourceHom_eq_of_isOpenImmersion` — two morphisms into
  an object of the small crystalline site agree on thickened schemes.
* `Crystalline.GlobalCrystallineSituation.isIso_selfProductDiagonal_sourceHom` — for an object of
  the small crystalline site, the component of the diagonal on thickened schemes is an
  isomorphism: `U(1) = U`.
* `Crystalline.GlobalCrystallineSituation.selfProductDiagonalIdeal_le` — for an object of the
  small crystalline site, the diagonal ideal is contained in the divided power ideal of `T(1)`
  on every open.
* `Crystalline.GlobalCrystallineSituation.selfProductDiagonalIdeal_isSubDPIdeal` — for an object
  of the small crystalline site, the diagonal ideal is itself stable under the divided powers of
  `J_{T(1)}` on every open.
* `Crystalline.GlobalCrystallineSituation.isOpenImmersion_selfProduct_toX` — the self-product in
  `CRIS(X/S)` of an object of `Cris(X/S)` is again an object of `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.ZariskiOpen.hom_ext` — the small Zariski site of `X` has
  at most one morphism between any two objects.
* `Crystalline.GlobalCrystallineSituation.isIso_smallSelfProductDiagonal_sourceHom` — `U(1) = U`
  for a self-product taken in `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDiagonalIdeal_le` and
  `smallSelfProductDiagonalIdeal_isSubDPIdeal` — for a self-product taken in `Cris(X/S)` the
  diagonal ideal is contained in `J_{T(1)}` and is preserved by the divided structure on
  `J_{T(1)}` (the first assertion of [Stacks, Tag 07J1]).

## References

* [Stacks Project, Tag 07J1](https://stacks.math.columbia.edu/tag/07J1)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07II](https://stacks.math.columbia.edu/tag/07II)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {A P : Thickening S} {p₀ p₁ : P ⟶ A}

section Diagonal

/-- The diagonal of a self-product in `CRIS(X/S)`: for a limit binary fan presenting
`(U(1), T(1), δ(1))` as a product of `(U, T, δ)` with itself, the morphism
`(U, T, δ) ⟶ (U(1), T(1), δ(1))` whose composites with the two projections are the identity. -/
def selfProductDiagonal (h : IsLimit (BinaryFan.mk p₀ p₁)) : A ⟶ P :=
  (BinaryFan.IsLimit.lift' h (𝟙 A) (𝟙 A)).1

/-- The diagonal followed by the first projection is the identity. -/
@[simp]
theorem selfProductDiagonal_fst (h : IsLimit (BinaryFan.mk p₀ p₁)) :
    selfProductDiagonal h ≫ p₀ = 𝟙 A :=
  (BinaryFan.IsLimit.lift' h (𝟙 A) (𝟙 A)).2.1

/-- The diagonal followed by the second projection is the identity. -/
@[simp]
theorem selfProductDiagonal_snd (h : IsLimit (BinaryFan.mk p₀ p₁)) :
    selfProductDiagonal h ≫ p₁ = 𝟙 A :=
  (BinaryFan.IsLimit.lift' h (𝟙 A) (𝟙 A)).2.2

/-- The ambient component `Δ : T ⟶ T(1)` of the diagonal of a self-product, as a morphism of
divided power schemes. -/
abbrev selfProductAmbientDiagonal (h : IsLimit (BinaryFan.mk p₀ p₁)) :
    A.thickening.target ⟶ P.thickening.target :=
  (selfProductDiagonal h).targetHom

/-- The diagonal ideal `K` on an open of `T(1)`: the kernel of `Δ` on sections. -/
abbrev selfProductDiagonalIdeal (h : IsLimit (BinaryFan.mk p₀ p₁))
    (W : P.thickening.target.scheme.Opens) : Ideal Γ(P.thickening.target.scheme, W) :=
  RingHom.ker ((selfProductAmbientDiagonal h).hom.app W).hom

/-- The kernel of a morphism of thickenings on sections, intersected with the divided power ideal
of the target, is stable under the divided powers of the target. -/
private theorem ker_inf_ideal_isSubDPIdeal (f : A ⟶ P) (W : P.thickening.target.scheme.Opens) :
    (P.thickening.target.dividedPowers.dividedPowers (op W)).IsSubDPIdeal
      (RingHom.ker (f.targetHom.hom.app W).hom ⊓ P.thickening.target.ideal.obj (op W)) :=
  DividedPowers.isSubDPIdeal_ker _
    (A.thickening.target.dividedPowers.dividedPowers (op (f.targetHom.hom ⁻¹ᵁ W)))
    (f.targetHom.compatible W)

/-- **The intersection of the diagonal ideal with the divided power ideal of `T(1)` is stable
under the divided powers of `T(1)`**, on every open of `T(1)`. -/
theorem selfProductDiagonalIdeal_inf_isSubDPIdeal (h : IsLimit (BinaryFan.mk p₀ p₁))
    (W : P.thickening.target.scheme.Opens) :
    (P.thickening.target.dividedPowers.dividedPowers (op W)).IsSubDPIdeal
      (selfProductDiagonalIdeal h W ⊓ P.thickening.target.ideal.obj (op W)) :=
  ker_inf_ideal_isSubDPIdeal _ W

end Diagonal

section SmallSite

/-- **Two morphisms into an object of the small crystalline site agree on thickened
schemes.** -/
theorem sourceHom_eq_of_isOpenImmersion [IsOpenImmersion A.toX] (f g : P ⟶ A) :
    f.sourceHom = g.sourceHom :=
  (cancel_mono A.toX).1 (f.toX_naturality.trans g.toX_naturality.symm)

/-- Two morphisms into an object of the small crystalline site become equal in `Sch/X`. -/
theorem forget_map_eq_of_isOpenImmersion [IsOpenImmersion A.toX] (f g : P ⟶ A) :
    (forget S).map f = (forget S).map g :=
  Over.OverMorphism.ext (sourceHom_eq_of_isOpenImmersion f g)

/-- The component of the diagonal on thickened schemes is split by either projection. -/
theorem selfProductDiagonal_sourceHom_comp (h : IsLimit (BinaryFan.mk p₀ p₁)) :
    (selfProductDiagonal h).sourceHom ≫ p₀.sourceHom = 𝟙 _ :=
  congrArg Thickening.Hom.sourceHom (selfProductDiagonal_fst h)

/-- Either projection is split by the component of the diagonal on thickened schemes, for an
object of the small crystalline site. -/
theorem selfProductDiagonal_comp_sourceHom [IsOpenImmersion A.toX]
    (h : IsLimit (BinaryFan.mk p₀ p₁)) :
    p₀.sourceHom ≫ (selfProductDiagonal h).sourceHom = 𝟙 _ := by
  have hL := isLimitOfPreserves (forget S) h
  have key : (forget S).map (p₀ ≫ selfProductDiagonal h) = (forget S).map (𝟙 P) := by
    refine hL.hom_ext ?_
    rintro ⟨j⟩
    cases j
    · show (forget S).map (p₀ ≫ selfProductDiagonal h) ≫ (forget S).map p₀ = _
      rw [← Functor.map_comp, Category.assoc, selfProductDiagonal_fst, Category.comp_id]
      show _ = (forget S).map (𝟙 P) ≫ (forget S).map p₀
      rw [← Functor.map_comp, Category.id_comp]
    · show (forget S).map (p₀ ≫ selfProductDiagonal h) ≫ (forget S).map p₁ = _
      rw [← Functor.map_comp, Category.assoc, selfProductDiagonal_snd, Category.comp_id]
      show _ = (forget S).map (𝟙 P) ≫ (forget S).map p₁
      rw [← Functor.map_comp, Category.id_comp]
      exact forget_map_eq_of_isOpenImmersion p₀ p₁
  simpa using congrArg (fun k => k.left) key

/-- **`U(1) = U` for an object of the small crystalline site**: the component of the diagonal of
a self-product on thickened schemes is an isomorphism. -/
theorem isIso_selfProductDiagonal_sourceHom [IsOpenImmersion A.toX]
    (h : IsLimit (BinaryFan.mk p₀ p₁)) : IsIso (selfProductDiagonal h).sourceHom :=
  ⟨p₀.sourceHom, selfProductDiagonal_sourceHom_comp h,
    selfProductDiagonal_comp_sourceHom h⟩

/-- A composite of homomorphisms of commutative rings kills a section the first one kills. -/
private theorem commRingComp_apply_eq_zero {R₁ R₂ R₃ : CommRingCat.{u}} (f : R₁ ⟶ R₂)
    (g : R₂ ⟶ R₃) (x : R₁) (hx : f.hom x = 0) : (f ≫ g).hom x = 0 := by
  rw [CommRingCat.hom_comp, RingHom.comp_apply, hx, map_zero]

/-- The kernel on sections of a morphism of thickenings that is an isomorphism on thickened
schemes lies in the divided power ideal of the target. -/
private theorem ker_le_ideal_of_isIso_sourceHom (f : A ⟶ P) [IsIso f.sourceHom]
    (W : P.thickening.target.scheme.Opens) :
    RingHom.ker (f.targetHom.hom.app W).hom ≤ P.thickening.target.ideal.obj (op W) := by
  intro s hs
  have hP : inv f.sourceHom ≫ (A.thickening.immersion ≫ f.targetHom.hom)
      = P.thickening.immersion := by
    rw [f.immersion_naturality, IsIso.inv_hom_id_assoc]
  refine (Crystalline.SchemeThickening.mem_ideal_iff_app_eq_zero P.thickening W s).mpr ?_
  rw [← hP]
  have hz : (f.targetHom.hom.app W).hom s = 0 := RingHom.mem_ker.mp hs
  simp only [Scheme.Hom.comp_app]
  exact commRingComp_apply_eq_zero _ _ _ (commRingComp_apply_eq_zero _ _ _ hz)

/-- The kernel on sections of a morphism of thickenings that is an isomorphism on thickened
schemes is stable under the divided powers of the target. -/
private theorem ker_isSubDPIdeal_of_isIso_sourceHom (f : A ⟶ P) [IsIso f.sourceHom]
    (W : P.thickening.target.scheme.Opens) :
    (P.thickening.target.dividedPowers.dividedPowers (op W)).IsSubDPIdeal
      (RingHom.ker (f.targetHom.hom.app W).hom) := by
  have hle := inf_eq_left.mpr (ker_le_ideal_of_isIso_sourceHom f W)
  exact hle ▸ ker_inf_ideal_isSubDPIdeal f W

/-- **The diagonal ideal is contained in the divided power ideal of `T(1)`, for an object of the
small crystalline site.** -/
theorem selfProductDiagonalIdeal_le [IsOpenImmersion A.toX] (h : IsLimit (BinaryFan.mk p₀ p₁))
    (W : P.thickening.target.scheme.Opens) :
    selfProductDiagonalIdeal h W ≤ P.thickening.target.ideal.obj (op W) :=
  have := isIso_selfProductDiagonal_sourceHom h
  ker_le_ideal_of_isIso_sourceHom _ W

/-- **The diagonal ideal is stable under the divided powers of `T(1)`, for an object of the small
crystalline site.** -/
theorem selfProductDiagonalIdeal_isSubDPIdeal [IsOpenImmersion A.toX]
    (h : IsLimit (BinaryFan.mk p₀ p₁)) (W : P.thickening.target.scheme.Opens) :
    (P.thickening.target.dividedPowers.dividedPowers (op W)).IsSubDPIdeal
      (selfProductDiagonalIdeal h W) :=
  have := isIso_selfProductDiagonal_sourceHom h
  ker_isSubDPIdeal_of_isIso_sourceHom _ W

/-- **The self-product in `CRIS(X/S)` of an object of the small crystalline site is again an
object of the small crystalline site.** -/
theorem isOpenImmersion_selfProduct_toX [IsOpenImmersion A.toX]
    (h : IsLimit (BinaryFan.mk p₀ p₁)) : IsOpenImmersion P.toX := by
  have := isIso_selfProductDiagonal_sourceHom h
  have hP : inv (selfProductDiagonal h).sourceHom ≫ A.toX = P.toX := by
    rw [← (selfProductDiagonal h).toX_naturality, IsIso.inv_hom_id_assoc]
  exact hP ▸ inferInstance

end SmallSite

section SmallSiteProduct

variable {B D : CrystallineThickening S} {pr₀ pr₁ : D ⟶ B}

/-- **The small Zariski site of `X` has at most one morphism between any two objects.** -/
theorem ZariskiOpen.hom_ext {Y Z : ZariskiOpen S} (f g : Y ⟶ Z) : f = g := by
  have : IsOpenImmersion Z.hom := Z.prop
  exact MorphismProperty.Over.Hom.ext
    ((cancel_mono Z.hom).1 ((MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm))

/-- The diagonal of a self-product in the small crystalline site `Cris(X/S)`: for a limit binary
fan presenting `(U(1), T(1), δ(1))` as a product of `(U, T, δ)` with itself, the morphism
`(U, T, δ) ⟶ (U(1), T(1), δ(1))` whose composites with the two projections are the identity. -/
def smallSelfProductDiagonal (h : IsLimit (BinaryFan.mk pr₀ pr₁)) : B ⟶ D :=
  (BinaryFan.IsLimit.lift' h (𝟙 B) (𝟙 B)).1

/-- The diagonal followed by the first projection is the identity, in `Cris(X/S)`. -/
@[simp]
theorem smallSelfProductDiagonal_fst (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    smallSelfProductDiagonal h ≫ pr₀ = 𝟙 B :=
  (BinaryFan.IsLimit.lift' h (𝟙 B) (𝟙 B)).2.1

/-- The diagonal followed by the second projection is the identity, in `Cris(X/S)`. -/
@[simp]
theorem smallSelfProductDiagonal_snd (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    smallSelfProductDiagonal h ≫ pr₁ = 𝟙 B :=
  (BinaryFan.IsLimit.lift' h (𝟙 B) (𝟙 B)).2.2

/-- **`U(1) = U` for a self-product taken in the small crystalline site**: the component of the
diagonal on thickened schemes is an isomorphism. -/
theorem isIso_smallSelfProductDiagonal_sourceHom (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    IsIso (smallSelfProductDiagonal h).hom.sourceHom := by
  have := (smallFreeForgetAdjunction S).rightAdjoint_preservesLimits
  have hF := mapIsLimitOfPreservesOfIsLimit (smallForget S) pr₀ pr₁ h
  have hpr : (smallForget S).map pr₀ = (smallForget S).map pr₁ := ZariskiOpen.hom_ext _ _
  have hback : (smallForget S).map (smallSelfProductDiagonal h) ≫ (smallForget S).map pr₀
      = 𝟙 _ := by
    rw [← Functor.map_comp, smallSelfProductDiagonal_fst]
    exact (smallForget S).map_id B
  have hforth : (smallForget S).map pr₀ ≫ (smallForget S).map (smallSelfProductDiagonal h)
      = 𝟙 _ := by
    refine BinaryFan.IsLimit.hom_ext hF ?_ ?_
    · rw [BinaryFan.mk_fst, Category.assoc, hback, Category.comp_id, Category.id_comp]
    · rw [BinaryFan.mk_snd, Category.assoc, ← Functor.map_comp, smallSelfProductDiagonal_snd,
        (smallForget S).map_id, Category.comp_id, Category.id_comp]
      exact hpr
  have : IsIso ((smallForget S).map (smallSelfProductDiagonal h)) := ⟨_, hback, hforth⟩
  exact inferInstanceAs (IsIso ((ZariskiOpen.ι S ⋙ CategoryTheory.Over.forget S.X).map
    ((smallForget S).map (smallSelfProductDiagonal h))))

/-- The ambient component `Δ : T ⟶ T(1)` of the diagonal of a self-product taken in the small
crystalline site, as a morphism of divided power schemes. -/
abbrev smallSelfProductAmbientDiagonal (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    B.obj.thickening.target ⟶ D.obj.thickening.target :=
  (smallSelfProductDiagonal h).hom.targetHom

/-- The diagonal ideal `K` on an open of `T(1)`, for a self-product taken in the small crystalline
site: the kernel of `Δ` on sections. -/
abbrev smallSelfProductDiagonalIdeal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.Opens) :
    Ideal Γ(D.obj.thickening.target.scheme, W) :=
  RingHom.ker ((smallSelfProductAmbientDiagonal h).hom.app W).hom

/-- For a self-product `(U(1), T(1), δ(1))` of an object `(U, T, δ)` of `Cris(X/S)` with itself,
the diagonal ideal `K` of `Δ : T ⟶ T(1)` is contained in the divided power ideal `J_{T(1)}` on
every open of `T(1)`. -/
@[stacks 07J1 "K ⊆ J_{T(1)}; sections over each open, K the kernel of Δ on sections"]
theorem smallSelfProductDiagonalIdeal_le (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.Opens) :
    smallSelfProductDiagonalIdeal h W ≤ D.obj.thickening.target.ideal.obj (op W) :=
  have := isIso_smallSelfProductDiagonal_sourceHom h
  ker_le_ideal_of_isIso_sourceHom _ W

/-- For a self-product `(U(1), T(1), δ(1))` of an object `(U, T, δ)` of `Cris(X/S)` with itself,
the diagonal ideal `K` of `Δ : T ⟶ T(1)` is preserved by the divided structure on `J_{T(1)}` on
every open of `T(1)`. -/
@[stacks 07J1 "K is preserved by the divided structure on J_{T(1)}; sections over each open"]
theorem smallSelfProductDiagonalIdeal_isSubDPIdeal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.Opens) :
    (D.obj.thickening.target.dividedPowers.dividedPowers (op W)).IsSubDPIdeal
      (smallSelfProductDiagonalIdeal h W) :=
  have := isIso_smallSelfProductDiagonal_sourceHom h
  ker_isSubDPIdeal_of_isIso_sourceHom _ W

end SmallSiteProduct

end Crystalline.GlobalCrystallineSituation

end
