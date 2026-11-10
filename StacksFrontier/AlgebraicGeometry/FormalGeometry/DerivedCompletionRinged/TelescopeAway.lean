module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimit
public import StacksFrontier.CategoryTheory.Abelian.Telescope
public import StacksCore.Tactic.StacksAttribute

/-!
# The telescope resolution of a localization of the structure sheaf

Let `(𝒞, 𝒪)` be a ringed site and `f` a global section of `𝒪`. This file resolves `𝒪_f` by free
sheaves of `𝒪`-modules:

`0 ⟶ ⊕_{n ∈ ℕ} 𝒪 ⟶ ⊕_{n ∈ ℕ} 𝒪 ⟶ 𝒪_f ⟶ 0`,

the first map being `1 - f·shift`, that is `e_n ↦ e_n - f e_{n+1}`, and the second sending `e_n`
to `f^{-n}`.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayTelescopeSum`: the coproduct `⊕_{n ∈ ℕ} 𝒪`.
* `AlgebraicGeometry.RingedSite.awayTelescopeSumMap`: the map `1 - f·shift`.
* `AlgebraicGeometry.RingedSite.awayTelescopeAugmentation`: the map `e_n ↦ f^{-n}` onto `𝒪_f`.
* `AlgebraicGeometry.RingedSite.colimitIsoAwayModule`: `𝒪_f` as the colimit of
  `𝒪 --f--> 𝒪 --f--> ⋯`, read out of the chosen colimit of that diagram.

## Main results

* `AlgebraicGeometry.RingedSite.awayTelescopeShortExact`: the sequence above is short exact.

## Implementation notes

`𝒪_f` is a sheafification, so nothing is checked on sections. The sequence is the mapping
telescope `Stacks.MappingTelescope.telescope_shortExact_general` of the sequential diagram
`𝒪 --f--> 𝒪 --f--> ⋯` of `AlgebraicGeometry.RingedSite.awaySequence`, whose colimit is `𝒪_f` by
`AlgebraicGeometry.RingedSite.isColimitAwayModuleCocone`; the third term is transported along
that identification, which carries the `n`-th colimit inclusion to
`AlgebraicGeometry.RingedSite.awayModuleCoconeι`, the canonical map divided by `f^n`. The
hypotheses of the telescope sequence are countable coproducts and exactness of colimits over `ℕ`,
and the latter is `AlgebraicGeometry.RingedSite.hasExactColimitsOfShape_nat_ringSheaf`: the
sheaves of `𝒪`-modules are Grothendieck abelian.

The telescope map is *defined* by the expression the telescope sequence uses, with the transition
map of the diagram rather than `a` itself, so that the sequence proved short exact is literally
the one `Stacks.MappingTelescope.telescope_shortExact_general` provides.

The diagram is taken with respect to an arbitrary endomorphism `a` of `𝒪` acting sectionwise by
multiplication by `f`, which `ha` determines uniquely. At `a = awaySmulUnit X h` the map
`awayTelescopeSumMap` is the map `AlgebraicGeometry.RingedSite.awayTelescopeMap`.

A free resolution of `𝒪_f` is used implicitly in [Stacks, Tag 0997] but not stated there.

## References

* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

open scoped IsMulCommutative


variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (a : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The coproduct `⊕_{n ∈ ℕ} 𝒪` of countably many copies of the structure sheaf, formed as the
coproduct of the terms of the sequential diagram `𝒪 --f--> 𝒪 --f--> ⋯`. -/
abbrev awayTelescopeSum : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ∐ fun n : ℕ => (awaySequence X a).obj n

/-- **The telescope map `1 - f·shift`** of `⊕_{n ∈ ℕ} 𝒪`, that is `e_n ↦ e_n - f e_{n+1}`. -/
def awayTelescopeSumMap : awayTelescopeSum X a ⟶ awayTelescopeSum X a :=
  Sigma.desc fun n => Sigma.ι (fun n : ℕ => (awaySequence X a).obj n) n -
    (awaySequence X a).map (homOfLE n.le_succ) ≫
      Sigma.ι (fun n : ℕ => (awaySequence X a).obj n) (n + 1)

omit [HasWeakSheafify X.J CommRingCat] in
/-- The telescope map sends the `n`-th summand inclusion `e_n` to `e_n - f e_{n+1}`. -/
@[reassoc]
theorem awayTelescopeι_comp_awayTelescopeSumMap (n : ℕ) :
    Sigma.ι (fun n : ℕ => (awaySequence X a).obj n) n ≫ awayTelescopeSumMap X a =
      Sigma.ι (fun n : ℕ => (awaySequence X a).obj n) n -
        (awaySequence X a).map (homOfLE n.le_succ) ≫
          Sigma.ι (fun n : ℕ => (awaySequence X a).obj n) (n + 1) :=
  Sigma.ι_comp_desc _ n

/-- **The augmentation `⊕_{n ∈ ℕ} 𝒪 ⟶ 𝒪_f`**, sending `e_n` to the canonical map `𝒪 ⟶ 𝒪_f`
divided by `f^n`. -/
def awayTelescopeAugmentation : awayTelescopeSum X a ⟶ awayModule X h :=
  Sigma.desc fun n => awayModuleCoconeι X h n

/-- The augmentation sends the `n`-th summand inclusion to the canonical map `𝒪 ⟶ 𝒪_f` divided
by `f^n`. -/
@[reassoc]
theorem awayTelescopeι_comp_awayTelescopeAugmentation (n : ℕ) :
    Sigma.ι (fun n : ℕ => (awaySequence X a).obj n) n ≫ awayTelescopeAugmentation X h a =
      awayModuleCoconeι X h n :=
  Sigma.ι_comp_desc _ n

variable (ha : ∀ (U : X.Cᵒᵖ)
    (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj U),
  (a.val.app U).hom x = globalSectionVal h U • x)

include ha

/-- **`𝒪_f` is the colimit of `𝒪 --f--> 𝒪 --f--> ⋯`**, read as an isomorphism out of the chosen
colimit of that diagram. -/
def colimitIsoAwayModule : colimit (awaySequence X a) ≅ awayModule X h :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (awaySequence X a))
    (isColimitAwayModuleCocone X h a ha)

/-- The isomorphism `colimitIsoAwayModule` carries the `n`-th colimit inclusion to the canonical
map `𝒪 ⟶ 𝒪_f` divided by `f^n`. -/
@[reassoc]
theorem colimit_ι_comp_colimitIsoAwayModule (n : ℕ) :
    colimit.ι (awaySequence X a) n ≫ (colimitIsoAwayModule X h a ha).hom =
      awayModuleCoconeι X h n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (awaySequence X a))
    (isColimitAwayModuleCocone X h a ha) n

/-- The telescope map followed by the augmentation is zero: dividing `f e_{n+1}` by `f^{n+1}`
gives the same thing as dividing `e_n` by `f^n`. -/
theorem awayTelescopeSumMap_comp_awayTelescopeAugmentation :
    awayTelescopeSumMap X a ≫ awayTelescopeAugmentation X h a = 0 := by
  refine Sigma.hom_ext _ _ fun n => ?_
  rw [comp_zero, awayTelescopeι_comp_awayTelescopeSumMap_assoc, Preadditive.sub_comp,
    awayTelescopeι_comp_awayTelescopeAugmentation, Category.assoc,
    awayTelescopeι_comp_awayTelescopeAugmentation, awaySequence_map_succ]
  exact sub_eq_zero.mpr (comp_awayModuleCoconeι_succ X h a ha n).symm

/-- **The telescope resolution of `𝒪_f`.** The sequence

`0 ⟶ ⊕_{n ∈ ℕ} 𝒪 --1 - f·shift--> ⊕_{n ∈ ℕ} 𝒪 ⟶ 𝒪_f ⟶ 0`

of sheaves of `𝒪`-modules is short exact. It is the mapping telescope of the sequential diagram
`𝒪 --f--> 𝒪 --f--> ⋯`, whose colimit is `𝒪_f`. -/
theorem awayTelescopeShortExact :
    (ShortComplex.mk (awayTelescopeSumMap X a) (awayTelescopeAugmentation X h a)
      (awayTelescopeSumMap_comp_awayTelescopeAugmentation X h a ha)).ShortExact := by
  have hz := Stacks.MappingTelescope.telescope_general_hz (awaySequence X a)
  refine ShortComplex.shortExact_of_iso ?_
    (Stacks.MappingTelescope.telescope_shortExact_general (awaySequence X a) hz)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (colimitIsoAwayModule X h a ha) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [awayTelescopeι_comp_awayTelescopeAugmentation, Sigma.ι_comp_desc_assoc,
      colimit_ι_comp_colimitIsoAwayModule]

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The telescope resolution of `𝒪_f`, read as a short exact sequence of cochain complexes
concentrated in degree zero. Placing an object in a single degree preserves finite limits and
colimits, so it preserves short exactness. -/
theorem awayTelescopeShortExact_single :
    ((ShortComplex.mk (awayTelescopeSumMap X a) (awayTelescopeAugmentation X h a)
        (awayTelescopeSumMap_comp_awayTelescopeAugmentation X h a ha)).map
      (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0)).ShortExact :=
  (awayTelescopeShortExact X h a ha).map_of_exact _

/-- **The distinguished triangle of the telescope resolution of `𝒪_f`**:

`⊕_ℕ 𝒪 ⟶ ⊕_ℕ 𝒪 ⟶ 𝒪_f ⟶ (⊕_ℕ 𝒪)⟦1⟧`

in `D(𝒪)`, the first map being `1 - f·shift`. -/
theorem awayTelescopeTriangle_distinguished :
    DerivedCategory.triangleOfSES (awayTelescopeShortExact_single X h a ha) ∈
      distTriang
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  DerivedCategory.triangleOfSES_distinguished _

/-- **`R𝑆heafHom_𝒪(𝒪_f, K)` vanishes exactly when the telescope map induces an isomorphism on
`R𝑆heafHom_𝒪(⊕_ℕ 𝒪, K)`.**

This is the vanishing criterion of [Stacks, Tag 0997] reduced to the identification of that
induced endomorphism with the Milnor difference map `1 - f·shift` of `∏_ℕ K`: derived internal
Hom into `K` carries the triangle of the telescope resolution to a distinguished triangle whose
first vertex is `R𝑆heafHom_𝒪(𝒪_f, K)`, and in a distinguished triangle the first vertex is zero
exactly when the second morphism is invertible. -/
theorem isZero_derivedSheafHom_derivedAwayModule_iff_isIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsZero (((derivedSheafHomBifunctor X).obj (op (derivedAwayModule X h))).obj K) ↔
      IsIso (((derivedSheafHomBifunctor X).flip.obj K).map
        (DerivedCategory.Q.map ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map (awayTelescopeSumMap X a))).op) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X K _
    (awayTelescopeTriangle_distinguished X h a ha)
  exact Triangle.isZero₁_iff_isIso₂ _ hδ

end Derived

end AlgebraicGeometry.RingedSite

end
