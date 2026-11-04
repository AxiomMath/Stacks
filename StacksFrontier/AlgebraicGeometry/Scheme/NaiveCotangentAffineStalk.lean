module

public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalk

/-!
# The stalks of the naive cotangent complex at a point of an affine open

Let `f : X ⟶ Y` be a morphism of schemes, let `Spec R = U ⊆ Y` and `Spec A = V ⊆ X` be affine
opens with `f(V) ⊆ U`, and let `x ∈ V`.  Write `𝔭 ⊆ A` for the prime of `A` corresponding to
`x` and `𝔮 = 𝔭 ∩ R` for the prime of `R` it contracts to.  This file identifies the two rings
whose naive cotangent complex is the stalk at `x` of `NL_{X/Y}`, and deduces that the
comparison out of the base changed ring-level complex is a quasi-isomorphism:

`NL_{A/R} ⊗_A 𝒪_{X,x} ⟶ NL_{𝒪_{X,x} / (f^{-1}𝒪_Y)_x}`.

The stalk `𝒪_{X,x}` is the localization `A_𝔭` and the stalk `(f^{-1}𝒪_Y)_x` is the localization
`R_𝔮`, so this is the stalkwise step of Stacks 0D0I at the geometric stalks, the right-hand side
being the stalk at `x` of `NL_{X/Y}` by Modules, Lemma 0D09.

## Main results

* `Stacks.NaiveCotangentAffineStalk.germ_comp_appLE`: the germ at `x` of the restriction
  `Γ(Y, U) ⟶ Γ(X, V)` of `f` is the germ at `f x` followed by the stalk map of `f`.  This is
  what makes the two towers `R → A → 𝒪_{X,x}` and `R → 𝒪_{Y,f x} → 𝒪_{X,x}` agree.
* `Stacks.NaiveCotangentAffineStalk.inverseImageStructureMap_eq_ringedSpace` and
  `Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap_eq_algebraStalk`: the
  structural map `f^{-1}𝒪_Y ⟶ 𝒪_X` used here is the one whose naive cotangent complex
  `NL_{X/Y}` is, and the algebra structure its stalk gives is the one Stacks 0D09 is stated
  over.  Both hold by `rfl`; stating them is what makes the composition with Stacks 0D09
  machine-checked rather than asserted in prose.
* `Stacks.NaiveCotangentAffineStalk.isLocalization_stalkInverseImage`: the stalk
  `(f^{-1}𝒪_Y)_x` of the inverse image of the structure sheaf of `Y` is the localization
  `R_𝔮`, for `𝔮` the prime of `R = Γ(Y, U)` corresponding to `f x`.  This is Sheaves, Lemma
  008H for the sheaf of rings `𝒪_Y` together with Schemes, Lemma 01HV.
* `Stacks.NaiveCotangentAffineStalk.comap_primeIdealOf`: `𝔮 = 𝔭 ∩ R`, in the spelling
  `Ideal.comap (algebraMap R A) 𝔭`, which is the hypothesis shape of the ring-level statement.
* `Stacks.NaiveCotangentAffineStalk.isQuasiIso_nlExtensionBaseChangeMap_stalk`: the canonical
  map `NL_{A/R} ⊗_A 𝒪_{X,x} ⟶ NL_{𝒪_{X,x}/𝒪_{Y,f x}}` is a quasi-isomorphism.
* `Stacks.NaiveCotangentAffineStalk.isQuasiIso_nlExtensionBaseChangeMap_stalkInverseImage`: the
  same with the base ring `(f^{-1}𝒪_Y)_x`, which is the ring that
  `Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk` (Stacks 0D09) takes
  the stalk of `NL_{X/Y}` to be the naive cotangent complex over.

## Implementation notes

**The role in Stacks 0D0I.**  Tag 0D0I asserts that there is a canonical map of complexes
`(NL_{A/R})~ ⟶ NL_{X/Y}|_U` and that it is an isomorphism in `D(𝒪_U)`.  The result here is the
input the source's proof uses at the very end, at the *geometric* stalks: the stalk of `𝒪_X` at
`x` is `A_𝔭`, the stalk of `f^{-1}𝒪_Y` at `x` is `R_𝔮` with `𝔮 = 𝔭 ∩ R`, and over those two rings
the base changed ring-level comparison is a quasi-isomorphism.

The algebra structures are supplied as `letI`s in the statements, in the style of
`Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk`, because none of them
is found by instance search: `Γ(X, V)` is an algebra over `Γ(Y, U)` only through the chosen
restriction `f.appLE`, and the two stalks are algebras over the sections only through the germ
maps.  They are named rather than inlined so that the same ones can be introduced in the same
order in a statement and in its proof.  The two scalar towers are carried the same way, by
`haveI`s in the statements: `NaiveCotangent.nlExtensionBaseChangeMap` takes them as instance
arguments, so without them the statements do not even elaborate.  Instances bound by a `letI` in
a statement are not in scope for the elaboration of a proof *term* against that statement, which
is why every proof below is a tactic proof that reintroduces them.

The algebra structure of `Γ(Y, U)` on `𝒪_{X,x}` is *defined* as the composite through
`Γ(X, V)`, which makes the tower `Γ(Y, U) → Γ(X, V) → 𝒪_{X,x}` hold by `rfl`; the other tower,
`Γ(Y, U) → 𝒪_{Y,f x} → 𝒪_{X,x}`, is then the content of
`Stacks.NaiveCotangentAffineStalk.germ_comp_appLE`.  The variant with `(f^{-1}𝒪_Y)_x` in place
of `𝒪_{Y,f x}` goes through the same tower, the extra leg being
`Stacks.SheafifyStalk.stalkMap_hom_eq_comp`.

The membership `f x ∈ U` is carried as its own hypothesis rather than written `hVU hx`: the
latter has type `x ∈ f ⁻¹ᵁ U`, which is only definitionally the former, and a goal stating a
germ at a proof of the wrong one of the two is rejected as not type-correct under the implicit
transparency level.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV), the stalks of the
  structure sheaf of an affine scheme.
* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H), the stalks of an
  inverse image.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), quasi-isomorphy of a
  map of complexes of sheaves of modules is detected on stalks.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineStalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
  (hVU : V ≤ f ⁻¹ᵁ U) {x : X} (hx : x ∈ V) (hfx : f x ∈ U)

/-! ### The algebra structures -/

/-- `Γ(X, V)` as an algebra over `Γ(Y, U)`, through the restriction `f.appLE` of `f` to the two
opens.  This is the ring map `R → A` of Stacks 0D0I. -/
noncomputable abbrev algebraAppLE : Algebra Γ(Y, U) Γ(X, V) :=
  (f.appLE U V hVU).hom.toAlgebra

/-- `𝒪_{X,x}` as an algebra over `Γ(Y, U)`, through `Γ(X, V)`: the germ at `x` composed with
the restriction of `f`.  Defining it as this composite makes the scalar tower
`Γ(Y, U) → Γ(X, V) → 𝒪_{X,x}` hold by `rfl`. -/
noncomputable abbrev algebraStalkOfAppLE : Algebra Γ(Y, U) ↑(X.presheaf.stalk x) :=
  ((X.presheaf.germ V x hx).hom.comp (f.appLE U V hVU).hom).toAlgebra

/-- `𝒪_{X,x}` as an algebra over `𝒪_{Y,f x}`, through the stalk map of `f`. -/
noncomputable abbrev algebraStalkMap :
    Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

/-- `(f^{-1}𝒪_Y)_x` as an algebra over `Γ(Y, U)`: the germ at `f x` followed by the inverse of
the identification `(f^{-1}𝒪_Y)_x ≅ 𝒪_{Y,f x}`. -/
noncomputable abbrev algebraStalkInverseImage :
    Algebra Γ(Y, U)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
  ((SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv.hom.comp
    (Y.presheaf.germ U (f x) hfx).hom).toAlgebra

/-- `𝒪_{X,x}` as an algebra over `(f^{-1}𝒪_Y)_x`, through the stalk at `x` of the structural map
`f^{-1}𝒪_Y ⟶ 𝒪_X`.  This is the algebra structure that
`Stacks.RelativeDifferentialStalk.algebraStalk` gives at the structural map, and the one the
stalk statement of Stacks 0D09 is about. -/
noncomputable abbrev algebraStalkInverseImageStructureMap :
    Algebra ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
      ↑(X.presheaf.stalk x) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (AlgebraicGeometry.inverseImageStructureMap f).hom).hom.toAlgebra
/-- **The structural map used above is the one `NL_{X/Y}` is built from.**  The map
`f^{-1}𝒪_Y ⟶ 𝒪_X` of `AlgebraicGeometry.inverseImageStructureMap`, whose stalk at `x` carries the
algebra structure of
`Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap`, is the map
`Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap` of the underlying morphism of
ringed spaces of `f`, which is the morphism of sheaves of rings whose naive cotangent complex
`AlgebraicGeometry.Scheme.naiveCotangentComplex` is.  The two are the same adjoint of `f`'s
comorphism, so this holds by `rfl`; stating it records that the two sheaves and the two maps
really are the same, which is what lets the stalk statement of Stacks 0D09 be read as a
statement about the stalk of `NL_{X/Y}`. -/
theorem inverseImageStructureMap_eq_ringedSpace :
    AlgebraicGeometry.inverseImageStructureMap f =
      Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f.toLRSHom.toShHom := rfl

/-- **The algebra structure above is the one Stacks 0D09 is stated over.**  The algebra
structure of `(f^{-1}𝒪_Y)_x` on `𝒪_{X,x}` used here is
`Stacks.RelativeDifferentialStalk.algebraStalk` at the structural map `f^{-1}𝒪_Y ⟶ 𝒪_X`, which
is the one the stalk statement
`Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk` of Stacks 0D09 is
about.  Together with
`Stacks.NaiveCotangentAffineStalk.inverseImageStructureMap_eq_ringedSpace` this says that the
target of the comparison below is the complex Stacks 0D09 identifies the stalk of `NL_{X/Y}`
with. -/
theorem algebraStalkInverseImageStructureMap_eq_algebraStalk :
    algebraStalkInverseImageStructureMap f (x := x) =
      Stacks.RelativeDifferentialStalk.algebraStalk
        (AlgebraicGeometry.inverseImageStructureMap f).hom x := rfl

/-! ### The two scalar towers -/

/-- **The germ of the restriction of `f` is the stalk map of `f`.**  Restricting a section of
`𝒪_Y` over `U` to `V ⊆ f^{-1}U` and taking its germ at `x` is the same as taking its germ at
`f x` and applying the stalk map of `f`.  This is Mathlib's `Scheme.Hom.germ_stalkMap` with the
further restriction from `f^{-1}U` to `V` absorbed into the germ. -/
theorem germ_comp_appLE :
    (X.presheaf.germ V x hx).hom.comp (f.appLE U V hVU).hom =
      (f.stalkMap x).hom.comp (Y.presheaf.germ U (f x) hfx).hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  refine congrArg CommRingCat.Hom.hom ?_
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-- The tower `Γ(Y, U) → Γ(X, V) → 𝒪_{X,x}`, which holds by construction of the algebra
structure of `Γ(Y, U)` on `𝒪_{X,x}`. -/
theorem isScalarTower_appLE :
    letI := algebraAppLE f hVU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    letI := algebraStalkOfAppLE f hVU hx
    IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) := by
  let := algebraAppLE f hVU
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  let := algebraStalkOfAppLE f hVU hx
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The tower `Γ(Y, U) → 𝒪_{Y,f x} → 𝒪_{X,x}`, which is
`Stacks.NaiveCotangentAffineStalk.germ_comp_appLE`. -/
theorem isScalarTower_stalkMap :
    letI := algebraAppLE f hVU
    letI := Y.presheaf.algebra_section_stalk (⟨f x, hfx⟩ : U)
    letI := algebraStalkOfAppLE f hVU hx
    letI := algebraStalkMap f (x := x)
    IsScalarTower Γ(Y, U) ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := by
  let := algebraAppLE f hVU
  let := Y.presheaf.algebra_section_stalk (⟨f x, hfx⟩ : U)
  let := algebraStalkOfAppLE f hVU hx
  let := algebraStalkMap f (x := x)
  exact IsScalarTower.of_algebraMap_eq' (germ_comp_appLE f hVU hx hfx)

/-- **The germ of the restriction of `f` factors through the stalk of `f^{-1}𝒪_Y`.**  The germ
at `x` of the restriction `Γ(Y, U) ⟶ Γ(X, V)` of `f` is the germ at `f x`, followed by the
identification `𝒪_{Y,f x} ≅ (f^{-1}𝒪_Y)_x`, followed by the stalk of the structural map
`f^{-1}𝒪_Y ⟶ 𝒪_X`.  The last two legs compose to the stalk map of `f`
(`Stacks.SheafifyStalk.stalkMap_hom_eq_comp`). -/
theorem germ_comp_appLE_inverseImage :
    (X.presheaf.germ V x hx).hom.comp (f.appLE U V hVU).hom =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
            (AlgebraicGeometry.inverseImageStructureMap f).hom).hom.comp
        ((SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv.hom.comp
          (Y.presheaf.germ U (f x) hfx).hom) := by
  rw [germ_comp_appLE f hVU hx hfx, SheafifyStalk.stalkMap_hom_eq_comp f x]
  exact RingHom.comp_assoc _ _ _

/-- The tower `Γ(Y, U) → (f^{-1}𝒪_Y)_x → 𝒪_{X,x}`, which is
`Stacks.NaiveCotangentAffineStalk.germ_comp_appLE_inverseImage`. -/
theorem isScalarTower_stalkInverseImage :
    letI := algebraAppLE f hVU
    letI := algebraStalkInverseImage f hfx
    letI := algebraStalkOfAppLE f hVU hx
    letI := algebraStalkInverseImageStructureMap f (x := x)
    IsScalarTower Γ(Y, U)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
      ↑(X.presheaf.stalk x) := by
  let := algebraAppLE f hVU
  let := algebraStalkInverseImage f hfx
  let := algebraStalkOfAppLE f hVU hx
  let := algebraStalkInverseImageStructureMap f (x := x)
  exact IsScalarTower.of_algebraMap_eq' (germ_comp_appLE_inverseImage f hVU hx hfx)

/-! ### The two localizations -/

/-- Transport of the property of being a localization at a prime along an equality of primes.
Needed because the two spellings of `𝔮` — the prime of `Γ(Y, U)` corresponding to `f x` and the
contraction of `𝔭` along `Γ(Y, U) ⟶ Γ(X, V)` — are equal but not identical, and
`IsLocalization.AtPrime` cannot be rewritten in its ideal argument: that argument carries the
`Ideal.IsPrime` instance used to form its complement, so the rewrite motive is ill-typed. -/
theorem isLocalization_atPrime_of_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (hPQ : P = Q)
    (hQ : IsLocalization.AtPrime S Q) : IsLocalization.AtPrime S P := by
  subst hPQ
  exact hQ

/-- **`𝔮 = 𝔭 ∩ R`.**  The prime of `Γ(Y, U)` corresponding to `f x` is the contraction along
the restriction of `f` of the prime of `Γ(X, V)` corresponding to `x`.  This is Mathlib's
`AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`, read through the algebra structure. -/
theorem comap_primeIdealOf (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := algebraAppLE f hVU
    Ideal.comap (algebraMap Γ(Y, U) Γ(X, V)) (hV.primeIdealOf ⟨x, hx⟩).asIdeal =
      (hU.primeIdealOf ⟨f x, hfx⟩).asIdeal :=
  congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx)

/-- **`𝒪_{X,x} = A_𝔭`** (Stacks 01HV): the stalk of the structure sheaf at a point of an affine
open is the localization of the sections at the corresponding prime. -/
theorem isLocalization_stalk (hV : IsAffineOpen V) :
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    IsLocalization.AtPrime ↑(X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
  hV.isLocalization_stalk ⟨x, hx⟩

/-- **`(f^{-1}𝒪_Y)_x = R_𝔮`**: the stalk at `x` of the inverse image of the structure sheaf of
`Y` is the localization of `Γ(Y, U)` at the prime corresponding to `f x`.  This combines
Stacks 008H for the sheaf of rings `𝒪_Y`, in the form of
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`, with Stacks 01HV for `𝒪_Y`. -/
theorem isLocalization_stalkInverseImage (hU : IsAffineOpen U) :
    letI := algebraStalkInverseImage f hfx
    IsLocalization.AtPrime
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
      (hU.primeIdealOf ⟨f x, hfx⟩).asIdeal := by
  let := Y.presheaf.algebra_section_stalk (⟨f x, hfx⟩ : U)
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (hU.primeIdealOf ⟨f x, hfx⟩).asIdeal.primeCompl
    (SheafifyStalk.stalkInverseImageStructureSheafIso f x).symm.commRingCatIsoToRingEquiv).mp
      (hU.isLocalization_stalk ⟨f x, hfx⟩)

/-! ### The stalkwise comparison -/

/-- The comparison `NL_{A/R} ⊗_A B ⟶ NL_{B/S}` is a quasi-isomorphism when `B = A_𝔭` and
`S = R_𝔮` for the prime `𝔮 = 𝔭 ∩ R`. -/
private theorem isQuasiIso_nlExtensionBaseChangeMap_of_comap_eq
    {R A B S : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing S] [Algebra R A]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra R S] [Algebra S B]
    [IsScalarTower R S B] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime B P] {Q : Ideal R}
    [Q.IsPrime] (hPQ : P.comap (algebraMap R A) = Q) [IsLocalization.AtPrime S Q]
    (h : (Algebra.Generators.self R A).toExtension.Hom
      (Algebra.Generators.self S B).toExtension) :
    NaiveCotangent.IsQuasiIso (NaiveCotangent.nlExtensionBaseChangeMap (T := B) h) :=
  haveI := isLocalization_atPrime_of_eq hPQ ‹IsLocalization.AtPrime S Q›
  NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_atPrime P h

/-- **The stalkwise step of Stacks 0D0I at the stalks of `𝒪_X` and `𝒪_Y`.**  Let `f : X ⟶ Y` be
a morphism of schemes, let `Spec R = U ⊆ Y` and `Spec A = V ⊆ X` be affine opens with
`V ⊆ f^{-1}U`, and let `x ∈ V`.  Then the canonical map of two-term complexes of
`𝒪_{X,x}`-modules

`NL_{A/R} ⊗_A 𝒪_{X,x} ⟶ NL_{𝒪_{X,x} / 𝒪_{Y,f x}}`

is a quasi-isomorphism.

The two stalks are the localizations `A_𝔭` and `R_𝔮` at the prime `𝔭` of `A` corresponding to
`x` and the prime `𝔮 = 𝔭 ∩ R` of `R` corresponding to `f x`, so this is
`NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_atPrime` at the geometric stalks.  As there,
the statement holds for every morphism of extensions `h` inducing the comparison: any two are
homotopic, so the induced maps on `H₁` and `H₀` do not depend on the choice. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_stalk (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := algebraAppLE f hVU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    letI := Y.presheaf.algebra_section_stalk (⟨f x, hfx⟩ : U)
    letI := algebraStalkOfAppLE f hVU hx
    letI := algebraStalkMap f (x := x)
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) :=
      isScalarTower_appLE f hVU hx
    haveI : IsScalarTower Γ(Y, U) ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      isScalarTower_stalkMap f hVU hx hfx
    ∀ h : (Algebra.Generators.self Γ(Y, U) Γ(X, V)).toExtension.Hom
        (Algebra.Generators.self ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x)).toExtension,
      NaiveCotangent.IsQuasiIso
        (NaiveCotangent.nlExtensionBaseChangeMap (T := ↑(X.presheaf.stalk x)) h) := by
  let := algebraAppLE f hVU
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  let := Y.presheaf.algebra_section_stalk (⟨f x, hfx⟩ : U)
  let := algebraStalkOfAppLE f hVU hx
  let := algebraStalkMap f (x := x)
  have _ := isScalarTower_appLE f hVU hx
  have _ := isScalarTower_stalkMap f hVU hx hfx
  intro h
  have _ := isLocalization_stalk hx hV
  have _ := hU.isLocalization_stalk ⟨f x, hfx⟩
  exact isQuasiIso_nlExtensionBaseChangeMap_of_comap_eq _ (comap_primeIdealOf f hVU hx hfx hU hV) h

/-- **The stalkwise step of Stacks 0D0I at the stalk of `f^{-1}𝒪_Y`.**  The form of
`Stacks.NaiveCotangentAffineStalk.isQuasiIso_nlExtensionBaseChangeMap_stalk` with the base ring
`(f^{-1}𝒪_Y)_x` in place of `𝒪_{Y,f x}`: the canonical map of two-term complexes of
`𝒪_{X,x}`-modules

`NL_{A/R} ⊗_A 𝒪_{X,x} ⟶ NL_{𝒪_{X,x} / (f^{-1}𝒪_Y)_x}`

is a quasi-isomorphism.

The right-hand side is the stalk at `x` of `NL_{X/Y}`: by Stacks 0D09
(`Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk`) the stalk of the
naive cotangent complex of a morphism of sheaves of rings `f^{-1}𝒪_Y ⟶ 𝒪_X` is the naive
cotangent complex of the induced map of stalks, and
`AlgebraicGeometry.Scheme.naiveCotangentComplex` is the naive cotangent complex of exactly that
morphism of sheaves of rings.  The algebra structure used here is the one Stacks 0D09 is stated
over, namely `Stacks.RelativeDifferentialStalk.algebraStalk` at the structural map. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_stalkInverseImage
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := algebraAppLE f hVU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    letI := algebraStalkInverseImage f hfx
    letI := algebraStalkOfAppLE f hVU hx
    letI := algebraStalkInverseImageStructureMap f (x := x)
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) :=
      isScalarTower_appLE f hVU hx
    haveI : IsScalarTower Γ(Y, U)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
        ↑(X.presheaf.stalk x) := isScalarTower_stalkInverseImage f hVU hx hfx
    ∀ h : (Algebra.Generators.self Γ(Y, U) Γ(X, V)).toExtension.Hom
        (Algebra.Generators.self
          ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
          ↑(X.presheaf.stalk x)).toExtension,
      NaiveCotangent.IsQuasiIso
        (NaiveCotangent.nlExtensionBaseChangeMap (T := ↑(X.presheaf.stalk x)) h) := by
  let := algebraAppLE f hVU
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  let := algebraStalkInverseImage f hfx
  let := algebraStalkOfAppLE f hVU hx
  let := algebraStalkInverseImageStructureMap f (x := x)
  have _ := isScalarTower_appLE f hVU hx
  have _ := isScalarTower_stalkInverseImage f hVU hx hfx
  intro h
  have _ := isLocalization_stalk hx hV
  have _ := isLocalization_stalkInverseImage f hfx hU
  exact isQuasiIso_nlExtensionBaseChangeMap_of_comap_eq _ (comap_primeIdealOf f hVU hx hfx hU hV) h

end Stacks.NaiveCotangentAffineStalk

end

end
