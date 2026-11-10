module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.CoherentComplexRepresentative
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroCovariance
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerComplexComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProCategoryOfMap

/-!
# Covariance of extension by zero for open subschemes of a Noetherian scheme

Let `X ⊃ U ⊃ U'` be open subschemes of a Noetherian scheme `X`, let `j : U ⟶ X` and
`j' : U' ⟶ X` be the inclusions and let `i : U' ⟶ U` be the inclusion, so that `j' = j ∘ i` and
hence `j'^* = i^* ∘ j^*`. [Stacks, Tag 0G4Y] constructs a canonical map of pro-objects

`Rj'_!(K|_{U'}) ⟶ Rj_! K`

functorial for `K` in `D^b_{Coh}(𝒪_U)`. This file is that map for the functors
`Rj_! = AlgebraicGeometry.extensionByZeroOpenImmersion` of [Stacks, Tag 0G4N]: it is the
categorical construction `CategoryTheory.extensionByZeroCovariance` (in
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroCovariance`) applied
to the restriction functors of `D^b_{Coh}` and the Deligne-system values of [Stacks, Tag 0G4L].

## Main definitions and results

* `AlgebraicGeometry.extensionByZeroOpenCovariance`: **Stacks 0G4Y**, the canonical map
  `Rj'_!(K|_{U'}) ⟶ Rj_! K`, functorial in `K`.
* `AlgebraicGeometry.extensionByZeroOpenHomEquiv_covariance`: the display of the tag, composing
  with the canonical map is the restriction map.
* `AlgebraicGeometry.extensionByZeroOpenCovariance_app_eq`: the canonical map is the only one with
  the property of the display.
* `AlgebraicGeometry.extensionByZeroOpenCovariance_conj_eq_ofMap`: the explicit construction, the
  canonical map is given by the inclusions `(𝓘')^n 𝓕^• ⊆ 𝓘^n 𝓕^•`.

## References

* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u' u''


/-! ### Open subschemes of a Noetherian scheme -/

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

section HomOfLE

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {X : Scheme.{u}} {U U' : X.Opens} (h : U' ≤ U)

/-- For opens `U' ⊆ U` of `X`, restricting from `X` to `U'` in the derived category is restricting
from `X` to `U` and then from `U` to `U'`. -/
public def restrictDerivedHomOfLEIso :
    (Scheme.Modules.restrictFunctor U'.ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
        Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

variable [IsLocallyNoetherian X]

/-- For opens `U' ⊆ U` of `X`, restricting from `X` to `U'` on `D^b_{Coh}` is restricting from `X`
to `U` and then from `U` to `U'`: the identification `j^* ⋙ i^* ≅ j'^*`. -/
public def restrictBoundedCoherentLiftHomOfLEIso :
    restrictBoundedCoherentLift U.ι ⋙ restrictBoundedCoherentLift (X.homOfLE h) ≅
      restrictBoundedCoherentLift U'.ι :=
  NatIso.ofComponents
    (fun L => ObjectProperty.isoMk _ ((restrictDerivedHomOfLEIso h).app L.obj).symm)
    (fun {_ _} ψ => ObjectProperty.hom_ext _ ((restrictDerivedHomOfLEIso h).inv.naturality ψ.hom))

/-- The identification `AlgebraicGeometry.restrictBoundedCoherentLiftHomOfLEIso`, read in
`D(𝒪_{U'})`, is the inverse of `AlgebraicGeometry.restrictDerivedHomOfLEIso`. -/
public lemma restrictBoundedCoherentLiftHomOfLEIso_hom_app_hom (L : BoundedCoherentDerived X) :
    ((restrictBoundedCoherentLiftHomOfLEIso h).hom.app L).hom =
      (restrictDerivedHomOfLEIso h).inv.app L.obj :=
  rfl

end HomOfLE


variable {X : Scheme.{u}} [IsNoetherian X] {U U' : X.Opens} (h : U' ≤ U)

/-- **Stacks Project, Tag 0G4Y.** Let `X ⊃ U ⊃ U'` be open subschemes of a Noetherian scheme `X`
and let `j : U ⟶ X`, `j' : U' ⟶ X` be the inclusions. There is a canonical map

`Rj'_!(K|_{U'}) ⟶ Rj_! K`

in `Pro-D^b_{Coh}(𝒪_X)`, functorial for `K` in `D^b_{Coh}(𝒪_U)`: a transformation
`i^* ⋙ Rj'_! ⟶ Rj_!` of functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_X)`, where `i : U' ⟶ U` is the
inclusion and `Rj_!`, `Rj'_!` are the functors `AlgebraicGeometry.extensionByZeroOpenImmersion`.

It induces, on morphisms into a constant pro-object `L`, the restriction map
`Hom_U(K, L|_U) → Hom_{U'}(K|_{U'}, L|_{U'})`
(`AlgebraicGeometry.extensionByZeroOpenHomEquiv_covariance`), it is the only map doing so
(`AlgebraicGeometry.extensionByZeroOpenCovariance_app_eq`), and it is given by the inclusions
`(𝓘')^n 𝓕^• ⊆ 𝓘^n 𝓕^•` (`AlgebraicGeometry.extensionByZeroOpenCovariance_conj_eq_ofMap`). -/
@[stacks 0G4Y "the canonical map Rj'_!(K|_{U'}) ⟶ Rj_! K, functorial in K"]
public def extensionByZeroOpenCovariance :
    restrictBoundedCoherentLift (X.homOfLE h) ⋙ extensionByZeroOpenImmersion U'.ι ⟶
      extensionByZeroOpenImmersion U.ι :=
  CategoryTheory.extensionByZeroCovariance (restrictBoundedCoherentLift U.ι)
    (restrictBoundedCoherentLift U'.ι) (restrictBoundedCoherentLift (X.homOfLE h))
    (restrictBoundedCoherentLiftHomOfLEIso h) (DeligneSystem.values U.ι).toAssignment
    (DeligneSystem.values U'.ι).toAssignment

/-- The canonical map of [Stacks, Tag 0G4Y] is the restriction map on functors of points: on
`α : K ⟶ L|_U` it is `α|_{U'}` followed by the identification `(L|_U)|_{U'} ≅ L|_{U'}`. -/
public lemma extensionByZeroOpenCovariance_app_unop_hom_app
    (K : BoundedCoherentDerived U.toScheme) (L : BoundedCoherentDerived X)
    (α : K ⟶ (restrictBoundedCoherentLift U.ι).obj L) :
    ((extensionByZeroOpenCovariance h).app K).unop.hom.app L α =
      (restrictBoundedCoherentLift (X.homOfLE h)).map α ≫
        (restrictBoundedCoherentLiftHomOfLEIso h).hom.app L :=
  rfl

/-- **The display of [Stacks, Tag 0G4Y].** Under the identifications
`Hom_{Pro}(Rj_! K, L) = Hom_U(K, L|_U)` of [Stacks, Tag 0G2H], composing with the canonical map
`Rj'_!(K|_{U'}) ⟶ Rj_! K` is the restriction map
`Hom_U(K, L|_U) → Hom_{U'}(K|_{U'}, L|_{U'})`. -/
@[stacks 0G4Y "the display: composing with the canonical map is the restriction map \
Hom_U(K, L|_U) → Hom_{U'}(K|_{U'}, L|_{U'})"]
public lemma extensionByZeroOpenHomEquiv_covariance
    (K : BoundedCoherentDerived U.toScheme) (L : BoundedCoherentDerived X)
    (f : (extensionByZeroOpenImmersion U.ι).obj K ⟶ ProSeq.const.obj L) :
    extensionByZeroHomEquiv _ (DeligneSystem.values U'.ι).toAssignment
        ((restrictBoundedCoherentLift (X.homOfLE h)).obj K) L
        ((extensionByZeroOpenCovariance h).app K ≫ f) =
      (restrictBoundedCoherentLift (X.homOfLE h)).map
          (extensionByZeroHomEquiv _ (DeligneSystem.values U.ι).toAssignment K L f) ≫
        (restrictBoundedCoherentLiftHomOfLEIso h).hom.app L :=
  CategoryTheory.extensionByZeroHomEquiv_covariance _ _ _ _ _ _ K L f

/-- **The canonical map of [Stacks, Tag 0G4Y] is the only one with the property of the display.**
A morphism `Rj'_!(K|_{U'}) ⟶ Rj_! K` of pro-objects which induces the restriction map on morphisms
into every constant pro-object is the canonical map; this is the appeal to [Stacks, Tag 0G2X] in
the source. -/
@[stacks 0G4Y "the canonical map is the only one inducing the restriction map on morphisms into \
constant pro-objects, which is the appeal to Tag 0G2X"]
public lemma extensionByZeroOpenCovariance_app_eq
    (K : BoundedCoherentDerived U.toScheme)
    (g : (extensionByZeroOpenImmersion U'.ι).obj
        ((restrictBoundedCoherentLift (X.homOfLE h)).obj K) ⟶
      (extensionByZeroOpenImmersion U.ι).obj K)
    (hg : ∀ (L : BoundedCoherentDerived X)
      (f : (extensionByZeroOpenImmersion U.ι).obj K ⟶ ProSeq.const.obj L),
      extensionByZeroHomEquiv _ (DeligneSystem.values U'.ι).toAssignment
          ((restrictBoundedCoherentLift (X.homOfLE h)).obj K) L (g ≫ f) =
        (restrictBoundedCoherentLift (X.homOfLE h)).map
            (extensionByZeroHomEquiv _ (DeligneSystem.values U.ι).toAssignment K L f) ≫
          (restrictBoundedCoherentLiftHomOfLEIso h).hom.app L) :
    g = (extensionByZeroOpenCovariance h).app K :=
  CategoryTheory.extensionByZeroCovariance_app_eq _ _ _ _ _ _ K g hg

/-! ### The explicit construction -/

section Explicit

open DeligneTriangle

variable (F : CochainComplex X.Modules ℤ) (hFge : ∃ a : ℤ, F.IsStrictlyGE a)
  (hFle : ∃ b : ℤ, F.IsStrictlyLE b) (hFcoh : ∀ i : ℤ, (F.X i).IsCoherent)
  {I I' : X.IdealSheafData} (hI : (I.support : Set X) = (Set.range U.ι.base)ᶜ)
  (hI' : (I'.support : Set X) = (Set.range U'.ι.base)ᶜ) (hle : I' ≤ I)

/-- The map of Deligne systems `(K'_n) ⟶ (K_n)` of the explicit construction of
[Stacks, Tag 0G4Y], `K'_n = (𝓘')^n 𝓕^•` and `K_n = 𝓘^n 𝓕^•`, induced by the inclusions
`(𝓘')^n 𝓕^• ⊆ 𝓘^n 𝓕^•` (`AlgebraicGeometry.IdealPowerComplexSystem.compareHom`). -/
public def idealPowerSystemCompare :
    (deligneSystemOfComplex U'.ι I' hI' F hFge hFle hFcoh).system ⟶
      (deligneSystemOfComplex U.ι I hI F hFge hFle hFcoh).system where
  app n := ObjectProperty.homMk (DerivedCategory.Q.map
    ((idealPowerComplexSystem I' F).compareHom (idealPowerComplexSystem I F) hle n.unop))
  naturality {m n} f := by
    let τ : idealPowerComplexFunctor I' F ⟶ idealPowerComplexFunctor I F :=
      NatTrans.ofOpSequence
        (fun n => (idealPowerComplexSystem I' F).compareHom (idealPowerComplexSystem I F) hle n)
        (fun n => by
          rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
          exact IdealPowerComplexSystem.compareHom_comp_transition _ _ hle n)
    exact ObjectProperty.hom_ext _
      (((DerivedCategory.Q.map_comp _ _).symm.trans
        (congrArg DerivedCategory.Q.map (τ.naturality f))).trans (DerivedCategory.Q.map_comp _ _))

/-- The component at `n` of `AlgebraicGeometry.idealPowerSystemCompare` is the comparison map
`(𝓘')^n 𝓕^• ⟶ 𝓘^n 𝓕^•`, read in the derived category. -/
public lemma idealPowerSystemCompare_app_hom (n : ℕᵒᵖ) :
    ((idealPowerSystemCompare F hFge hFle hFcoh hI hI' hle).app n).hom =
      DerivedCategory.Q.map
        ((idealPowerComplexSystem I' F).compareHom (idealPowerComplexSystem I F) hle n.unop) :=
  rfl

variable (K : BoundedCoherentDerived U.toScheme)
  (φ : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj (DerivedCategory.Q.obj F) ≅
    (boundedCoherentDerived U.toScheme).ι.obj K)

/-- The identification of `𝓕^•|_{U'}` with `K|_{U'}` induced by an identification `φ` of
`𝓕^•|_U` with `K`. -/
public def restrictValueIsoOfLE :
    (Scheme.Modules.restrictFunctor U'.ι).mapDerivedCategory.obj (DerivedCategory.Q.obj F) ≅
      (boundedCoherentDerived U'.toScheme).ι.obj
        ((restrictBoundedCoherentLift (X.homOfLE h)).obj K) :=
  (restrictDerivedHomOfLEIso h).app (DerivedCategory.Q.obj F) ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory.mapIso φ

/-- The inverse of `AlgebraicGeometry.restrictValueIsoOfLE` is the restriction of `φ⁻¹` followed
by the comparison of the two ways of restricting from `X` to `U'`. -/
public lemma restrictValueIsoOfLE_inv :
    (restrictValueIsoOfLE h F K φ).inv =
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory.map φ.inv ≫
        (restrictDerivedHomOfLEIso h).inv.app (DerivedCategory.Q.obj F) :=
  rfl

/-- The key identity behind the explicit construction: under the values of the two ideal-power
systems, restricting the identification `K ≅ K_n|_U` to `U'` is the identification
`K|_{U'} ≅ K'_n|_{U'}` followed by the comparison map. -/
public lemma restrict_constIso_inv_comp (n : ℕ) :
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory.map
        ((DeligneSystem.ofComplexValue (j := U.ι) I hI F hFge hFle hFcoh K φ).constIso.inv.app
          (op n)) ≫
      (restrictDerivedHomOfLEIso h).inv.app (DerivedCategory.Q.obj
        ((idealPowerComplexSystem I F).complex n)) =
    (DeligneSystem.ofComplexValue (j := U'.ι) I' hI' F hFge hFle hFcoh _
        (restrictValueIsoOfLE h F K φ)).constIso.inv.app (op n) ≫
      (Scheme.Modules.restrictFunctor U'.ι).mapDerivedCategory.map
        (DerivedCategory.Q.map ((idealPowerComplexSystem I' F).compareHom
          (idealPowerComplexSystem I F) hle n)) := by
  -- `R`, `R'` and `Ri` are the restrictions from `X` to `U`, from `X` to `U'` and from `U` to `U'`
  let R := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory
  let R' := (Scheme.Modules.restrictFunctor U'.ι).mapDerivedCategory
  let Ri := (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory
  let ρ : R' ≅ R ⋙ Ri := restrictDerivedHomOfLEIso h
  let ι := DerivedCategory.Q.map ((idealPowerComplexSystem I F).inclusion n)
  let ι' := DerivedCategory.Q.map ((idealPowerComplexSystem I' F).inclusion n)
  let τ := DerivedCategory.Q.map ((idealPowerComplexSystem I' F).compareHom
    (idealPowerComplexSystem I F) hle n)
  have : IsIso (R.map ι) := isIso_restrict_idealPowerComplex_inclusion U.ι I hI F hFcoh n
  have : IsIso (R'.map ι') := isIso_restrict_idealPowerComplex_inclusion U'.ι I' hI' F hFcoh n
  have hρ : ρ.inv.app _ ≫ R'.map ι = Ri.map (R.map ι) ≫ ρ.inv.app _ :=
    (ρ.inv.naturality ι).symm
  have : IsIso (R'.map ι) := by
    have : R'.map ι = ρ.hom.app _ ≫ Ri.map (R.map ι) ≫ ρ.inv.app _ := by
      rw [← hρ, Iso.hom_inv_id_app_assoc]
    rw [this]
    infer_instance
  have hτ : R'.map τ ≫ R'.map ι = R'.map ι' := by
    rw [← Functor.map_comp, ← DerivedCategory.Q.map_comp,
      IdealPowerComplexSystem.compareHom_comp_inclusion]
  have hc :=
    DeligneSystem.ofComplexValue_constIso_inv_app_comp (j := U.ι) I hI F hFge hFle hFcoh K φ n
  have hc' :=
    DeligneSystem.ofComplexValue_constIso_inv_app_comp (j := U'.ι) I' hI' F hFge hFle hFcoh _
    (restrictValueIsoOfLE h F K φ) n
  refine (cancel_mono (R'.map ι)).1 ?_
  have e1 := (Category.assoc _ _ _).trans (congrArg (fun t =>
    Ri.map ((DeligneSystem.ofComplexValue (j := U.ι) I hI F hFge hFle hFcoh K φ).constIso.inv.app
      (op n)) ≫ t) hρ)
  have e2 := (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ ρ.inv.app _)
    ((Ri.map_comp _ _).symm.trans (congrArg Ri.map hc)))
  have e4 := (congrArg (fun t => (DeligneSystem.ofComplexValue (j := U'.ι) I' hI' F hFge hFle
    hFcoh _ (restrictValueIsoOfLE h F K φ)).constIso.inv.app (op n) ≫ t) hτ.symm).trans
      (Category.assoc _ _ _).symm
  exact e1.trans (e2.trans (hc'.symm.trans e4))

/-- **A morphism of Deligne systems compatible with the values represents the canonical map of
[Stacks, Tag 0G4Y].** Let `(K_n)` be a Deligne system along `U ⟶ X` with value `K`, let `(K'_n)` be
one along `U' ⟶ X` with value `K|_{U'}`, and let `τ : (K'_n) ⟶ (K_n)` be a morphism of inverse
systems whose restriction to `U'` is, at every `n`, the restriction of the identification
`K ≅ K_n|_U`. Then under the identifications `Rj_! K = (K_n)` and `Rj'_!(K|_{U'}) = (K'_n)` the
canonical map `Rj'_!(K|_{U'}) ⟶ Rj_! K` is the morphism of pro-objects induced by `τ`. -/
public theorem extensionByZeroOpenCovariance_conj_eq_ofMap_of_compat
    (K : BoundedCoherentDerived U.toScheme) {D : DeligneSystem U.ι} {D' : DeligneSystem U'.ι}
    (e : D.system ⋙ restrictBoundedCoherent U.ι ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U.toScheme).ι.obj K))
    (e' : D'.system ⋙ restrictBoundedCoherent U'.ι ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U'.toScheme).ι.obj
        ((restrictBoundedCoherentLift (X.homOfLE h)).obj K)))
    (τ : D'.system ⟶ D.system)
    (hτ : ∀ n : ℕᵒᵖ, (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory.map
          (e.inv.app n) ≫
        (restrictDerivedHomOfLEIso h).inv.app ((boundedCoherentDerived X).ι.obj (D.system.obj n)) =
      e'.inv.app n ≫ (restrictBoundedCoherent U'.ι).map (τ.app n)) :
    (D'.valueOfIso _ e').extensionByZeroIso.hom ≫ (extensionByZeroOpenCovariance h).app K ≫
        (D.valueOfIso K e).extensionByZeroIso.inv =
      ProSeq.ofMap τ := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply colimit.hom_ext
  intro i
  rw [ProSeq.ι_ofMap_unop_hom]
  ext L g
  let A := (D.valueOfIso K e).pointsIso
  let A' := (D'.valueOfIso _ e').pointsIso
  change A'.hom.app L (((extensionByZeroOpenCovariance h).app K).unop.hom.app L
      (A.inv.app L ((colimit.ι ((Pro.liftedInverseSequence D.system).op ⋙ coyoneda) i).app L g))) =
    (colimit.ι ((Pro.liftedInverseSequence D'.system).op ⋙ coyoneda) i).app L
      (τ.app (Pro.liftedIndexDown i) ≫ g)
  have hA' : ∀ x, A'.hom.app L (A'.inv.app L x) = x := fun x =>
    Iso.inv_hom_id_app_apply A' L x
  rw [← hA' ((colimit.ι ((Pro.liftedInverseSequence D'.system).op ⋙ coyoneda) i).app L
      (τ.app (Pro.liftedIndexDown i) ≫ g)),
    DeligneSystem.Value.pointsIso_inv_app_ι, DeligneSystem.Value.pointsIso_inv_app_ι]
  congr 1
  apply ObjectProperty.hom_ext
  -- the remaining identity lives in `D(𝒪_{U'})`
  let n := Pro.liftedIndexDown i
  let Ri := (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory
  let ρ := restrictDerivedHomOfLEIso h
  change Ri.map (e.inv.app n ≫ (restrictBoundedCoherent U.ι).map g) ≫ ρ.inv.app L.obj =
    e'.inv.app n ≫ (restrictBoundedCoherent U'.ι).map (τ.app n ≫ g)
  calc Ri.map (e.inv.app n ≫ (restrictBoundedCoherent U.ι).map g) ≫ ρ.inv.app L.obj
      = Ri.map (e.inv.app n) ≫ Ri.map ((restrictBoundedCoherent U.ι).map g) ≫
          ρ.inv.app L.obj :=
        (congrArg (fun t => t ≫ ρ.inv.app L.obj) (Ri.map_comp _ _)).trans (Category.assoc _ _ _)
    _ = (Ri.map (e.inv.app n) ≫ ρ.inv.app ((boundedCoherentDerived X).ι.obj (D.system.obj n))) ≫
          (restrictBoundedCoherent U'.ι).map g :=
        (congrArg (fun t => Ri.map (e.inv.app n) ≫ t) (ρ.inv.naturality g.hom)).trans
          (Category.assoc _ _ _).symm
    _ = (e'.inv.app n ≫ (restrictBoundedCoherent U'.ι).map (τ.app n)) ≫
          (restrictBoundedCoherent U'.ι).map g :=
        congrArg (fun t => t ≫ (restrictBoundedCoherent U'.ι).map g) (hτ n)
    _ = e'.inv.app n ≫ (restrictBoundedCoherent U'.ι).map (τ.app n ≫ g) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => e'.inv.app n ≫ t) ((restrictBoundedCoherent U'.ι).map_comp _ _).symm)

/-- **The explicit construction of [Stacks, Tag 0G4Y].** Let `𝓕^•` be a bounded complex of
coherent `𝒪_X`-modules whose restriction to `U` represents `K`, and let `𝓘' ⊆ 𝓘` be quasi-coherent
sheaves of ideals with `V(𝓘) = X ∖ U` and `V(𝓘') = X ∖ U'`. Then `Rj_! K` and `Rj'_!(K|_{U'})` are
represented by the inverse systems `K_n = 𝓘^n 𝓕^•` and `K'_n = (𝓘')^n 𝓕^•`
(`AlgebraicGeometry.DeligneSystem.Value.extensionByZeroIso`), and under these identifications
the canonical map `Rj'_!(K|_{U'}) ⟶ Rj_! K` is given by the maps `K'_n ⟶ K_n` coming from the
inclusions `(𝓘')^n ⊆ 𝓘^n`.

The reduction to `𝓘' ⊆ 𝓘` is `Stacks.AlgebraicGeometry.IdealPower.support_sup_eq_left`, and
such complexes exist by `AlgebraicGeometry.exists_bounded_isCoherent_complex_restrict_Q_iso`;
such ideals exist, e.g. the vanishing ideals of the closed complements. -/
@[stacks 0G4Y "the explicit construction: the canonical map is given by the maps \
K'_n = (𝓘')^n 𝓕^• ⟶ 𝓘^n 𝓕^• = K_n coming from the inclusions (𝓘')^n ⊆ 𝓘^n"]
public theorem extensionByZeroOpenCovariance_conj_eq_ofMap :
    (DeligneSystem.ofComplexValue (j := U'.ι) I' hI' F hFge hFle hFcoh _
          (restrictValueIsoOfLE h F K φ)).extensionByZeroIso.hom ≫
        (extensionByZeroOpenCovariance h).app K ≫
        (DeligneSystem.ofComplexValue (j := U.ι) I hI F hFge hFle hFcoh K
          φ).extensionByZeroIso.inv =
      ProSeq.ofMap (idealPowerSystemCompare F hFge hFle hFcoh hI hI' hle) :=
  extensionByZeroOpenCovariance_conj_eq_ofMap_of_compat h K _ _ _
    (fun n => restrict_constIso_inv_comp h F hFge hFle hFcoh hI hI' hle K φ n.unop)

end Explicit

end AlgebraicGeometry

end
