module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.Instances.Discrete
public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.Different.Support.EtaleDiscreteFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointsVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Stalks
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ComparisonWithEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.EtaleComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Localization
public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ProfiniteComponentRealization
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.WeaklyEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteSpectrum
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField
public import StacksCore.Tactic.StacksAttribute

/-!
# Functions modulo locally constant functions on the pro-étale site

Let `X` be a scheme and `A` an abelian group. On the small pro-étale site of `X` the rule sending
a weakly étale `X`-scheme `U` to the group `fun(U, A)` of all maps from the set of points of `U` to
`A` is a sheaf `fun(-, A)`. The constant sheaf `A` is a subsheaf of it; write `F` for the quotient,
so that there is a short exact sequence

`0 → A → fun(-, A) → F → 0`

of abelian sheaves on `X_proétale`. Let `ε : X_proétale → X_étale` be the comparison morphism of
sites. The constant sheaf is pulled back from the final topos, hence `A = ε⁻¹A`. On the other
hand, if `X` is nonempty and `A` has more than one element, then `fun(-, A)` is not of the form
`ε⁻¹ℱ`: the fibres of étale `X`-schemes are discrete, while a weakly étale `X`-scheme can have a
Cantor set in a fibre. The same holds for `F`, since the essential image of `ε⁻¹` is closed under
extensions.

Suppose all points of `X` are closed with separably closed residue fields and `U` is affine. Then
all points of `U` are closed with separably closed residue fields, so
`H¹_proétale(U, A) = H¹_étale(U, A) = 0`, and therefore `F(U) = fun(U, A)/A(U)`.

## Main definitions

* `AlgebraicGeometry.ProEtale.pointFunctionsSheaf`: the sheaf `fun(-, A)`, whose sections over `U`
  are by definition all maps `U → A` of sets of points.
* `AlgebraicGeometry.ProEtale.constantToPointFunctions`: the map `A ⟶ fun(-, A)`, induced by the
  inclusion of the constant functions.
* `AlgebraicGeometry.ProEtale.pointFunctionsQuotient`: the quotient sheaf `F`, with projection
  `AlgebraicGeometry.ProEtale.pointFunctionsQuotientProj`, and
  `AlgebraicGeometry.ProEtale.pointFunctionsShortComplex` the sequence
  `0 → A → fun(-, A) → F → 0`.
* `AlgebraicGeometry.ProEtale.constantSheafCompEpsilonInverseImageIsoConstantSheaf`: `A = ε⁻¹A`,
  naturally in `A`.

## Main results

* `AlgebraicGeometry.ProEtale.pointFunctions_isSheaf`: `fun(-, A)` is a sheaf.
* `AlgebraicGeometry.ProEtale.mono_constantToPointFunctions` and
  `AlgebraicGeometry.ProEtale.pointFunctionsShortComplex_shortExact`: the sequence is exact.
* `AlgebraicGeometry.ProEtale.not_etalePullback_pointFunctionsSheaf`: `fun(-, A)` is not pulled
  back from the étale site.
* `AlgebraicGeometry.ProEtale.isClosed_singleton_of_proetale` and
  `AlgebraicGeometry.ProEtale.isSepClosed_residueField_of_proetale`: the hypotheses on the points
  of `X` pass to the objects of its small pro-étale site.
* `AlgebraicGeometry.ProEtale.subsingleton_etaleH_one_constantSheaf`: `H¹_étale(U, A) = 0`.
* `AlgebraicGeometry.ProEtale.ker_pointFunctionsQuotientProjApp`: the kernel of
  `fun(U, A) ⟶ F(U)` is `A(U)`.
* `AlgebraicGeometry.ProEtale.subsingleton_proetaleH_one_constantSheaf`,
  `AlgebraicGeometry.ProEtale.surjective_pointFunctionsQuotientProjApp`,
  `AlgebraicGeometry.ProEtale.pointFunctionsQuotientAppEquiv`:
  `H¹_proétale(U, A) = 0` and `F(U) = fun(U, A)/A(U)`, by the comparison
  `H^i(U_étale, ℱ) = H^i(U_proétale, ε⁻¹ℱ)` [Stacks, Tag 099W].
* `AlgebraicGeometry.ProEtale.not_etalePullback_pointFunctionsQuotient`: `F` is not pulled back
  from the étale site, by `Rε_*ε⁻¹ℱ = ℱ` [Stacks, Tag 099V].

## Implementation notes

The presheaf `fun(-, A)` is defined directly, with restriction maps given by precomposition with
the maps of points, and shown to be a sheaf by identifying it with the sheaf of continuous maps to
`A` with the indiscrete topology; its sections are therefore literally the maps `|U| → A`. The
quotient `F` is the categorical cokernel, and the description of `F(U)` is through the projection
on sections at `U`: its kernel is the image of the constant sections, and in the affine case it is
surjective.

The assertion that `fun(-, A)` and `F` are not pulled back needs `X` to be nonempty: over the
empty scheme every object of the small pro-étale site is empty, `fun(-, A)` and `F` are zero, and
zero is pulled back.

Abelian sheaves on the small pro-étale site of a `Scheme.{u}` take values in
`AddCommGrpCat.{max (u + 1) v}`, so the coefficient group is transported there by `ULift`
(`AlgebraicGeometry.ProEtale.pointFunctionsCoeff`). Cohomology is `CategoryTheory.Sheaf.H`, `Ext`
out of the constant sheaf `ℤ`, in an arbitrary universe `w`. The comparison `ε` is
`AlgebraicGeometry.ProEtale.epsilonInverseImage`, the inverse image along the inclusion of the
small étale site into the small pro-étale site.

## References

* [Stacks Project, Tag 0F6D](https://stacks.math.columbia.edu/tag/0F6D)
* [Stacks Project, Tag 099W](https://stacks.math.columbia.edu/tag/099W)
* [Stacks Project, Tag 099V](https://stacks.math.columbia.edu/tag/099V)
* [Stacks Project, Tag 09AY](https://stacks.math.columbia.edu/tag/09AY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] hasSheafify_proetale enoughInjectives_sheaf_proetale
  isGrothendieckAbelian_sheaf_proetale IsGrothendieckAbelian.hasExt

/-! ### Residue fields of weakly étale morphisms and spectra with closed points -/

private theorem weaklyEtale_residueFieldMap_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] (x : X)
    [IsSepClosed (Y.residueField (f x))] :
    Function.Bijective (f.residueFieldMap x).hom := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let g := f.stalkMap x
  let p := IsLocalRing.maximalIdeal A
  let q := IsLocalRing.maximalIdeal B
  let : Algebra A B := g.hom.toAlgebra
  have : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  have : IsLocalHom g.hom := inferInstance
  have hpq : p = q.comap g.hom := (IsLocalRing.maximalIdeal_comap g.hom).symm
  have hw : Algebra.WeaklyEtale A B := (weaklyEtale_iff_stalkMap_weaklyEtale f).1 ‹_› x
  let r : p.ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.map p q g.hom hpq
  let : Algebra p.ResidueField q.ResidueField := r.toAlgebra
  have : Algebra.IsSeparable p.ResidueField q.ResidueField :=
    (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B hw p q hpq).1
  let eY : Y.residueField (f x) ≃+* p.ResidueField :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p) |>.toRingEquiv
  let eX : X.residueField x ≃+* q.ResidueField :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q) |>.toRingEquiv
  let : IsSepClosed p.ResidueField := IsSepClosed.of_ringEquiv eY.symm
  have hrbij : Function.Bijective r :=
    IsSepClosed.algebraMap_bijective p.ResidueField q.ResidueField
  have hcompat : eX.toRingHom.comp (f.residueFieldMap x).hom =
      r.comp eY.toRingHom := by
    ext z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    have hmk : ∀ {R : Type u} [CommRing R] (P : Ideal R) [P.IsMaximal] (b : R),
        IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
          (Ideal.Quotient.mk P b) = algebraMap R P.ResidueField b := fun _ _ _ => rfl
    show eX (IsLocalRing.ResidueField.map g.hom (IsLocalRing.residue A a)) =
      r (eY (IsLocalRing.residue A a))
    rw [IsLocalRing.ResidueField.map_residue]
    exact (hmk q _).trans <|
      (Ideal.ResidueField.map_algebraMap p q g.hom hpq a).symm.trans (congrArg r (hmk p a)).symm
  have h : Function.Bijective (eX.toRingHom.comp (f.residueFieldMap x).hom) := by
    rw [hcompat]
    exact hrbij.comp eY.bijective
  exact (eX.bijective.of_comp_iff' _).mp h

private theorem primeSpectrum_isMaximal_of_affine_closed_points
    (S : Scheme.{u}) [IsAffine S]
    (hclosed : ∀ x : S, IsClosed ({x} : Set S)) :
    ∀ q : PrimeSpectrum Γ(S, ⊤), q.asIdeal.IsMaximal := by
  let R := Γ(S, ⊤)
  intro q
  let y : S := S.isoSpec.hom.homeomorph.symm q
  have himage : IsClosed (S.isoSpec.hom.homeomorph '' ({y} : Set S)) :=
    S.isoSpec.hom.homeomorph.isClosedMap _ (hclosed y)
  have heq : S.isoSpec.hom.homeomorph '' ({y} : Set S) = {q} := by
    rw [Set.image_singleton]
    exact congrArg (fun z : PrimeSpectrum R => ({z} : Set (PrimeSpectrum R)))
      (S.isoSpec.hom.homeomorph.apply_symm_apply q)
  rw [heq] at himage
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp himage

private theorem primeSpectrum_isProfinite_of_affine_closed_points
    (S : Scheme.{u}) [IsAffine S]
    (hclosed : ∀ x : S, IsClosed ({x} : Set S)) :
    CompactSpace (PrimeSpectrum Γ(S, ⊤)) ∧ T2Space (PrimeSpectrum Γ(S, ⊤)) ∧
      TotallyDisconnectedSpace (PrimeSpectrum Γ(S, ⊤)) :=
  (spec_profinite_tfae Γ(S, ⊤)).out 6 1 rfl rfl |>.mp fun q hq =>
    primeSpectrum_isMaximal_of_affine_closed_points S hclosed ⟨q, hq⟩

/-! ### The sheaf `fun(-, A)` and the constant subsheaf -/

/-- The coefficient group `A`, transported to the universe in which abelian sheaves on the small
pro-étale site of a `Scheme.{u}` take their values. -/
abbrev pointFunctionsCoeff (A : Type v) [AddCommGroup A] : AddCommGrpCat.{max (u + 1) v} :=
  AddCommGrpCat.of (ULift.{max (u + 1) v} A)

/-- The presheaf `fun(-, A)` on the small pro-étale site of `X`: it sends a weakly étale
`X`-scheme `U` to the group of all maps from the set of points of `U` to `A`, and a morphism to
precomposition with the induced map of points. -/
def pointFunctions (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    (X.ProEt)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} where
  obj U := AddCommGrpCat.of (U.unop.left → ULift.{max (u + 1) v} A)
  map g := AddCommGrpCat.ofHom
    { toFun s := fun x => s (g.unop.left.base x)
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- With the indiscrete topology on the coefficients, all maps of points are continuous, so the
point-function presheaf is the presheaf of continuous maps restricted to the small site. -/
private def pointFunctionsForgetIso (X : Scheme.{u}) (A : Type v) [AddCommGroup A]
    [TopologicalSpace (ULift.{max (u + 1) v} A)]
    [IndiscreteTopology (ULift.{max (u + 1) v} A)] :
    pointFunctions X A ⋙ CategoryTheory.forget AddCommGrpCat ≅
      (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙
        AlgebraicGeometry.continuousMapPresheaf (ULift.{max (u + 1) v} A) := by
  refine NatIso.ofComponents (fun U => Equiv.toIso {
    toFun := fun f => ⟨f, continuous_of_indiscreteTopology⟩
    invFun := fun f => f.toFun
    left_inv := fun _ => rfl
    right_inv := fun _ => by
      apply ContinuousMap.ext
      intro x
      rfl
  }) ?_
  intro U V f
  ext g
  apply ContinuousMap.ext
  intro x
  rfl

/-- **The point functions form a sheaf.** The rule `U ↦ (|U| → A)` is a sheaf for the pro-étale
topology: it is the sheaf of continuous maps to `A` with the indiscrete topology, which is an
fpqc sheaf. -/
@[stacks 0F6D "`fun(-, A)` is a sheaf on the pro-étale site"]
theorem pointFunctions_isSheaf (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (pointFunctions.{u, v} X A) := by
  let : TopologicalSpace (ULift.{max (u + 1) v} A) := ⊤
  refine (Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (pointFunctions X A) (CategoryTheory.forget AddCommGrpCat)).2 ?_
  rw [Presheaf.isSheaf_of_iso_iff (pointFunctionsForgetIso X A)]
  have hpro : Presheaf.IsSheaf Scheme.proetaleTopology
      (AlgebraicGeometry.continuousMapPresheaf (ULift.{max (u + 1) v} A)) :=
    Presheaf.IsSheaf.of_le Scheme.proetaleTopology_le_fpqcTopology
      (AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf _)
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology X) Scheme.proetaleTopology
    (AlgebraicGeometry.continuousMapPresheaf _)
    hpro

/-- The sheaf `fun(-, A)` on the small pro-étale site of `X`. Its sections over `U` are all maps
from the points of `U` to `A`, with the restriction maps of `pointFunctions`. -/
def pointFunctionsSheaf (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  ⟨pointFunctions X A, pointFunctions_isSheaf X A⟩

/-- The inclusion of the constant presheaf with value `A` into `fun(-, A)` as the constant
functions. -/
def constantToPointFunctionsPresheaf (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    (Functor.const (X.ProEt)ᵒᵖ).obj (pointFunctionsCoeff.{u} A) ⟶ pointFunctions X A where
  app U := AddCommGrpCat.ofHom {
    toFun a := fun _ => a
    map_zero' := rfl
    map_add' _ _ := rfl }
  naturality U V f := by
    ext a
    rfl

/-- The map `A ⟶ fun(-, A)` of the sequence `0 → A → fun(-, A) → F → 0`: the map from the
constant sheaf with value `A` induced, through sheafification, by the inclusion of the constant
functions `constantToPointFunctionsPresheaf`. -/
def constantToPointFunctions (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj
        (pointFunctionsCoeff.{u} A) ⟶ pointFunctionsSheaf X A :=
  ⟨sheafifyLift (Scheme.ProEt.topology X) (constantToPointFunctionsPresheaf X A)
    (pointFunctions_isSheaf X A)⟩

/-- `constantToPointFunctions` restricts, along the sheafification map of the constant presheaf,
to the inclusion of the constant functions. -/
theorem toSheafify_comp_constantToPointFunctions (X : Scheme.{u}) (A : Type v)
    [AddCommGroup A] :
    toSheafify (Scheme.ProEt.topology X) ((Functor.const (X.ProEt)ᵒᵖ).obj
        (pointFunctionsCoeff.{u} A)) ≫ (constantToPointFunctions X A).hom =
      constantToPointFunctionsPresheaf X A :=
  toSheafify_sheafifyLift _ _ _

/-- **The constant sheaf is a subsheaf of `fun(-, A)`**: the map `A ⟶ fun(-, A)` is a
monomorphism, which is exactness on the left of `0 → A → fun(-, A) → F → 0`. -/
@[stacks 0F6D "exactness on the left of `0 → A → fun(-, A) → F → 0`"]
theorem mono_constantToPointFunctions (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    Mono (constantToPointFunctions.{u, v} X A) := by
  let J := Scheme.ProEt.topology X
  let P := (Functor.const (X.ProEt)ᵒᵖ).obj (pointFunctionsCoeff.{u} A)
  let η := toSheafify J P
  let φ := constantToPointFunctionsPresheaf X A
  have hloc : Presheaf.IsLocallyInjective J φ := by
    constructor
    intro U a b hab
    by_cases hEmpty : IsEmpty U.unop.left
    · exact J.superset_covering bot_le (Scheme.ProEt.bot_mem_topology U.unop)
    · obtain ⟨x⟩ := not_isEmpty_iff.mp hEmpty
      obtain rfl : a = b := congrFun (show (fun _ : U.unop.left => a) = fun _ => b from hab) x
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact J.top_mem U.unop
  let : Presheaf.IsLocallyInjective J (η ≫ (constantToPointFunctions X A).hom) := by
    rw [toSheafify_comp_constantToPointFunctions]
    exact hloc
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  have : Presheaf.IsLocallyInjective J (constantToPointFunctions X A).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      J η (constantToPointFunctions X A).hom
  exact Sheaf.mono_of_isLocallyInjective (constantToPointFunctions X A)

/-- The quotient sheaf `F` of the sequence `0 → A → fun(-, A) → F → 0`: the cokernel of
`constantToPointFunctions`. -/
def pointFunctionsQuotient (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  cokernel (constantToPointFunctions X A)

/-- The projection `fun(-, A) ⟶ F` of the sequence `0 → A → fun(-, A) → F → 0`. -/
abbrev pointFunctionsQuotientProj (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    pointFunctionsSheaf X A ⟶ pointFunctionsQuotient X A :=
  cokernel.π (constantToPointFunctions X A)

/-- The sequence `0 → A → fun(-, A) → F → 0` of abelian sheaves on the small pro-étale site. -/
abbrev pointFunctionsShortComplex (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    ShortComplex (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :=
  ShortComplex.mk (constantToPointFunctions X A) (pointFunctionsQuotientProj X A)
    (cokernel.condition _)

/-- **The sequence `0 → A → fun(-, A) → F → 0` is short exact.** -/
@[stacks 0F6D "the sequence `0 → A → fun(-, A) → F → 0` is exact"]
theorem pointFunctionsShortComplex_shortExact (X : Scheme.{u}) (A : Type v) [AddCommGroup A] :
    (pointFunctionsShortComplex X A).ShortExact :=
  have := mono_constantToPointFunctions X A
  { exact := ShortComplex.exact_cokernel _
    epi_g := inferInstanceAs (Epi (cokernel.π _)) }

/-- The inclusion `A(U) ⟶ fun(U, A)` of the constant sections at `U`. -/
abbrev constantToPointFunctionsApp (X : Scheme.{u}) (A : Type v) [AddCommGroup A]
    (U : X.ProEt) :=
  ((constantToPointFunctions.{u, v} X A).hom.app (op U)).hom

/-- The projection `fun(U, A) ⟶ F(U)` at `U`. -/
abbrev pointFunctionsQuotientProjApp (X : Scheme.{u}) (A : Type v) [AddCommGroup A]
    (U : X.ProEt) :=
  ((pointFunctionsQuotientProj.{u, v} X A).hom.app (op U)).hom

/-- **The kernel of `fun(U, A) ⟶ F(U)` is `A(U)`**, for every object `U` of the small pro-étale
site: sections are left exact. -/
@[stacks 0F6D "the kernel of `fun(U, A) → F(U)` is `A(U)`"]
theorem ker_pointFunctionsQuotientProjApp (X : Scheme.{u}) (A : Type v) [AddCommGroup A]
    (U : X.ProEt) :
    (pointFunctionsQuotientProjApp X A U).ker = (constantToPointFunctionsApp X A U).range := by
  let J := Scheme.ProEt.topology X
  let D := AddCommGrpCat.{max (u + 1) v}
  let ev : Sheaf J D ⥤ D := sheafToPresheaf J D ⋙ (evaluation (X.ProEt)ᵒᵖ D).obj (op U)
  have hS : ((pointFunctionsShortComplex X A).map ev).Exact :=
    (pointFunctionsShortComplex_shortExact X A).exact.map_of_mono_of_preservesKernel ev
      (mono_constantToPointFunctions X A) inferInstance
  refine le_antisymm (ShortComplex.ab_exact_iff_ker_le_range.mp hS) ?_
  rintro _ ⟨a, rfl⟩
  exact DFunLike.congr_fun
    (congrArg AddCommGrpCat.Hom.hom ((pointFunctionsShortComplex X A).map ev).zero) a

/-! ### The constant sheaf is pulled back from the étale site -/

/-- **The constant sheaf is pulled back from the étale site: `A = ε⁻¹A`.** Both the constant
sheaf functor of the small pro-étale site and the constant sheaf functor of the small étale site
followed by `ε⁻¹` are left adjoint to taking sections over the final object `X ⟶ X`, that is,
both are the pullback from the final topos; the isomorphism is the comparison of these two left
adjoints, natural in the coefficient group. -/
@[stacks 0F6D "`A = ε⁻¹A`: the constant sheaf is pulled back from the étale site"]
def constantSheafCompEpsilonInverseImageIsoConstantSheaf (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
        epsilonInverseImage.{u, v} X ≅
      constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ ↦ inferInstance⟩
  letI : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ ↦ inferInstance⟩
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let hT' : IsTerminal (X.etaleToProetale.obj T) := MorphismProperty.Over.mkIdTerminal _ X
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} hT).comp
      (epsilonAdjunction.{u, v} X)).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} hT')

/-! ### `fun(-, A)` is not pulled back from the étale site -/

private def fiberFunctor (X : Scheme.{u}) (x : X) : X.ProEt ⥤ Scheme.{u} :=
  Scheme.ProEt.forget X ⋙ Over.pullback (X.fromSpecResidueField x) ⋙ Over.forget _

private local instance fiberFunctor_continuous (X : Scheme.{u}) (x : X) :
    (fiberFunctor X x).IsContinuous (Scheme.ProEt.topology X) Scheme.proetaleTopology := by
  dsimp [fiberFunctor]
  have : (Over.pullback (X.fromSpecResidueField x) ⋙ Over.forget _).IsContinuous
      (Scheme.proetaleTopology.over X) Scheme.proetaleTopology :=
    Functor.isContinuous_comp _ _ _ (Scheme.proetaleTopology.over _) _
  exact Functor.isContinuous_comp _ _ _ (Scheme.proetaleTopology.over X) _

private def fiberContinuousSheaf (X : Scheme.{u}) (x : X)
    (A : Type (max (u + 1) v)) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  ⟨(fiberFunctor X x).op ⋙ continuousMapPresheafAb A,
    (fiberFunctor X x).op_comp_isSheaf_of_isSheaf _ Scheme.proetaleTopology _
      (Presheaf.IsSheaf.of_le Scheme.proetaleTopology_le_fpqcTopology
        (isSheaf_fpqcTopology_continuousMapPresheafAb A))⟩

private def fiberContinuousInclusion (X : Scheme.{u}) (x : X)
    (A : Type (max (u + 1) v)) [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] :
    fiberContinuousSheaf X x A ⟶
      @fiberContinuousSheaf X x A _ ⊤ inferInstance where
  hom.app _ := AddCommGrpCat.ofHom {
    toFun f := @ContinuousMap.mk _ A _ ⊤ (fun t => f t)
      (@continuous_of_indiscreteTopology _ _ _ ⊤ inferInstance _)
    map_zero' := rfl
    map_add' _ _ := rfl }
  hom.naturality _ _ _ := rfl

private theorem isIso_push_fiberContinuousInclusion (X : Scheme.{u}) (x : X)
    (A : Type (max (u + 1) v)) [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] :
    IsIso ((epsilonDirectImage.{u, v} X).map
        (fiberContinuousInclusion X x A)) := by
  let m := (epsilonDirectImage.{u, v} X).map
        (fiberContinuousInclusion X x A)
  have : ∀ U, IsIso (((sheafToPresheaf _ _).map m).app U) := by
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    show Function.Bijective (fun f : C(U.unop.hom.fiber x, A) =>
      @ContinuousMap.mk _ A _ ⊤ (fun t => f t)
        (@continuous_of_indiscreteTopology _ _ _ ⊤ inferInstance _))
    constructor
    · intro a b h
      exact ContinuousMap.ext (fun t => congrArg (fun f : @ContinuousMap _ A _ ⊤ => f t) h)
    · intro a
      have : DiscreteTopology (U.unop.hom.fiber x) :=
        AlgebraicGeometry.discreteTopology_fiber U.unop.hom x
      exact ⟨⟨fun t => a t, continuous_of_discreteTopology⟩, rfl⟩
  have : IsIso ((sheafToPresheaf _ _).map m) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso m (sheafToPresheaf _ _)

/-- Objects in the image of a left adjoint lift against maps inverted by the right adjoint. -/
private theorem factors_of_essImage_of_isIso_rightAdjoint
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {P Q V : D} (m : P ⟶ Q) [IsIso (R.map m)]
    (hV : L.essImage V) (f : V ⟶ Q) : ∃ g : V ⟶ P, g ≫ m = f := by
  obtain ⟨W, ⟨e⟩⟩ := hV
  let g := (adj.homEquiv W P).symm ((adj.homEquiv W Q) (e.hom ≫ f) ≫ inv (R.map m))
  refine ⟨e.inv ≫ g, ?_⟩
  have hg : g ≫ m = e.hom ≫ f := by
    apply (adj.homEquiv W Q).injective
    rw [adj.homEquiv_naturality_right]
    simp [g]
  rw [Category.assoc, hg, Iso.inv_hom_id_assoc]

private def pointFunctionsToFiber (X : Scheme.{u}) (x : X) (A : Type v)
    [AddCommGroup A] : pointFunctionsSheaf X A ⟶
      @fiberContinuousSheaf X x (ULift.{max (u + 1) v} A) _ ⊤ inferInstance where
  hom.app U := AddCommGrpCat.ofHom {
    toFun f := @ContinuousMap.mk _ _ _ ⊤ (fun t => f (U.unop.hom.fiberι x t))
      (@continuous_of_indiscreteTopology _ _ _ ⊤ inferInstance _)
    map_zero' := rfl
    map_add' _ _ := rfl }
  hom.naturality U V g := by
    apply AddCommGrpCat.hom_ext
    ext f
    apply @ContinuousMap.ext _ _ _ ⊤
    intro t
    change f (g.unop.left (V.unop.hom.fiberι x t)) =
      f (U.unop.hom.fiberι x ((pullback.map V.unop.hom (X.fromSpecResidueField x)
        U.unop.hom (X.fromSpecResidueField x) g.unop.left (𝟙 _) (𝟙 X)
        ((Category.comp_id _).trans (MorphismProperty.Over.w g.unop).symm) (by simp)) t))
    congr 1
    have heq : pullback.map V.unop.hom (X.fromSpecResidueField x)
        U.unop.hom (X.fromSpecResidueField x) g.unop.left (𝟙 _) (𝟙 X)
        (by simpa using (MorphismProperty.Over.w g.unop).symm) (by simp) ≫
        pullback.fst U.unop.hom (X.fromSpecResidueField x) =
        pullback.fst V.unop.hom (X.fromSpecResidueField x) ≫ g.unop.left := by
      dsimp only [pullback.map]
      exact pullback.lift_fst _ _ _
    exact (congrArg (fun h : V.unop.hom.fiber x ⟶ U.unop.left => h t) heq).symm

/-- Point-functions coming from the étale site are continuous on every fibre. -/
private theorem continuous_on_fiber_of_essImage (X : Scheme.{u}) (A : Type v)
    [AddCommGroup A]
    (h : (epsilonInverseImage.{u, v} X).essImage (pointFunctionsSheaf X A))
    (U : X.ProEt) (x : X) (s : U.left → ULift.{max (u + 1) v} A) :
    @Continuous _ _ _ ⊥ (s ∘ U.hom.fiberι x) := by
  let : TopologicalSpace (ULift.{max (u + 1) v} A) := ⊥
  let : DiscreteTopology (ULift.{max (u + 1) v} A) := ⟨rfl⟩
  let : IsTopologicalAddGroup (ULift.{max (u + 1) v} A) := inferInstance
  let m := fiberContinuousInclusion X x (ULift.{max (u + 1) v} A)
  let adj := epsilonAdjunction.{u, v} X
  have : IsIso ((epsilonDirectImage.{u, v} X).map m) :=
    isIso_push_fiberContinuousInclusion X x _
  obtain ⟨g, hg⟩ := factors_of_essImage_of_isIso_rightAdjoint adj m h
    (pointFunctionsToFiber X x A)
  let t := g.hom.app (op U) s
  have ht : t.toFun = s ∘ U.hom.fiberι x :=
    congrArg (fun f : @ContinuousMap _ (ULift.{max (u + 1) v} A) _ ⊤ =>
      @ContinuousMap.toFun _ _ _ ⊤ f) (congrArg (fun k => k.hom.app (op U) s) hg)
  exact ht ▸ t.continuous

private theorem exists_spec_profinite_section (R : Type u) [CommRing R]
    (p : PrimeSpectrum R) (T : Type u) [TopologicalSpace T] [CompactSpace T]
    [T2Space T] [TotallyDisconnectedSpace T] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S), Algebra.WeaklyEtale R S ∧
      ∃ (g : C(PrimeSpectrum S, T)) (s : C(T, PrimeSpectrum S)),
        (∀ t, PrimeSpectrum.comap (algebraMap R S) (s t) = p) ∧
        (∀ t, g (s t) = t) := by
  obtain ⟨S, hS, hRS, hZ, g, e, he, hpb⟩ :=
    AlgebraicGeometry.ProEtale.exists_indZariski_of_profinite_component_map R T
      ((isProfiniteStacks_iff_compact_t2_totallyDisconnected T).2
        ⟨inferInstance, inferInstance, inferInstance⟩)
      (ContinuousMap.const T (ConnectedComponents.mk p))
  let a : TopCat.of T ⟶ TopCat.of (ULift.{u} (PrimeSpectrum R)) :=
    TopCat.ofHom (ContinuousMap.const T (ULift.up p))
  let b : TopCat.of T ⟶ TopCat.of (ULift.{u} T) :=
    TopCat.ofHom ⟨ULift.up, continuous_uliftUp⟩
  have hw : a ≫ TopCat.ofHom
      (⟨fun p => ULift.up (ConnectedComponents.mk p.down),
        continuous_uliftUp.comp (ConnectedComponents.continuous_coe.comp continuous_uliftDown)⟩ :
        C(ULift.{u} (PrimeSpectrum R), ULift.{u} (_root_.ConnectedComponents (PrimeSpectrum R)))) =
      b ≫ TopCat.ofHom
        (⟨fun _ => ULift.up (ConnectedComponents.mk p), continuous_const⟩ :
          C(ULift.{u} T, ULift.{u} (_root_.ConnectedComponents (PrimeSpectrum R)))) := by
    ext t
    rfl
  let s := hpb.lift a b hw
  refine ⟨S, hS, hRS, Algebra.WeaklyEtale.of_isIndZariski hZ, g, s.hom, ?_, ?_⟩
  · intro t
    exact congrArg (fun f : TopCat.of T ⟶ TopCat.of (ULift.{u} (PrimeSpectrum R)) =>
      (f t).down) (hpb.lift_fst a b hw)
  · intro t
    exact congrArg (fun f : TopCat.of T ⟶ TopCat.of (ULift.{u} T) =>
      (f t).down) (hpb.lift_snd a b hw)

private theorem exists_proetale_profinite_section (X : Scheme.{u}) (hX : Nonempty X)
    (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TotallyDisconnectedSpace T] :
    ∃ (U : X.ProEt) (x : X) (g : C(U.left, T)) (s : C(T, U.left)),
      (∀ t, U.hom (s t) = x) ∧ (∀ t, g (s t) = t) := by
  let x₀ := Classical.choice hX
  let V := (X.affineCover.f (X.affineCover.idx x₀)).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  have hx : x₀ ∈ V := X.affineCover.covers x₀
  let p := hV.primeIdealOf ⟨x₀, hx⟩
  obtain ⟨S, hS, hRS, hweak, g, s, hs, hgs⟩ :=
    exists_spec_profinite_section Γ(X, V) p T
  let f := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) S))
  have : WeaklyEtale f := (weaklyEtale_specMap_iff _).2
    (by rw [CommRingCat.hom_ofHom, toAlgebra_algebraMap]; exact hweak)
  have : WeaklyEtale hV.fromSpec := inferInstance
  let U : X.ProEt := Scheme.ProEt.mk (f ≫ hV.fromSpec)
  refine ⟨U, hV.fromSpec p, g, s, ?_, hgs⟩
  intro t
  show hV.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, V) S) (s t)) = _
  rw [hs]

private theorem finite_of_continuous_functions (T A : Type*) [TopologicalSpace T]
    [CompactSpace T] [TopologicalSpace A] [DiscreteTopology A] [Nontrivial A]
    (h : ∀ f : T → A, Continuous f) : Finite T := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have : DiscreteTopology T := discreteTopology_iff_isOpen_singleton.mpr fun t => by
    have hp := (isOpen_discrete ({a} : Set A)).preimage (h (fun z => if z = t then a else b))
    convert hp using 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    split_ifs with hz
    · simp [hz]
    · simp [hz, Ne.symm hab]
  exact finite_of_compact_of_discrete

/-- Over the empty scheme `fun(-, A)` is zero, hence pulled back from the étale site, so the
hypothesis that `X` is nonempty in `not_etalePullback_pointFunctionsSheaf` cannot be dropped. -/
theorem mem_essImage_pointFunctionsSheaf_of_isEmpty (X : Scheme.{u}) [IsEmpty X] (A : Type v)
    [AddCommGroup A] : (epsilonInverseImage.{u, v} X).essImage (pointFunctionsSheaf X A) := by
  have hP : IsZero (pointFunctionsSheaf X A) := by
    refine IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) _
      (Functor.isZero _ fun U ↦ ?_)
    have : IsEmpty U.unop.left := ⟨fun y ↦ @IsEmpty.false X _ (U.unop.hom y)⟩
    let : Subsingleton (U.unop.left → ULift.{max (u + 1) v} A) := inferInstance
    exact AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (U.unop.left → ULift A))
  have := (epsilonAdjunction.{u, v} X).isLeftAdjoint
  obtain ⟨Z, hZ⟩ :=
    HasZeroObject.zero (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  exact ⟨Z, ⟨(Functor.map_isZero _ hZ).iso hP⟩⟩

/-- **`fun(-, A)` is not pulled back from the étale site.** If `X` is nonempty and `A` has more
than one element, `fun(-, A)` is not in the essential image of `ε⁻¹`.

A pulled back sheaf restricted to the fibre over a point `x` only sees continuous functions on the
fibres of its sections' domains with the discrete topology on `A`, since the fibres of étale
`X`-schemes over `x` are discrete; but there is a weakly étale `X`-scheme whose fibre over `x`
contains a Cantor set, on which not every function is continuous. -/
@[stacks 0F6D "if `A` has more than one element, `fun(-, A)` is not pulled back from the étale \
site (for `X` nonempty)"]
theorem not_etalePullback_pointFunctionsSheaf (X : Scheme.{u}) (A : Type v)
    [AddCommGroup A] (hX : Nonempty X) (hA : Nontrivial A) :
    ¬ (epsilonInverseImage.{u, v} X).essImage (pointFunctionsSheaf X A) := by
  classical
  intro h
  let : Nontrivial A := hA
  let : TopologicalSpace (ULift.{max (u + 1) v} A) := ⊥
  let : DiscreteTopology (ULift.{max (u + 1) v} A) := ⟨rfl⟩
  let T := ULift.{u} (ℕ → Bool)
  have : TotallyDisconnectedSpace T := Homeomorph.ulift.symm.totallyDisconnectedSpace
  obtain ⟨U, x, g, s, hs, hgs⟩ := exists_proetale_profinite_section X hX T
  let sf : C(T, U.hom.fiber x) :=
    ⟨fun t => (U.hom.fiberHomeo x).symm ⟨s t, hs t⟩,
      (U.hom.fiberHomeo x).symm.continuous.comp (s.continuous.subtype_mk _)⟩
  have hall (f : T → ULift.{max (u + 1) v} A) : Continuous f := by
    have hc := (continuous_on_fiber_of_essImage X A h U x (f ∘ g)).comp sf.continuous
    convert hc using 1
    funext t
    show f t = f (g (U.hom.fiberι x ((U.hom.fiberHomeo x).symm ⟨s t, hs t⟩)))
    rw [Scheme.Hom.fiberι_fiberHomeo_symm, hgs]
  have : Finite T := finite_of_continuous_functions T (ULift.{max (u + 1) v} A) hall
  exact not_finite T

/-! ### Points and residue fields of the objects of the small pro-étale site -/

/-- **Closed points pass to weakly étale `X`-schemes.** If all points of `X` are closed, then all
points of every object `U` of the small pro-étale site of `X` are closed: over an affine open of
`X`, whose spectrum is then profinite, an affine open of `U` has profinite spectrum too. -/
@[stacks 0F6D "if all points of `X` are closed, then all points of `U` are closed"]
theorem isClosed_singleton_of_proetale (X : Scheme.{u})
    (hclosed : ∀ x : X, IsClosed ({x} : Set X))
    (U : X.ProEt) (y : U.left) : IsClosed ({y} : Set U.left) := by
  let f := U.hom
  let : WeaklyEtale f := U.prop
  apply closure_subset_iff_isClosed.mp
  intro z hz
  have hyz : y ⤳ z := specializes_iff_mem_closure.2 hz
  have hfyz : f y ⤳ f z := hyz.map f.continuous
  have hbase : f y = f z := by
    have hmem := (specializes_iff_forall_closed.mp hfyz) ({f y} : Set X)
      (hclosed (f y)) (by simp)
    simpa using hmem.symm
  let C := X.affineCover.f (X.affineCover.idx (f z))
  let W := C.opensRange
  let hW : IsAffineOpen W := isAffineOpen_opensRange C
  have hzW : f z ∈ W := X.affineCover.covers (f z)
  have hyW : f y ∈ W := by simpa [hbase]
  let P : U.left.Opens := f ⁻¹ᵁ W
  have hzP : z ∈ P := by simpa [P] using hzW
  obtain ⟨_, ⟨V : U.left.Opens, hV, rfl⟩, hzV, hVP⟩ :=
    U.left.isBasis_affineOpens.exists_subset_of_mem_open hzP P.2
  have hyV : y ∈ V := hyz.mem_open V.2 hzV
  let S := W.toScheme
  have hclosedS : ∀ x : S, IsClosed ({x} : Set S) := by
    intro x
    rw [← W.ι.isOpenEmbedding.injective.preimage_image {x}, Set.image_singleton]
    exact (hclosed (W.ι x)).preimage W.ι.continuous
  let : IsAffine S := hW
  let : IsAffine V.toScheme := hV
  let g := f.resLE W V hVP
  have hgcomp : g ≫ W.ι = V.ι ≫ f := Scheme.Hom.resLE_comp_ι f hVP
  have : WeaklyEtale (g ≫ W.ι) := by
    rw [hgcomp]
    infer_instance
  have : WeaklyEtale W.ι := inferInstance
  have : WeaklyEtale g := WeaklyEtale.of_comp g W.ι
  let R := Γ(S, ⊤)
  let T := Γ(V.toScheme, ⊤)
  let φ : R →+* T := g.appTop.hom
  let : Algebra R T := φ.toAlgebra
  have hweakSpec : WeaklyEtale (Spec.map (CommRingCat.ofHom φ)) := by
    have heq : Spec.map (CommRingCat.ofHom φ) =
        V.toScheme.isoSpec.inv ≫ g ≫ S.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality g]
      simp [φ]
    rw [heq]
    infer_instance
  let : Algebra.WeaklyEtale R T := (weaklyEtale_specMap_iff (CommRingCat.ofHom φ)).1 hweakSpec
  have hbaseProf := primeSpectrum_isProfinite_of_affine_closed_points S hclosedS
  have htotalProf := AlgebraicGeometry.ProEtale.primeSpectrum_isProfinite_of_weaklyEtale
    R T hbaseProf
  let e := (V.toScheme.isoSpec.hom.homeomorph).symm
  let : T2Space V.toScheme :=
    @Homeomorph.t2Space (PrimeSpectrum T) V.toScheme _ _ htotalProf.2.1 e
  have hspecV : (⟨y, hyV⟩ : V.toScheme) ⤳ (⟨z, hzV⟩ : V.toScheme) :=
    (subtype_specializes_iff ⟨y, hyV⟩ ⟨z, hzV⟩).2 hyz
  have heqV := (specializes_iff_eq (X := V.toScheme)).mp hspecV
  show z = y
  simpa using (congrArg Subtype.val heqV).symm

/-- **Separably closed residue fields pass to weakly étale `X`-schemes.** If all residue fields
of `X` are separably closed, then so are all residue fields of every object `U` of the small
pro-étale site of `X`: the residue field extensions of a weakly étale morphism are separable
algebraic. -/
@[stacks 0F6D "if all residue fields of `X` are separably closed, then so are those of `U`"]
theorem isSepClosed_residueField_of_proetale (X : Scheme.{u})
    (hsep : ∀ x : X, IsSepClosed (X.residueField x))
    (U : X.ProEt) (y : U.left) : IsSepClosed (U.left.residueField y) := by
  let : IsSepClosed (X.residueField (U.hom y)) := hsep (U.hom y)
  let : WeaklyEtale U.hom := U.prop
  have hbij := weaklyEtale_residueFieldMap_bijective
    (X := U.left) (Y := X) (f := U.hom) y
  let e : X.residueField (U.hom y) ≃+* U.left.residueField y :=
    RingEquiv.ofBijective (U.hom.residueFieldMap y).hom hbij
  exact IsSepClosed.of_ringEquiv e.symm

/-! ### Values of `F` on affine objects -/

/-- **`H¹_étale(U, A) = 0`** for an affine object `U` of the small pro-étale site of a scheme `X`
all of whose points are closed with separably closed residue fields: the points of `U` are then
closed with separably closed residue fields, and étale cohomology in positive degrees vanishes on
such an affine scheme. -/
@[stacks 0F6D "`H¹_étale(U, A) = 0` for affine `U`, when all points of `X` are closed with \
separably closed residue fields"]
theorem subsingleton_etaleH_one_constantSheaf (X : Scheme.{u}) (A : Type v) [AddCommGroup A]
    (hclosed : ∀ x : X, IsClosed ({x} : Set X))
    (hsep : ∀ x : X, IsSepClosed (X.residueField x))
    (U : X.ProEt) [IsAffine U.left]
    [HasExt.{w} (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    Subsingleton (Sheaf.H.{w}
      ((constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (pointFunctionsCoeff.{u} A)) 1) := by
  have : U.left.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact subsingleton_etaleCohomology_of_closed_points.{u, max (u + 1) v, w} U.left
    (isClosed_singleton_of_proetale X hclosed U) (isSepClosed_residueField_of_proetale X hsep U)
    _ 1 one_pos

/-! ### The statements resting on the comparison of étale and pro-étale cohomology -/

/-- **`H¹_proétale(U, A) = 0`** for an affine object `U` of the small pro-étale site of a scheme
`X` all of whose points are closed with separably closed residue fields: by the comparison
`H^i(U_étale, ℱ) = H^i(U_proétale, ε⁻¹ℱ)` of étale and pro-étale cohomology on `U` (Stacks 099W
(1), `AlgebraicGeometry.ProEtale.epsilonInverseImageCompFunctorHIso`) and `A = ε⁻¹A`, it reduces
to `H¹_étale(U, A) = 0`. -/
@[stacks 0F6D "`H¹_proétale(U, A) = 0` for affine `U`, when all points of `X` are closed with \
separably closed residue fields"]
theorem subsingleton_proetaleH_one_constantSheaf (X : Scheme.{u})
    (A : Type v) [AddCommGroup A]
    (hclosed : ∀ x : X, IsClosed ({x} : Set X))
    (hsep : ∀ x : X, IsSepClosed (X.residueField x))
    (U : X.ProEt) [IsAffine U.left]
    [HasExt.{w} (Sheaf (Scheme.ProEt.topology U.left) AddCommGrpCat.{max (u + 1) v})] :
    Subsingleton (Sheaf.H.{w}
      ((constantSheaf (Scheme.ProEt.topology U.left) AddCommGrpCat.{max (u + 1) v}).obj
        (pointFunctionsCoeff.{u} A)) 1) := by
  let D := AddCommGrpCat.{max (u + 1) v}
  let F := (constantSheaf U.left.smallEtaleTopology D).obj (pointFunctionsCoeff.{u} A)
  have : Subsingleton (Sheaf.H.{max (u + 1) v} F 1) :=
    subsingleton_etaleH_one_constantSheaf X A hclosed hsep U
  let e : Sheaf.H.{max (u + 1) v} F 1 ≃+
      Sheaf.H.{max (u + 1) v} ((epsilonInverseImage.{u, v} U.left).obj F) 1 :=
    ((epsilonInverseImageCompFunctorHIso.{max (u + 1) v, v, u} U.left 1).app
      F).addCommGroupIsoToAddEquiv.symm
  let e' := (Sheaf.functorH.{max (u + 1) v} (Scheme.ProEt.topology U.left) 1).mapIso
    ((constantSheafCompEpsilonInverseImageIsoConstantSheaf.{u, v} U.left).app
      (pointFunctionsCoeff.{u} A))
  let : Subsingleton ((Sheaf.functorH.{max (u + 1) v} (Scheme.ProEt.topology U.left) 1).obj
      ((constantSheaf U.left.smallEtaleTopology D ⋙ epsilonInverseImage.{u, v} U.left).obj
        (pointFunctionsCoeff.{u} A))) :=
    e.symm.injective.subsingleton
  have : Subsingleton (Sheaf.H.{max (u + 1) v}
      ((constantSheaf (Scheme.ProEt.topology U.left) D).obj (pointFunctionsCoeff.{u} A)) 1) :=
    e'.symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  exact Abelian.Ext.chgUniv.{max (u + 1) v, w}.injective.subsingleton

/-- Postcomposition with a weakly étale `U ⟶ X` is cocontinuous for the small pro-étale
topologies: it is the localization equivalence onto the slice over `U` followed by the forgetful
functor of the slice. -/
private theorem isCocontinuous_proetalePostcompose {S X : Scheme.{u}}
    (j : S ⟶ X) [WeaklyEtale j] :
    (proetalePostcompose j).IsCocontinuous
      (Scheme.ProEt.topology S) (Scheme.ProEt.topology X) := by
  let e := localizationEquivalence (Scheme.ProEt.mk j)
  let : e.functor.IsCocontinuous (Scheme.ProEt.topology S)
      ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk j)) := by
    show (localizationEquivalence (Scheme.ProEt.mk j)).functor.IsCocontinuous
      (Scheme.ProEt.topology (Scheme.ProEt.mk j).left) _
    rw [localizationEquivalence_inducedTopology]
    infer_instance
  have h := isCocontinuous_comp (L := Scheme.ProEt.topology X) e.functor
    (Over.forget (Scheme.ProEt.mk j))
    (Scheme.ProEt.topology S) ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk j))
  rw [localizationEquivalence_forget] at h
  exact h

/-- In a short exact sequence of abelian sheaves whose first term has vanishing `H¹`, sections
over a final object are surjective on the last two terms. -/
private theorem surjective_app_of_subsingleton_H_one
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    {T : C} (hT : IsTerminal T) (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.ShortExact) [Subsingleton (Sheaf.H.{w} S.X₁ 1)] :
    Function.Surjective (S.g.hom.app (op T)) := by
  intro s
  let x := (Sheaf.H.equiv₀ S.X₃ hT).symm s
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hS x (n₁ := 1) rfl
    (Subsingleton.elim _ _)
  refine ⟨Sheaf.H.equiv₀ S.X₂ hT y, ?_⟩
  rw [Sheaf.H.equiv₀_naturality]
  rw [show Sheaf.H.map S.g 0 y = x from hy]
  exact (Sheaf.H.equiv₀ S.X₃ hT).apply_symm_apply s

/-- **`fun(U, A) ⟶ F(U)` is surjective** for an affine object `U` of the small pro-étale site of
a scheme `X` all of whose points are closed with separably closed residue fields: the obstruction
lies in `H¹_proétale(U, A)`, which vanishes. -/
@[stacks 0F6D "`F(U) = fun(U, A)/A(U)` for affine `U`: every section of `F` over `U` lifts to \
`fun(U, A)`"]
theorem surjective_pointFunctionsQuotientProjApp (X : Scheme.{u})
    (A : Type v) [AddCommGroup A]
    (hclosed : ∀ x : X, IsClosed ({x} : Set X))
    (hsep : ∀ x : X, IsSepClosed (X.residueField x))
    (U : X.ProEt) [IsAffine U.left] :
    Function.Surjective (pointFunctionsQuotientProjApp.{u, v} X A U) := by
  let : WeaklyEtale U.hom := U.prop
  let D := AddCommGrpCat.{max (u + 1) v}
  let J := Scheme.ProEt.topology U.left
  let K := Scheme.ProEt.topology X
  let g := proetalePostcompose U.hom
  let : g.IsContinuous J K := proetalePostcompose_isContinuous U.hom
  let : g.IsCocontinuous J K := isCocontinuous_proetalePostcompose U.hom
  let R := g.sheafPushforwardContinuous D J K
  let : R.IsLeftAdjoint := (g.sheafAdjunctionCocontinuous D J K).isLeftAdjoint
  let : R.IsRightAdjoint := (g.sheafAdjunctionContinuous D J K).isRightAdjoint
  let : R.Additive := ⟨rfl⟩
  have hS := pointFunctionsShortComplex_shortExact X A
  have := hS.mono_f
  have := hS.epi_g
  let T := (pointFunctionsShortComplex X A).map R
  have hT : T.ShortExact := hS.map R
  let F := (constantSheaf J D).obj (pointFunctionsCoeff.{u} A)
  let e : F ≅ T.X₁ := (g.pushforwardContinuousSheafificationCompatibility D J K).app
    ((Functor.const (X.ProEt)ᵒᵖ).obj (pointFunctionsCoeff.{u} A))
  have : Subsingleton (Sheaf.H.{max (u + 1) v} F 1) :=
    subsingleton_proetaleH_one_constantSheaf X A hclosed hsep U
  let : Subsingleton ((Sheaf.functorH.{max (u + 1) v} J 1).obj F) :=
    inferInstanceAs (Subsingleton (Sheaf.H.{max (u + 1) v} F 1))
  have : Subsingleton (Sheaf.H.{max (u + 1) v} T.X₁ 1) :=
    ((Sheaf.functorH.{max (u + 1) v} J 1).mapIso e).symm.addCommGroupIsoToAddEquiv.toEquiv
      |>.subsingleton
  let : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ ↦ inferInstance⟩
  let V : U.left.ProEt := Scheme.ProEt.mk (𝟙 U.left)
  have hV : IsTerminal V :=
    MorphismProperty.Over.mkIdTerminal (@WeaklyEtale : MorphismProperty Scheme.{u}) U.left
  let i : g.obj V ≅ U := MorphismProperty.Over.isoMk (Iso.refl _) (by
    show U.hom = 𝟙 U.left ≫ U.hom
    exact (Category.id_comp _).symm)
  intro s
  obtain ⟨t, ht⟩ := surjective_app_of_subsingleton_H_one J hV T hT
    ((pointFunctionsQuotient X A).obj.map i.hom.op s)
  refine ⟨(pointFunctionsSheaf X A).obj.map i.inv.op t, ?_⟩
  have hnat := congrArg (fun k => k t)
    (congrArg AddCommGrpCat.Hom.hom ((pointFunctionsQuotientProj X A).hom.naturality i.inv.op))
  show (pointFunctionsQuotientProj X A).hom.app (op U)
    ((pointFunctionsSheaf X A).obj.map i.inv.op t) = s
  refine (hnat.trans ?_)
  show (pointFunctionsQuotient X A).obj.map i.inv.op
    ((pointFunctionsQuotientProj X A).hom.app (op (g.obj V)) t) = s
  rw [show (pointFunctionsQuotientProj X A).hom.app (op (g.obj V)) t =
    (pointFunctionsQuotient X A).obj.map i.hom.op s from ht]
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp,
    Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **`F(U) = fun(U, A)/A(U)`** for an affine object `U` of the small pro-étale site of a scheme
`X` all of whose points are closed with separably closed residue fields: the projection
`fun(U, A) ⟶ F(U)` is surjective with kernel the constant sections `A(U)`. -/
@[stacks 0F6D "`F(U) = fun(U, A)/A(U)` for affine `U`, when all points of `X` are closed with \
separably closed residue fields"]
def pointFunctionsQuotientAppEquiv (X : Scheme.{u})
    (A : Type v) [AddCommGroup A]
    (hclosed : ∀ x : X, IsClosed ({x} : Set X))
    (hsep : ∀ x : X, IsSepClosed (X.residueField x))
    (U : X.ProEt) [IsAffine U.left] :
    (U.left → ULift.{max (u + 1) v} A) ⧸ (constantToPointFunctionsApp.{u, v} X A U).range ≃+
      (pointFunctionsQuotient.{u, v} X A).obj.obj (op U) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_pointFunctionsQuotientProjApp X A U).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_pointFunctionsQuotientProjApp X A hclosed hsep U))

/-- **`F` is not pulled back from the étale site.** If `X` is nonempty and `A` has more than one
element, the quotient `F = fun(-, A)/A` is not in the essential image of `ε⁻¹`: since
`Rε_*ε⁻¹ℱ = ℱ` for abelian sheaves `ℱ` on `X_étale` (Stacks 099V (1),
`AlgebraicGeometry.ProEtale.isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage`), the
essential image of `ε⁻¹` is closed under extensions, `A = ε⁻¹A`, and `fun(-, A)` is not in it. -/
@[stacks 0F6D "if `A` has more than one element, the quotient `F` is not pulled back from the \
étale site (for `X` nonempty)"]
theorem not_etalePullback_pointFunctionsQuotient (X : Scheme.{u}) (A : Type v)
    [AddCommGroup A] (hX : Nonempty X) (hA : Nontrivial A) :
    ¬ (epsilonInverseImage.{u, v} X).essImage (pointFunctionsQuotient X A) := by
  intro h₃
  apply not_etalePullback_pointFunctionsSheaf X A hX hA
  have hε : ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      IsIso ((epsilonAdjunction.{u, v} X).unit.app F) ∧
        ∀ q : ℕ, 0 < q → IsZero (((epsilonDirectImage.{u, v} X).rightDerived q).obj
          ((epsilonInverseImage.{u, v} X).obj F)) :=
    isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage.{v, u} X
  let L := epsilonInverseImage.{u, v} X
  let R := epsilonDirectImage.{u, v} X
  let adj := epsilonAdjunction.{u, v} X
  let S := pointFunctionsShortComplex X A
  have hS : S.ShortExact := pointFunctionsShortComplex_shortExact X A
  have : ∀ F, IsIso (adj.unit.app F) := fun F ↦ (hε F).1
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have : L.Full := adj.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : R.IsRightAdjoint := adj.isRightAdjoint
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  let e₁ : L.obj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (pointFunctionsCoeff.{u} A)) ≅ S.X₁ :=
    (constantSheafCompEpsilonInverseImageIsoConstantSheaf.{u, v} X).app _
  have h₁ : L.essImage S.X₁ := ⟨_, ⟨e₁⟩⟩
  have hR₁ : IsZero ((R.rightDerived 1).obj S.X₁) :=
    ((hε _).2 1 one_pos).of_iso ((R.rightDerived 1).mapIso e₁).symm
  have hR : (S.map R).ShortExact :=
    Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one R hS hR₁
  let φ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  have : IsIso φ.τ₁ := (adj.isIso_counit_app_iff_mem_essImage).2 h₁
  have : IsIso φ.τ₃ := (adj.isIso_counit_app_iff_mem_essImage).2 h₃
  have : Mono S.f := hS.mono_f
  have : Epi (S.map R).g := hR.epi_g
  have : Mono ((S.map R).map L).f := by
    have : Mono (((S.map R).map L).f ≫ φ.τ₂) := by
      rw [← φ.comm₁₂]
      infer_instance
    exact mono_of_mono _ φ.τ₂
  have hLR : ((S.map R).map L).ShortExact :=
    ShortComplex.ShortExact.mk'
      (hR.exact.map_of_epi_of_preservesCokernel L inferInstance inferInstance)
      inferInstance (by
        have := Functor.preservesEpimorphisms_of_isLeftAdjoint L
        exact L.map_epi (S.map R).g)
  have : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hLR hS
  exact ⟨R.obj S.X₂, ⟨asIso φ.τ₂⟩⟩

end AlgebraicGeometry.ProEtale

end
