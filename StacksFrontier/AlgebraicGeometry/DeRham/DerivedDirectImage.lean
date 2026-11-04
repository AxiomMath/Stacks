module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedScalarRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.DerivedDirectImageComposition
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of the relative de Rham complex

Let `p : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. The relative de Rham
complex `Ω^•_{X/S}` is a complex of sheaves of `p^{-1}𝒪_S`-modules on `X`, so its direct image
is taken along the morphism of ringed spaces `(X, p^{-1}𝒪_S) ⟶ (S, 𝒪_S)` and lands in the
`𝒪_S`-modules. This file shows that the resulting object `Rp_*Ω^•_{X/S}` of `D⁺(𝒪_S)` lies in
`D_QCoh(𝒪_S)`: all of its cohomology sheaves are quasi-coherent.

The argument is the one of the source. The de Rham complex is bounded below, so a
Cartan--Eilenberg resolution gives a spectral sequence with first page `R^b p_*Ω^a_{X/S}`
converging to the cohomology of `Rp_*Ω^•_{X/S}`; quasi-coherent modules form a weak Serre
subcategory, so it suffices that each `R^b p_*Ω^a_{X/S}` be quasi-coherent, and that is the
quasi-coherence of the higher direct images of a quasi-coherent module together with the
quasi-coherence of the sheaves of relative differential forms.

## Main definitions

* `Stacks.DeRhamDirectImage.inverseImageBase`: the ringed space `(X, p^{-1}𝒪_S)`, together with
  its projection to `S` and the identity-on-spaces morphism from `(X, 𝒪_X)`.
* `Stacks.DeRhamDirectImage.relativePushforward`: the direct image
  `Mod(p^{-1}𝒪_S) ⥤ Mod(𝒪_S)`.
* `Stacks.DeRhamDirectImage.derivedDeRhamDirectImage`: **`Rp_*Ω^•_{X/S}`**, an object of
  `D⁺(𝒪_S)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`: the sheaf
  `Ω^n_{X/S}` of relative differential `n`-forms is quasi-coherent, in every degree.
* `Stacks.DeRhamDirectImage.relativePushforwardHigherIso`: the higher direct images of an
  `𝒪_X`-module computed in `Mod(p^{-1}𝒪_S)` are the usual ones; with
  `Stacks.DeRhamDirectImage.isQuasicoherent_relativePushforward_higher` this transports the
  quasi-coherence of `R^q p_*` across the two readings of the coefficients.
* `Stacks.DeRhamDirectImage.weakSerre_homology_total`: a weak Serre subcategory which contains
  the columnwise cohomology of a diagonally finite double complex contains the cohomology of
  its total complex.
* `Stacks.DeRhamDirectImage.isQuasicoherent_homology_derivedDeRhamDirectImage` and
  `Stacks.DeRhamDirectImage.derivedCategoryB_derivedDeRhamDirectImage`: **Tag 0FLX**, in its
  degreewise and its membership form.

## Implementation notes

The de Rham differential is only `p^{-1}𝒪_S`-linear, so the terms of `Ω^•_{X/S}` appear as
restrictions of scalars of the `𝒪_X`-modules `Ω^n_{X/S}` along `p^{-1}𝒪_S ⟶ 𝒪_X`. The
comparison with the direct image of `𝒪_X`-modules — where quasi-coherence of the higher direct
images is available — is made by factoring the underlying morphism of ringed spaces as
`(X, 𝒪_X) ⟶ (X, p^{-1}𝒪_S) ⟶ (S, 𝒪_S)`, the first factor being the identity on spaces and
restriction of scalars on modules. Leray's composition isomorphism for the two factors then
identifies `R^q` of the second factor, applied to a restriction of scalars, with `R^q p_*`,
because the first factor is exact and so contributes nothing to the derived functor.

That factorization is proved as `Stacks.DeRhamDirectImage.toInverseImageBase_comp`, and it is
used through `Stacks.DeRhamDirectImage.relativePushforwardHigherIsoOfFactors`, which takes the
factorization as a hypothesis on a variable morphism and substitutes it. Rewriting with the
equality of the two direct image functors instead is not possible: those functors carry an
additivity instance whose type mentions the functor, so the rewrite motive is not type correct.
Substituting a variable avoids the dependency, and the two spellings `pushforward p^♯` and
`AlgebraicGeometry.Scheme.Modules.pushforward p` of the direct image on `𝒪_X`-modules are then
crossed by unification, where they are definitionally equal.

Likewise the factorization itself is proved through `AlgebraicGeometry.PresheafedSpace.hext`
rather than the `ext` lemma: the base maps of the two sides are `𝟙 ≫ p` and `p`, which are
definitionally but not syntactically equal, and the `ext` lemma inserts an `eqToHom` along the
proof of their equality which nothing then removes. The heterogeneous form asks instead for an
equality of the structure maps up to that definitional identification.

The three spellings of the category of modules on a ringed space in this library are
definitionally equal and carry separately declared instances. `Stacks.DeRhamDirectImage` works
in the spelling of `StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`, which is the one
Leray's composition isomorphism is stated for; the abelian structure, the Grothendieck axioms
and the existence of enough injectives are restated there as local instances, instance search
not crossing the abbreviation on its own. The derived categories are those of
`CategoryTheory.HasDerivedCategory.standard`, whose priority is raised for the file: the
quasi-coherence of the higher direct images is baked at that model, and the locally small model
arrives with the imports as a competing instance of the same priority.

## References

* [Stacks Project, Tag 0FLX](https://stacks.math.columbia.edu/tag/0FLX)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedDirectImageComposition

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace CategoryTheory.Functor

/-- **The total right derived functor of an exact functor is the functor itself**, on an object
placed in degree zero: `RF(M[0]) ≅ (F M)[0]`. A homology-preserving functor inverts
quasi-isomorphisms already on the homotopy category, so the unit of its right derived functor is
invertible and no resolution intervenes. -/
def objSingleIsoOfPreservesHomology {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [EnoughInjectives A] {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] [F.PreservesHomology] (M : A) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj M) := by
  have hu : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) :=
    (NatTrans.isIso_iff_isIso_app _).mp
      (F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology) _
  refine F.rightDerivedFunctorPlus.mapIso
    ((Functor.singleFunctorPlusIsoCompQh 0).app M) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M))).symm ≪≫ ?_
  exact DerivedCategory.Plus.ι.preimageIso
    (DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
        ((CochainComplex.singleFunctor A 0).obj M)) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _ ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Quasi-coherence of the sheaves of relative differential forms -/

/-- **The sheaf `Ω^n_{X/S}` of relative differential `n`-forms is quasi-coherent**, in every
degree and with no hypothesis on the morphism. This is the per-degree form of the exterior-algebra
clause of [Stacks, Tag 01CL]: the sheaf of relative differentials is quasi-coherent, and a cover
presenting it presents each of its exterior powers over the same opens, so the quasi-coherent data
of `Ω_{X/S}` transfer to `Ω^n_{X/S}` without shrinking the cover. -/
theorem isQuasicoherent_relativeDifferentialForms (n : ℕ) :
    (relativeDifferentialForms f (n : ℤ)).IsQuasicoherent := by
  obtain ⟨c⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
    (M := relativeDifferentials f)
  refine _root_.SheafOfModules.QuasicoherentData.isQuasicoherent
    (M := relativeDifferentialForms f (n : ℤ))
    { I := c.I
      X := c.X
      coversTop := c.coversTop
      presentation := fun i => ?_ }
  exact (Stacks.SheafOfModules.nonempty_presentation_exteriorPower_over (c.X i)
    (relativeDifferentials f) (deRhamAlgebras f) (c.presentation i) n).some

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRhamDirectImage

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The intermediate ringed space -/

/-- The ringed space `(X, f^{-1}𝒪_S)`: the space of `X` equipped with the inverse image of the
structure sheaf of the base. This is where the relative de Rham complex lives. -/
abbrev inverseImageBase : RingedSpace.{u} :=
  RingedSpace.inverseImage S.toRingedSpace f.base

/-- The projection `(X, f^{-1}𝒪_S) ⟶ S`: the morphism of ringed spaces with underlying map that
of `f` and structure map the unit `𝒪_S ⟶ f_*f^{-1}𝒪_S`. -/
abbrev inverseImageBaseProjection : inverseImageBase f ⟶ S.toRingedSpace :=
  RingedSpace.inverseImageProjection S.toRingedSpace f.base

/-- The morphism of ringed spaces `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)`: the identity on spaces, with
structure map the structural `f^{-1}𝒪_S ⟶ 𝒪_X`. -/
def toInverseImageBase : X.toRingedSpace ⟶ inverseImageBase f :=
  InducedCategory.homMk
    { base := 𝟙 X.carrier
      c := (inverseImageStructureMap f).hom }

/-- **The morphism of ringed spaces underlying `f` factors through `(X, f^{-1}𝒪_S)`.** The
structure map of the composite is the unit followed by the direct image of the structural map,
which is `f^♯` by the defining adjunction property of the latter. -/
theorem toInverseImageBase_comp :
    toInverseImageBase f ≫ inverseImageBaseProjection f = f.toLRSHom.toShHom := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv
    S.sheaf X.sheaf |>.apply_symm_apply
      (⟨f.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)
  exact congrArg (fun t => t.hom) h

/-- **Pushforward along `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` is restriction of scalars** along
`f^{-1}𝒪_S ⟶ 𝒪_X`, the underlying map of spaces being the identity. -/
theorem pushforward_toInverseImageBase :
    pushforward (toInverseImageBase f) =
      _root_.SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
          (inverseImageStructureMap f)) :=
  rfl

/-- Restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` is left exact: it does not change the
underlying sheaf of abelian groups. -/
instance preservesFiniteLimits_pushforward_toInverseImageBase :
    PreservesFiniteLimits (pushforward (toInverseImageBase f)) :=
  (Scheme.Hom.exactFunctor_scalarRestriction f).1

/-- Restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` is right exact: it does not change the
underlying sheaf of abelian groups. -/
instance preservesFiniteColimits_pushforward_toInverseImageBase :
    PreservesFiniteColimits (pushforward (toInverseImageBase f)) :=
  (Scheme.Hom.exactFunctor_scalarRestriction f).2

/-- Sheaves of modules on a ringed space form an abelian category. Instance search does not
cross the abbreviation, so the instance is restated at these binders. Both universes are the
universe of the schemes in this file. -/
local instance abelian_modules (Y : RingedSpace.{u, u}) : Abelian (Modules Y) :=
  _root_.AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules _

/-- Sheaves of modules on a ringed space form a Grothendieck abelian category. -/
local instance isGrothendieckAbelian_modules (Y : RingedSpace.{u, u}) :
    IsGrothendieckAbelian.{u} (Modules Y) :=
  _root_.SheafOfModules.instIsGrothendieckAbelian _

/-- **The direct image of `f^{-1}𝒪_S`-modules along `f`**, `Mod(f^{-1}𝒪_S) ⥤ Mod(𝒪_S)`: the
pushforward along the projection `(X, f^{-1}𝒪_S) ⟶ S`. Its right derived functor is the `Rp_*`
in which the de Rham complex is pushed forward. -/
abbrev relativePushforward : Modules (inverseImageBase f) ⥤ Modules S.toRingedSpace :=
  pushforward (inverseImageBaseProjection f)

/-- **Transfer of the higher direct images across the two spellings**, in the form in which the
factorization of `f` is a hypothesis rather than a rewrite: Leray's composition isomorphism for
`(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S) ⟶ S`, with the first factor exact, so that it contributes nothing
beyond restriction of scalars. -/
def relativePushforwardHigherIsoOfFactors (g : X.toRingedSpace ⟶ S.toRingedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g) (M : X.Modules) (q : ℤ) :
    ((relativePushforward f).rightDerivedPlus q).obj
        ((pushforward (toInverseImageBase f)).obj M) ≅
      ((pushforward g).rightDerivedPlus q).obj M := by
  subst hg
  exact (DerivedCategory.Plus.homologyFunctor S.Modules q).mapIso
    (((pushforward (inverseImageBaseProjection f)).rightDerivedFunctorPlus.mapIso
        ((pushforward (toInverseImageBase f)).objSingleIsoOfPreservesHomology M)).symm ≪≫
      (higherDirectImagesCompIso (toInverseImageBase f) (inverseImageBaseProjection f)).app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))

/-- **The higher direct images of an `𝒪_X`-module are unchanged when its coefficients are
restricted to `f^{-1}𝒪_S`**: computing `R^q` of the direct image of `f^{-1}𝒪_S`-modules on the
restriction of scalars of `M` gives `R^q f_*M`. -/
def relativePushforwardHigherIso (M : X.Modules) (q : ℤ) :
    ((relativePushforward f).rightDerivedPlus q).obj
        ((pushforward (toInverseImageBase f)).obj M) ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus q).obj M :=
  relativePushforwardHigherIsoOfFactors f _ (toInverseImageBase_comp f) M q

/-- **The higher direct images of a quasi-coherent `𝒪_X`-module, taken in `Mod(f^{-1}𝒪_S)`, are
quasi-coherent.** By the comparison above they are the usual higher direct images, which are
quasi-coherent along a quasi-compact and quasi-separated morphism by [Stacks, Tag 01XJ]. -/
theorem isQuasicoherent_relativePushforward_higher [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) (hM : M.IsQuasicoherent) (q : ℤ) :
    (((relativePushforward f).rightDerivedPlus q).obj
      ((pushforward (toInverseImageBase f)).obj M)).IsQuasicoherent := by
  have : M.IsQuasicoherent := hM
  exact (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (relativePushforwardHigherIso f M q).symm
    (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage f M q)

/-! ### The spectral sequence of the total complex -/

/-- **A weak Serre subcategory containing the columnwise cohomology of a diagonally finite
double complex contains the cohomology of its total complex**, by the first spectral sequence
of the total complex. -/
theorem weakSerre_homology_total {C : Type*} [Category* C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (hK : ∀ n : ℤ,
      {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q, P ((K.X p).homology q)) (n : ℤ) :
    P ((K.total (ComplexShape.up ℤ)).homology n) := by
  let L := K.totalFiltration₁
  let F := fun p n => Subobject.mk ((L.filtration.ι.app (.op p)).f n)
  let Z := FilteredComplexSpectralSequence.cycles L.X F
  let D := FilteredComplexSpectralSequence.boundaries L.X F
  obtain ⟨E, e, α, hδ, -⟩ := CochainComplex.exists_cohomologicalSpectralSequence
    L F (fun _ _ => rfl) Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl)
  obtain ⟨β, -⟩ := (K.exists_iso_pages_totalFiltration₁ F (fun _ _ => rfl)
    Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl) E e hδ).2.1
  exact (K.isBounded_and_converges_totalFiltration₁ hK F (fun _ _ => rfl)
    Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl)
    (fun n p => imageSubobject (HomologicalComplex.homologyMap
      (L.filtration.ι.app (.op p)) n)) (fun _ _ => rfl) E e).2.2.2.2
    P 1 zero_le_one (fun p q => P.prop_of_iso (β p q).symm (hP p q)) n

/-! ### The derived direct image of the relative de Rham complex -/

/-- The relative de Rham complex `Ω^•_{X/S}`, extended by zero to a `ℤ`-indexed cochain complex
of `f^{-1}𝒪_S`-modules, which is the indexing the derived category uses. -/
abbrev deRhamCochainComplex : CochainComplex (Modules (inverseImageBase f)) ℤ :=
  (show CochainComplex (Modules (inverseImageBase f)) ℕ from
    Scheme.Hom.deRhamComplex f).extend ComplexShape.embeddingUpNat

/-- The extended de Rham complex is concentrated in nonnegative degrees. -/
instance isStrictlyGE_deRhamCochainComplex : (deRhamCochainComplex f).IsStrictlyGE 0 where
  isZero i hi := HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
    (fun n => by simpa using hi n)

/-- **`Rp_*Ω^•_{X/S}`**, the derived direct image of the relative de Rham complex: an object of
`D⁺(𝒪_S)`. The direct image is the one of `f^{-1}𝒪_S`-modules, which is where the de Rham
complex lives, and the de Rham complex is concentrated in nonnegative degrees. -/
def derivedDeRhamDirectImage : DerivedCategory.Plus (Modules S.toRingedSpace) :=
  (relativePushforward f).rightDerivedFunctorPlus.obj
    (DerivedCategory.Plus.Q.obj ⟨deRhamCochainComplex f, 0, inferInstance⟩)

/-- **Stacks Project, Tag 0FLX.** For a quasi-compact and quasi-separated morphism of schemes
`p : X ⟶ S` the derived direct image `Rp_*Ω^•_{X/S}` of the relative de Rham complex is an
object of `D_QCoh(𝒪_S)`: every one of its cohomology sheaves is quasi-coherent. -/
@[stacks 0FLX]
theorem isQuasicoherent_homology_derivedDeRhamDirectImage [QuasiCompact f] [QuasiSeparated f]
    (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor S.Modules i).obj
      (derivedDeRhamDirectImage f)).IsQuasicoherent := by
  let F := relativePushforward f
  let K := deRhamCochainComplex f
  obtain ⟨I, hI⟩ := CochainComplex.exists_cartanEilenbergResolution K 0
  have := hI
  let L := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I.bicomplex
  have hp (a : ℤ) (ha : a < 0) : IsZero (L.X a) :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex 0 a ha)
  have hq (a b : ℤ) (hb : b < 0) : IsZero ((L.X a).X b) :=
    F.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X a) 0 b hb)
  have hfinite := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded L 0 hq hp
  have : HomologicalComplex₂.HasTotal L (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ hfinite
  have hSS := I.exists_homologyIso_rightDerivedPlus F ⟨0, inferInstance⟩
  -- The columns `L.X a` live in `Modules S.toRingedSpace`, that is over
  -- `Stacks.SheafOfModules.Tensor.ringSheaf S.toRingedSpace.sheaf`, where the abelian and weak
  -- Serre instances are reachable. `AlgebraicGeometry.Scheme.ringCatSheaf` is the same sheaf of
  -- rings only after unfolding that definition, which instance search will not do, so the
  -- property is named at the spelling the columns are stated at.
  let P := _root_.SheafOfModules.isQuasicoherent (ringCatSheaf S.toRingedSpace)
  have : P.IsWeakSerreClass :=
    Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass S
  have hcol (a b : ℤ) : P ((L.X a).homology b) := by
    by_cases ha : 0 ≤ a
    · obtain ⟨e, -⟩ := hSS.1 b
      refine P.prop_of_iso (e a).symm ?_
      lift a to ℕ using ha
      refine P.prop_of_iso ((F.rightDerivedPlus b).mapIso
        ((show CochainComplex (Modules (inverseImageBase f)) ℕ from
            Scheme.Hom.deRhamComplex f).extendXIso
          ComplexShape.embeddingUpNat (i := a) rfl)).symm ?_
      rw [Scheme.Hom.deRhamComplex_X]
      exact isQuasicoherent_relativePushforward_higher f _
        (Scheme.Hom.isQuasicoherent_relativeDifferentialForms f a) b
    · exact P.prop_of_isZero
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) b).map_isZero
          (hp a (lt_of_not_ge ha)))
  obtain ⟨e⟩ := hSS.2.2 i
  exact P.prop_of_iso e (weakSerre_homology_total L hfinite P hcol i)

/-- **Stacks Project, Tag 0FLX.** `Rp_*Ω^•_{X/S}` is an object of `D_QCoh(𝒪_S)`, in the
membership form: the object property on `D(𝒪_S)` cutting out the complexes with quasi-coherent
cohomology holds of it. Since `AlgebraicGeometry.Scheme.Hom.deRhamComplex` is bounded below, the
derived direct image is read in `D⁺(𝒪_S)` and compared with `D(𝒪_S)` along the inclusion, under
which the cohomology functors agree. -/
@[stacks 0FLX]
theorem derivedCategoryB_derivedDeRhamDirectImage [QuasiCompact f] [QuasiSeparated f] :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf)
      (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f)) :=
  fun i => isQuasicoherent_homology_derivedDeRhamDirectImage f i

end Stacks.DeRhamDirectImage

end
