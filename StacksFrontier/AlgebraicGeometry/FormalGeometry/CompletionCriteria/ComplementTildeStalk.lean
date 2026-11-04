module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.TildeStalkPrime
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# The stalks on the open complement of the sheaf associated to a module

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. For an `A`-module `N` the quasi-coherent
sheaf `Ñ` on `X` restricts to a sheaf `Ñ|_U` of `𝒪_U`-modules, and this file computes its stalks:
at a point `y` of `U` lying over the prime `𝔭 ⊆ A`, the stalk of `Ñ|_U` at `y` is the
localization `N_𝔭`, semilinearly over the identification `𝒪_{U,y} ≅ A_𝔭` of the local ring of `U`
at `y` with the localization of `A` at `𝔭`.

The computation is a composite of two identifications, which between them account for the two
halves of that identification of rings.

* Restricting to an open does not change a stalk: the stalk of `Ñ|_U` at `y` is the stalk of `Ñ`
  at the image of `y` in `X`, semilinearly over `𝒪_{U,y} ≅ 𝒪_{X,𝔭}`. That identification of
  local rings is inverse to the stalk map of the open immersion `U ⟶ X`, over which the
  comparison of stalks of modules is semilinear.
* On an affine scheme the stalk of `M̃` at a prime `𝔭` is the localization `M_𝔭`, because the germ
  map `M → M̃_𝔭` is a localization of modules at the complement of `𝔭`. That identification is
  linear over the base ring, while the two rings acting are the local ring `𝒪_{Spec R, 𝔭}` and
  `R_𝔭`, both localizations of `R` at the complement of `𝔭`; and an additive bijection between
  modules over two such localizations which is linear over `R` is automatically semilinear over
  the canonical isomorphism of the two localizations.

## Main definitions

* `Stacks.Algebraization.tildeStalkAddEquiv` — on an affine scheme, the stalk of `M̃` at a prime
  `𝔭` is the localization `M_𝔭`, as an additive equivalence; this is
  `AlgebraicGeometry.tildeStalkLinearEquiv` with its linearity over the base ring forgotten.
* `Stacks.Algebraization.openStalkRingEquiv` — the local ring of `U` at `y` is the local ring of
  `X` at the prime under `y`, as a ring isomorphism.
* `Stacks.Algebraization.complementTildeStalkAddEquiv` — the stalk of `Ñ|_U` at `y` is the stalk
  of `Ñ` at the prime under `y`.
* `Stacks.Algebraization.modulesStalkComplementTildeAddEquiv` — the composite of the two: the
  stalk of `Ñ|_U` at `y` is `N_𝔭`.

## Main results

* `Stacks.Algebraization.smul_eq_of_isLocalization` — an additive bijection from a module over a
  ring receiving `A` to a module over a localization of `A`, linear over `A`, is semilinear over
  any isomorphism of those two rings commuting with the maps from `A`.
* `Stacks.Algebraization.tildeStalkAddEquiv_smul` and
  `Stacks.Algebraization.complementTildeStalkAddEquiv_smul` — the semilinearity of the two
  halves, over `AlgebraicGeometry.Spec.stalkIso` and over
  `AlgebraicGeometry.Scheme.Opens.stalkIso` respectively.
* `Stacks.Algebraization.modulesStalkComplementTildeAddEquiv_smul` — the composite
  identification is semilinear over `Stacks.Algebraization.pointStalkRingEquiv`, which is the
  composite of those two isomorphisms of rings.
* `Stacks.Algebraization.nonempty_semilinearEquiv_modulesStalk_complementTilde` — **the stalk of
  `Ñ|_U` at `y` is `N_𝔭`**, as an equivalence semilinear over
  `Stacks.Algebraization.pointStalkRingEquiv`.
* `Stacks.Algebraization.exists_addEquiv_modulesStalk_complementTilde` — the same statement with
  the semilinear equivalence unbundled into an additive equivalence and its compatibility with
  the two scalar actions.

## Implementation notes

Only one of the two localizations is used as such in the proof of semilinearity: an element of
the local ring `𝒪_{Spec R, 𝔭}` is carried over by the ring isomorphism and written as a fraction
in `R_𝔭`, so no localization instance on the stalk itself is needed, and the hypothesis of
`Stacks.Algebraization.smul_eq_of_isLocalization` is correspondingly one-sided.

A point of `Spec R` can be spelled either as a point of the underlying space or as a prime ideal
of `R`, and the two spellings agree only after unfolding `Spec`, which instance resolution does
not do. The module structure of the stalk of a module on a scheme over the stalk of the structure
sheaf is indexed by the first spelling, and the `tilde` construction by the second, so the two
cannot be mixed in one statement; `Stacks.Algebraization.tildeStalkModule` is the former read at
the latter spelling, and is a local instance, Mathlib's being the global one. For the same reason
the statements below name the point of `X` under `y` as `S.U.ι.base y` rather than as
`Stacks.Algebraization.underlyingPrime S y`: the two are definitionally equal, but a stalk at one
and a stalk at the other are identified only through the colimit defining the stalk, which is
expensive.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (3).
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-! ### Semilinearity of a map which is linear over the base -/

/-- **An additive bijection which is linear over the base is semilinear over the localizations.**
Let `B` and `C` be rings receiving `A`, with `C` a localization of `A` at a submonoid `q`, let
`σ : B ≃+* C` be an isomorphism commuting with the two maps from `A`, and let `e : M ≃+ P` be an
additive bijection from a `B`-module to a `C`-module which is linear for the two actions of `A`.
Then `e` is semilinear over `σ`.

An element `b` of `B` has `σ b = r / s` with `s ∈ q`; multiplying by the image of `s`, which is a
unit of `C` and therefore acts invertibly on `P`, reduces the identity to the assumed
`A`-linearity. Note that `B` itself is not assumed to be a localization of `A`: the presentation
of `σ b` as a fraction is read off in `C` and transported back along `σ`. -/
theorem smul_eq_of_isLocalization {A : Type u} [CommRing A] {q : Submonoid A}
    {B : Type*} [CommRing B] {C : Type*} [CommRing C] [Algebra A C] [IsLocalization q C]
    {M : Type*} [AddCommGroup M] [Module B M] {P : Type*} [AddCommGroup P] [Module C P]
    (gB : A →+* B) (σ : B ≃+* C) (hσ : ∀ a : A, σ (gB a) = algebraMap A C a)
    (e : M ≃+ P) (he : ∀ (a : A) (m : M), e (gB a • m) = algebraMap A C a • e m)
    (b : B) (m : M) : e (b • m) = σ b • e m := by
  obtain ⟨r, s, hrs⟩ := IsLocalization.exists_mk'_eq q (σ b)
  have hsb : gB (s : A) * b = gB r := by
    refine σ.injective ?_
    rw [map_mul, hσ, hσ, ← hrs]
    exact IsLocalization.mk'_spec' C r s
  have hL : algebraMap A C (s : A) • e (b • m) = algebraMap A C r • e m := by
    rw [← he (s : A) (b • m), ← mul_smul, hsb]
    exact he r m
  have hR : algebraMap A C (s : A) • (σ b • e m) = algebraMap A C r • e m := by
    rw [smul_smul, ← hσ (s : A), ← map_mul, hsb, hσ]
  exact (IsLocalization.map_units C s).smul_left_cancel.mp (hL.trans hR.symm)

/-! ### The stalk of `M̃` at a prime of an affine scheme -/

/-- The stalk of `M̃` at a prime `𝔭` of `R` is a module over the local ring of `Spec R` at `𝔭`.
This is the module structure carried by the stalk of any module on a scheme, with the point of
`Spec R` spelled as a prime ideal of `R`, which is the spelling the `tilde` construction uses. -/
@[instance_reducible]
def tildeStalkModule {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (x : PrimeSpectrum R) :
    Module ↑((Spec R).presheaf.stalk x) ↑((AlgebraicGeometry.tilde M).presheaf.stalk x) :=
  Scheme.Modules.instModuleStalk (AlgebraicGeometry.tilde M) x

attribute [local instance] tildeStalkModule

section Tilde

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (x : PrimeSpectrum R)

/-- **The stalk of `M̃` at a prime `𝔭` is the localization `M_𝔭`**, as an additive equivalence.
This is `AlgebraicGeometry.tildeStalkLinearEquiv`, which states the same identification as an
`R`-linear equivalence in the other direction, with its linearity forgotten; the semilinearity
over the local ring of `Spec R` at `𝔭` is recovered below. -/
def tildeStalkAddEquiv :
    ↑((AlgebraicGeometry.tilde M).presheaf.stalk x) ≃+
      LocalizedModule x.asIdeal.primeCompl (M : Type u) :=
  (AlgebraicGeometry.tildeStalkLinearEquiv M x).symm.toAddEquiv

/-- **The identification of the local ring of `Spec R` at `𝔭` with `R_𝔭` commutes with the two
maps from `R`**: the structure map of the stalk is the germ at `𝔭` of the image of an element of
`R` in the global sections, and the identification carries it to the localization map. -/
theorem specStalkIso_toStalk (a : ↑R) :
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv ((StructureSheaf.toStalk R x).hom a) =
      algebraMap ↑R (Localization.AtPrime x.asIdeal) a := by
  have h : CommRingCat.ofHom (algebraMap ↑R (Localization.AtPrime x.asIdeal)) ≫
      (Spec.stalkIso R x).inv = StructureSheaf.toStalk R x := by
    rw [Spec.algebraMap_stalkIso_inv, Scheme.ΓSpecIso_inv]
    exact StructureSheaf.algebraMap_germ ⊤ x trivial
  have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a
  exact (congrArg (fun t => (Spec.stalkIso R x).commRingCatIsoToRingEquiv t) h2.symm).trans
    ((Spec.stalkIso R x).commRingCatIsoToRingEquiv.apply_symm_apply _)

/-- **The identification of the stalk of `M̃` at `𝔭` with `M_𝔭` is semilinear** over the
identification `𝒪_{Spec R, 𝔭} ≅ R_𝔭` of rings.

The identification is `R`-linear, and the `R`-actions on both sides are the restrictions of the
actions of the two localizations along their maps from `R`, so
`Stacks.Algebraization.smul_eq_of_isLocalization` applies. -/
theorem tildeStalkAddEquiv_smul (b : ↑((Spec R).presheaf.stalk x))
    (m : ↑((AlgebraicGeometry.tilde M).presheaf.stalk x)) :
    tildeStalkAddEquiv M x (b • m) =
      (Spec.stalkIso R x).commRingCatIsoToRingEquiv b • tildeStalkAddEquiv M x m := by
  refine smul_eq_of_isLocalization (q := x.asIdeal.primeCompl)
    (show ↑R →+* ↑((Spec R).presheaf.stalk x) from (StructureSheaf.toStalk R x).hom) _
    (specStalkIso_toStalk x) (tildeStalkAddEquiv M x) (fun a m => ?_) b m
  have h1 : (show ↑R →+* ↑((Spec R).presheaf.stalk x) from
      (StructureSheaf.toStalk R x).hom) a • m = a • m := rfl
  have h2 : tildeStalkAddEquiv M x (a • m) = a • tildeStalkAddEquiv M x m :=
    (AlgebraicGeometry.tildeStalkLinearEquiv M x).symm.map_smul a m
  rw [h1, h2, IsScalarTower.algebraMap_smul]

end Tilde

/-! ### The stalk of `Ñ|_U` on the open complement -/

section Complement

variable (S : AlgebraizationSituation.{u}) (N : ModuleCat.{u} S.A) (y : S.U.toScheme)

/-- **The local ring of `U` at `y` is the local ring of `X` at the prime under `y`**, as a ring
isomorphism. It is `Stacks.Algebraization.pointStalkRingEquiv` with its second half, the
identification of the local ring of `X` with a localization of `A`, left off. -/
def openStalkRingEquiv :
    ↑(S.U.toScheme.presheaf.stalk y) ≃+* ↑(S.X.presheaf.stalk (S.U.ι.base y)) :=
  (Scheme.Opens.stalkIso S.U y).commRingCatIsoToRingEquiv

/-- The identification of local rings above is inverse to the stalk map of the open immersion
`U ⟶ X`. -/
theorem stalkMap_openStalkRingEquiv (r : S.U.toScheme.presheaf.stalk y) :
    (S.U.ι.stalkMap y).hom (openStalkRingEquiv S y r) = r := by
  rw [show S.U.ι.stalkMap y = (Scheme.Opens.stalkIso S.U y).inv from
    (Scheme.Opens.stalkIso_inv S.U y).symm]
  exact (Scheme.Opens.stalkIso S.U y).commRingCatIsoToRingEquiv.symm_apply_apply r

/-- **The stalk of `Ñ|_U` at a point of `U` is the stalk of `Ñ` at the prime under it**, as an
additive equivalence. This is the comparison of stalks across restriction along an open
immersion, read at the open immersion `U ⟶ X`. -/
def complementTildeStalkAddEquiv :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
        (Stacks.LocalCohomology.complementTilde S.A S.a N) ≃+
      ↑((AlgebraicGeometry.tilde (R := CommRingCat.of S.A) N).presheaf.stalk
        (S.U.ι.base y)) :=
  Scheme.Modules.restrictStalkAddEquiv S.U.ι
    (AlgebraicGeometry.tilde (R := CommRingCat.of S.A) N) y

/-- **The comparison of stalks across the inclusion of the open complement is semilinear** over
the identification `𝒪_{U,y} ≅ 𝒪_{X,𝔭}` of local rings: the comparison is semilinear over the
stalk map of `U ⟶ X`, and that identification is its inverse. -/
theorem complementTildeStalkAddEquiv_smul (r : S.U.toScheme.presheaf.stalk y)
    (z : (Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
      (Stacks.LocalCohomology.complementTilde S.A S.a N)) :
    complementTildeStalkAddEquiv S N y (r • z) =
      openStalkRingEquiv S y r • complementTildeStalkAddEquiv S N y z := by
  have key := Scheme.Modules.restrictStalkAddEquiv_smul S.U.ι
    (AlgebraicGeometry.tilde (R := CommRingCat.of S.A) N) y (openStalkRingEquiv S y r) z
  rw [stalkMap_openStalkRingEquiv] at key
  exact key

/-- **The stalk of `Ñ|_U` at a point `y` of `U` is the localization of `N` at the prime under
`y`**, as an additive equivalence. -/
def modulesStalkComplementTildeAddEquiv :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
        (Stacks.LocalCohomology.complementTilde S.A S.a N) ≃+
      LocalizedModule (underlyingPrime S y).asIdeal.primeCompl (N : Type u) :=
  (complementTildeStalkAddEquiv S N y).trans
    (tildeStalkAddEquiv (R := CommRingCat.of S.A) N (S.U.ι.base y))

/-- **The identification of the stalk of `Ñ|_U` at `y` with `N_𝔭` is semilinear** over
`Stacks.Algebraization.pointStalkRingEquiv`, which is precisely the composite of the two ring
isomorphisms the two halves of the identification are semilinear over. -/
theorem modulesStalkComplementTildeAddEquiv_smul (r : S.U.toScheme.presheaf.stalk y)
    (z : (Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
      (Stacks.LocalCohomology.complementTilde S.A S.a N)) :
    modulesStalkComplementTildeAddEquiv S N y (r • z) =
      pointStalkRingEquiv S y r • modulesStalkComplementTildeAddEquiv S N y z := by
  have h0 : modulesStalkComplementTildeAddEquiv S N y (r • z) =
      tildeStalkAddEquiv (R := CommRingCat.of S.A) N (S.U.ι.base y)
        (complementTildeStalkAddEquiv S N y (r • z)) := rfl
  rw [h0, complementTildeStalkAddEquiv_smul]
  exact tildeStalkAddEquiv_smul N (S.U.ι.base y) (openStalkRingEquiv S y r)
    (complementTildeStalkAddEquiv S N y z)

/-! ### The semilinear equivalence -/

/-- The ring isomorphism `𝒪_{U,y} ≅ A_𝔭` and its inverse form an inverse pair of ring
homomorphisms, which is what makes semilinear maps over it available. -/
instance ringHomInvPair_pointStalkRingEquiv :
    RingHomInvPair (pointStalkRingEquiv S y).toRingHom
      (pointStalkRingEquiv S y).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (pointStalkRingEquiv S y)

/-- The inverse pair of `Stacks.Algebraization.ringHomInvPair_pointStalkRingEquiv` taken in the
other order. -/
instance ringHomInvPair_pointStalkRingEquiv_symm :
    RingHomInvPair (pointStalkRingEquiv S y).symm.toRingHom
      (pointStalkRingEquiv S y).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (pointStalkRingEquiv S y)

/-- **The stalk of `Ñ|_U` at a point `y` of `U` is the localization of `N` at the prime under
`y`**, as an equivalence semilinear over the identification
`Stacks.Algebraization.pointStalkRingEquiv` of the local ring of `U` at `y` with that
localization of `A`. -/
theorem nonempty_semilinearEquiv_modulesStalk_complementTilde :
    Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
        (Stacks.LocalCohomology.complementTilde S.A S.a N)
      ≃ₛₗ[(pointStalkRingEquiv S y).toRingHom]
      LocalizedModule (underlyingPrime S y).asIdeal.primeCompl (N : Type u)) :=
  ⟨{ __ := modulesStalkComplementTildeAddEquiv S N y
     map_smul' := modulesStalkComplementTildeAddEquiv_smul S N y }⟩

/-- `Stacks.Algebraization.nonempty_semilinearEquiv_modulesStalk_complementTilde` with the
semilinear equivalence unbundled: an additive equivalence together with its compatibility with
the two scalar actions. -/
theorem exists_addEquiv_modulesStalk_complementTilde :
    ∃ e : (Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
          (Stacks.LocalCohomology.complementTilde S.A S.a N) ≃+
        LocalizedModule (underlyingPrime S y).asIdeal.primeCompl (N : Type u),
      ∀ (r : S.U.toScheme.presheaf.stalk y) (x), e (r • x) = pointStalkRingEquiv S y r • e x :=
  let ⟨e⟩ := nonempty_semilinearEquiv_modulesStalk_complementTilde S N y
  ⟨e.toAddEquiv, fun r x => map_smulₛₗ e r x⟩

end Complement

end Stacks.Algebraization

end
