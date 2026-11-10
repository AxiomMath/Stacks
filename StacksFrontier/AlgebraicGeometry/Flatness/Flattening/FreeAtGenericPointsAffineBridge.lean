module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapGenericFibreFreeness
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FiniteTypeStalkGenerators
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SmoothAffineGeometricallyIntegral

/-!
# From a free stalk at the generic point of a fibre to the ring-theoretic engine

The engine of the first assertion of [Stacks, Tag 05MS],
`Module.bijective_of_forall_basis_localizedModule_genericFibre`, asks — for a smooth morphism of
affines with geometrically irreducible fibres, written on functions as `R → S` — for a basis of
`N_{rS}` over `S_{rS}` indexed by `Fin p`, at *every* prime `r` of `R`. The hypothesis that the
source's proof has available is geometric: the stalk of the module at the generic point of every
fibre is free of rank `p`. This file is the translation between the two.

It has two halves, which are independent of each other.

*The module half.* For a quasi-coherent module on an affine open `U` and a point `x ∈ U`, the
stalk `F_x` is the localization of `Γ(F, U)` at the prime of `x`
(`AlgebraicGeometry.isLocalizedModule_germₗ`) and `𝒪_{X,x}` is the localization of `Γ(X, U)` at
that same prime, so a basis of the stalk over the local ring *is* a basis of the localized
sections over the localized ring — once transported, which is what
`AlgebraicGeometry.nonempty_basis_localizedModule_of_stalkFreeOfRank` does.

*The point half.* For a prime `r` of `R` the prime `rS` of `S` is, as the source says, the
generic point of the fibre over `r`: it lies over `r`
(`Ideal.comap_map_of_geometricallyIrreducible`) and is contained in every prime that does, so
the point it names is the one generic point of that fibre. The identification with the point
supplied by the geometric hypothesis — the image under `AlgebraicGeometry.Scheme.Hom.fiberι` of a
generic point of the scheme-theoretic fibre — is
`AlgebraicGeometry.primeIdealOf_eq_map_appLE_of_isGenericPoint`, by specialization in both
directions.

## Main results

* `AlgebraicGeometry.mem_closure_fiberι_of_isGenericPoint`: every point over `y` lies in the
  closure of the image of a generic point of the scheme-theoretic fibre over `y`.
* `AlgebraicGeometry.nonempty_basis_localizedModule_of_stalkFreeOfRank`: a free stalk of rank `p`
  at a point of an affine open gives a basis of the localized sections there.
* `AlgebraicGeometry.primeIdealOf_eq_map_appLE_of_isGenericPoint`: the prime of a generic point
  of a fibre is the extension `rS` of the prime `r` of the point of the base.

## Implementation notes

The transport of the module half is in two steps, because the stalk is a module over
`𝒪_{X,x}` while the localized sections are a module over `Localization.AtPrime 𝔮`, and the two
rings are only canonically isomorphic. Both sides are therefore first viewed as `Γ(X, U)`-modules
— where `IsLocalizedModule.linearEquiv` compares them and `Finsupp.mapRange.linearEquiv` carries
the coefficients along `IsLocalization.algEquiv` — and the resulting `Γ(X, U)`-linear equivalence
is promoted by `LinearEquiv.extendScalarsOfIsLocalization`, which is exactly the statement that a
`Γ(X, U)`-linear map between modules over the localization is automatically linear over it.

The point half needs no scheme-theoretic generic point of its own: the dictionary between points
of an affine open and primes of its functions is `AlgebraicGeometry.IsAffineOpen.primeIdealOf`,
its compatibility with a morphism is `AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`,
and specialization in the open is read off in `PrimeSpectrum` through the open immersion
`AlgebraicGeometry.IsAffineOpen.fromSpec`, which is inducing.

## References

* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
-/

@[expose] public section

open CategoryTheory CommRingCat TopologicalSpace
open Stacks.ModuleStalkSpecialization

universe u

namespace AlgebraicGeometry

/-! ### Generic points of fibres, topologically -/

/-- A point of `X` lies in the image of the fibre over `y` iff it lies over `y`. -/
private theorem mem_range_fiberι_iff {X Y : Scheme.{u}} (g : X ⟶ Y) (y : Y) (z : X) :
    z ∈ Set.range (g.fiberι y) ↔ g.base z = y := by
  rw [Scheme.Hom.range_fiberι]
  rfl

/-- **Every point over `y` lies in the closure of the image of a generic point of the fibre over
`y`.** The point is the image of a point of the scheme-theoretic fibre, which lies in the closure
of the generic point there, and the closure is carried along the continuous map
`AlgebraicGeometry.Scheme.Hom.fiberι`. -/
theorem mem_closure_fiberι_of_isGenericPoint {X Y : Scheme.{u}} (g : X ⟶ Y) (y : Y)
    {ξ : g.fiber y} (hξ : IsGenericPoint ξ (Set.univ : Set (g.fiber y)))
    {z : X} (hz : g.base z = y) :
    z ∈ closure ({g.fiberι y ξ} : Set X) := by
  obtain ⟨ζ, hζ⟩ := (mem_range_fiberι_iff g y z).2 hz
  have hmem : ζ ∈ closure ({ξ} : Set (g.fiber y)) := by
    rw [hξ]
    exact Set.mem_univ _
  have himg := image_closure_subset_closure_image
    (f := (g.fiberι y).base) (g.fiberι y).continuous (s := {ξ})
  have hcl := himg ⟨ζ, hmem, rfl⟩
  rw [← hζ]
  simpa using hcl

/-! ### A free stalk as a basis of the localized sections -/

/-- **A free stalk of rank `p` at a point of an affine open is a basis of the localized sections
there.** The stalk of a quasi-coherent module at a point of an affine open is the localization of
its sections at the prime of that point, and the local ring is the localization of the functions
at that prime, so a basis of the stalk over the local ring transports to a basis of the localized
sections over the localized ring. -/
theorem nonempty_basis_localizedModule_of_stalkFreeOfRank {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (p : ℕ)
    (h : StalkFreeOfRank F x p) :
    Nonempty (Module.Basis (Fin p)
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U))) := by
  classical
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  let := stalkModule F x
  let := sectionsStalkModule F hx
  have := isScalarTower_sectionsStalk F hx
  have := isLocalizedModule_germₗ F hU hx
  obtain ⟨b0⟩ := h
  -- `Scheme.Modules.presheaf` is not unfolded by instance search, so restate the equivalence
  -- with the stalk in the spelling the module structures above are attached to.
  have b : F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (Fin p →₀ X.presheaf.stalk x) := b0
  have e0 : LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)
      ≃ₗ[Γ(X, U)] F.presheaf.stalk x :=
    IsLocalizedModule.linearEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ _) (germₗ F hx)
  have eR : Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal
      ≃ₐ[Γ(X, U)] X.presheaf.stalk x :=
    IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
  have e1 : LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)
      ≃ₗ[Γ(X, U)]
      (Fin p →₀ Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :=
    (e0.trans (b.restrictScalars Γ(X, U))).trans
      (Finsupp.mapRange.linearEquiv eR.symm.toLinearEquiv)
  exact ⟨Module.Basis.ofRepr (e1.extendScalarsOfIsLocalization
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))⟩

/-! ### The prime of the generic point of a fibre -/

/-- **The prime of a generic point of a fibre is the extension `rS` of the prime of the point of
the base.** Let `U` and `V` be affine opens with `U ⊆ g⁻¹(V)`, write `R → S` for the induced map
of functions, assume it flat with geometrically integral fibres, and let `r` be the prime of a
point `y ∈ V`. If a generic point of the fibre of `g` over `y` lies in `U`, then its prime is
`rS`.

Both inclusions are elementary. That `rS` is contained in the prime `𝔮` of the generic point is
the contraction `𝔮 ∩ R = r` of `AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`. For the
converse, `rS` is prime and contracts to `r`
(`Ideal.comap_map_of_geometricallyIrreducible`), so the point it names lies over `y` as well,
hence in the closure of the generic point by
`AlgebraicGeometry.mem_closure_fiberι_of_isGenericPoint`; read in `PrimeSpectrum` through the
open immersion `AlgebraicGeometry.IsAffineOpen.fromSpec` that says `𝔮 ≤ rS`. -/
theorem primeIdealOf_eq_map_appLE_of_isGenericPoint {X Y : Scheme.{u}} (g : X ⟶ Y)
    {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ g ⁻¹ᵁ V)
    (hflat : letI := (g.appLE V U hUV).hom.toAlgebra
      Module.Flat Γ(Y, V) Γ(X, U))
    (hgi : letI := (g.appLE V U hUV).hom.toAlgebra
      GeometricallyIntegral (Spec.map (ofHom (algebraMap Γ(Y, V) Γ(X, U)))))
    {y : Y} (hy : y ∈ V) {ξ : g.fiber y}
    (hξ : IsGenericPoint ξ (Set.univ : Set (g.fiber y))) (hmem : g.fiberι y ξ ∈ U) :
    letI := (g.appLE V U hUV).hom.toAlgebra
    (hU.primeIdealOf ⟨g.fiberι y ξ, hmem⟩).asIdeal =
      Ideal.map (algebraMap Γ(Y, V) Γ(X, U)) (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  let := (g.appLE V U hUV).hom.toAlgebra
  have := hflat
  have := hgi
  have halg : (algebraMap Γ(Y, V) Γ(X, U)) = (g.appLE V U hUV).hom :=
    RingHom.algebraMap_toAlgebra _
  have hgx : g.base (g.fiberι y ξ) = y := (mem_range_fiberι_iff g y _).1 ⟨ξ, rfl⟩
  have hcomap : (hU.primeIdealOf ⟨g.fiberι y ξ, hmem⟩).comap
      (algebraMap Γ(Y, V) Γ(X, U)) = hV.primeIdealOf ⟨y, hy⟩ := by
    rw [halg, IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hmem]
    congr 1
    exact Subtype.ext hgx
  have hp : (Ideal.map (algebraMap Γ(Y, V) Γ(X, U))
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal).IsPrime :=
    Ideal.isPrime_map_of_geometricallyIntegral Γ(Y, V) Γ(X, U) _
  set P : PrimeSpectrum Γ(X, U) :=
    ⟨Ideal.map (algebraMap Γ(Y, V) Γ(X, U)) (hV.primeIdealOf ⟨y, hy⟩).asIdeal, hp⟩ with hPdef
  have hle₁ : P.asIdeal ≤ (hU.primeIdealOf ⟨g.fiberι y ξ, hmem⟩).asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq (congrArg PrimeSpectrum.asIdeal hcomap).symm)
  have hPcomap : Spec.map (g.appLE V U hUV) P = hV.primeIdealOf ⟨y, hy⟩ := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (g.appLE V U hUV).hom P.asIdeal = _
    rw [← halg]
    exact Ideal.comap_map_of_geometricallyIrreducible Γ(Y, V) Γ(X, U) _
  have hgP : g.base (hU.fromSpec P) = y := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec g hV hU hUV
    have h3 : ∀ z : (Spec Γ(X, U) : Scheme),
        hV.fromSpec ((Spec.map (g.appLE V U hUV)) z) = g (hU.fromSpec z) := fun z => by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
    have h2 := h3 P
    rw [hPcomap, IsAffineOpen.fromSpec_primeIdealOf] at h2
    exact h2.symm
  have hclos : hU.fromSpec P ∈ closure ({g.fiberι y ξ} : Set X) :=
    mem_closure_fiberι_of_isGenericPoint g y hξ hgP
  have hind : Topology.IsInducing hU.fromSpec.base :=
    hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing
  have hsp0 : hU.fromSpec.base (hU.primeIdealOf ⟨g.fiberι y ξ, hmem⟩) ⤳
      hU.fromSpec.base P := by
    rw [specializes_iff_mem_closure, IsAffineOpen.fromSpec_primeIdealOf]
    exact hclos
  have hsp : (hU.primeIdealOf ⟨g.fiberι y ξ, hmem⟩ : (Spec Γ(X, U) : Scheme)) ⤳ P :=
    hind.specializes_iff.mp hsp0
  exact le_antisymm ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
    ((PrimeSpectrum.le_iff_specializes _ _).mpr hsp)) hle₁

/-! ### The engine on an affine open -/

/-- A basis of a localized module at a prime transports along an equality of primes. -/
theorem nonempty_basis_localizedModule_congr {S : Type u} [CommRing S] {q q' : Ideal S}
    [q.IsPrime] [q'.IsPrime] (h : q = q') (N : Type*) [AddCommGroup N] [Module S N] (p : ℕ)
    (hb : Nonempty (Module.Basis (Fin p) (Localization.AtPrime q)
      (LocalizedModule q.primeCompl N))) :
    Nonempty (Module.Basis (Fin p) (Localization.AtPrime q')
      (LocalizedModule q'.primeCompl N)) := by
  subst h
  exact hb

/-- **The engine of the first assertion of [Stacks, Tag 05MS], on an affine open.** Let `g` be a
morphism with geometrically irreducible fibres, let `V` be an affine open of the target and `U` an
affine open of the source lying over it and meeting every fibre over `V`, and suppose the induced
map of functions is flat of finite presentation with geometrically integral fibres — all of which
holds for an affine open of a smooth morphism with geometrically irreducible fibres which
surjects onto an affine open of the base. Let `F` be quasi-coherent of finite type, generated on
`U` by `p` sections. If the stalk of `F` at the generic point of *every* fibre of `g` is free of
rank `p`, then `Γ(F, U)` is free of rank `p` over `Γ(X, U)`.

This is the source's "for every `t' ∈ T` the induced map `α` is an isomorphism, hence the
surjection `α` is an isomorphism": the generating sections give a surjection
`Γ(X, U)^{⊕ p} → Γ(F, U)`, at the prime `rS` of each prime `r` of `Γ(Y, V)` the localization of
`Γ(F, U)` is free of rank `p` because that prime is the generic point of the fibre
(`AlgebraicGeometry.primeIdealOf_eq_map_appLE_of_isGenericPoint` and
`AlgebraicGeometry.nonempty_basis_localizedModule_of_stalkFreeOfRank`), and
`Module.bijective_of_forall_basis_localizedModule_genericFibre` concludes. -/
theorem nonempty_basis_sections_of_forall_stalkFreeOfRank {X Y : Scheme.{u}} (g : X ⟶ Y)
    [GeometricallyIrreducible g] {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ g ⁻¹ᵁ V)
    (hcov : ∀ y ∈ V, ∃ x ∈ U, g.base x = y)
    (hfp : letI := (g.appLE V U hUV).hom.toAlgebra
      Algebra.FinitePresentation Γ(Y, V) Γ(X, U))
    (hflat : letI := (g.appLE V U hUV).hom.toAlgebra
      Module.Flat Γ(Y, V) Γ(X, U))
    (hgi : letI := (g.appLE V U hUV).hom.toAlgebra
      GeometricallyIntegral (Spec.map (ofHom (algebraMap Γ(Y, V) Γ(X, U)))))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (p : ℕ) (s : Fin p → Γ(F, U))
    (hs : Function.Surjective fun c : Fin p → Γ(X, U) ↦ ∑ i, c i • s i)
    (hstalk : ∀ (y : Y) (ξ : g.fiber y), IsGenericPoint ξ (Set.univ : Set (g.fiber y)) →
      StalkFreeOfRank F (g.fiberι y ξ) p) :
    Nonempty (Module.Basis (Fin p) Γ(X, U) Γ(F, U)) := by
  classical
  let := (g.appLE V U hUV).hom.toAlgebra
  have := hfp
  have := hflat
  have := hgi
  let : Module Γ(Y, V) Γ(F, U) :=
    Module.compHom _ (algebraMap Γ(Y, V) Γ(X, U))
  have : IsScalarTower Γ(Y, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
  have halpha : Function.Surjective (Fintype.linearCombination Γ(X, U) s) := by
    simpa [Fintype.linearCombination] using hs
  refine Module.nonempty_basis_of_forall_basis_localizedModule_genericFibre
    Γ(Y, V) Γ(X, U) Γ(F, U) p (Fintype.linearCombination Γ(X, U) s) (fun r hr ↦ ?_) halpha
  have := hr
  have := Ideal.isPrime_map_of_geometricallyIntegral Γ(Y, V) Γ(X, U) r
  -- the point of `V` whose prime is `r`
  set y : Y := hV.fromSpec ⟨r, hr⟩ with hydef
  have hy : y ∈ V := hV.fromSpec_mem ⟨r, hr⟩
  have hpy : (hV.primeIdealOf ⟨y, hy⟩).asIdeal = r :=
    congrArg PrimeSpectrum.asIdeal (hV.primeIdealOf_fromSpec ⟨r, hr⟩ hy)
  -- the generic point of the fibre over `y`, which lies in `U`
  have : IrreducibleSpace (g.fiber y) := inferInstance
  have hξ : IsGenericPoint (genericPoint (g.fiber y)) (Set.univ : Set (g.fiber y)) :=
    genericPoint_spec _
  obtain ⟨x₀, hx₀U, hx₀y⟩ := hcov y hy
  obtain ⟨ζ, hζ⟩ := (mem_range_fiberι_iff g y x₀).2 hx₀y
  have hopen : IsOpen ((g.fiberι y).base ⁻¹' (U : Set X)) :=
    U.isOpen.preimage (g.fiberι y).continuous
  have hζU : ζ ∈ (g.fiberι y).base ⁻¹' (U : Set X) := by
    rw [Set.mem_preimage, hζ]
    exact hx₀U
  have hmemU : g.fiberι y (genericPoint (g.fiber y)) ∈ U := by
    by_contra hc
    have hsub : closure ({genericPoint (g.fiber y)} : Set (g.fiber y)) ⊆
        ((g.fiberι y).base ⁻¹' (U : Set X))ᶜ :=
      closure_minimal (Set.singleton_subset_iff.mpr hc) hopen.isClosed_compl
    rw [hξ] at hsub
    exact hsub (Set.mem_univ ζ) hζU
  -- the prime of that generic point is `rS`, and the stalk there is free of rank `p`
  have heq : (hU.primeIdealOf ⟨g.fiberι y (genericPoint (g.fiber y)), hmemU⟩).asIdeal =
      Ideal.map (algebraMap Γ(Y, V) Γ(X, U)) r := by
    rw [← hpy]
    exact primeIdealOf_eq_map_appLE_of_isGenericPoint g hV hU hUV hflat hgi hy hξ hmemU
  exact nonempty_basis_localizedModule_congr heq Γ(F, U) p
    (nonempty_basis_localizedModule_of_stalkFreeOfRank F hU hmemU p
      (hstalk y (genericPoint (g.fiber y)) hξ))

end AlgebraicGeometry

end
