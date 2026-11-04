module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Smoothness from locally free differentials over a perfect field

A reduced scheme locally of finite type over a perfect field is smooth as soon as its sheaf of
relative differentials is locally free. Over a field of characteristic zero reducedness is not
needed; over a perfect field of positive characteristic it is, a nonreduced example being
`k[t]/(t ^ p)`, whose relative differentials are free of rank one while the scheme is a point.

## Main results

* `AlgebraicGeometry.smooth_of_isLocallyFree_relativeDifferentials_of_perfectField`: the
  structure morphism of a reduced scheme locally of finite type over a perfect field whose sheaf
  of relative differentials is locally free is smooth.

## Implementation notes

Smoothness is tested pointwise: a morphism locally of finite presentation is smooth exactly when
its smooth locus is everything, and membership in the smooth locus at a point is formal
smoothness of the stalk map. Local finite presentation is automatic here, since the spectrum of a
field is locally Noetherian.

Everything is then read on one affine open `V` containing the point, with `A = Γ(X, V)` a finite
type algebra over the field `F = Γ(Spec k, ⊤)`, which `AlgebraicGeometry.Scheme.ΓSpecIso`
identifies with `k`. What local freeness of the sheaf contributes is that every prime of `A` lies
in the free locus of the `A`-module `Ω_{A/F}`; `Ω_{A/F}` is therefore projective, hence flat, and
its rank at a prime is unchanged under generalization
(`Module.rankAtStalk_eq_of_le_of_finite_of_flat`). The commutative-algebra input is then Stacks
Tag 00TT, which for a finite type algebra over a field says that smoothness at a prime `𝔮` is the
inequality `dim_{κ(𝔮)} κ(𝔮) ⊗_A Ω_{A/F} ≤ dim_𝔮 Spec A`, together with two facts about a minimal
prime `𝔭 ≤ 𝔮`:

* at `𝔭` the inequality is an equality, because `A` is reduced, so `A_𝔭` is a field (Tag 00EU,
  `minimal_prime_reduced_localization_isField`), and a field extension of a perfect field is
  formally smooth (`Algebra.FormallySmooth.of_perfectField`), so Tag 00TT applies at `𝔭` in the
  other direction;
* the local dimension is monotone under generalization, because the open neighbourhoods of `𝔮`
  are among those of `𝔭` while the local dimension is the infimum of their dimensions
  (`localKrullDim_le_of_specializes`).

Membership of a prime `𝔴` of `A` in the free locus is the only step that goes through the sheaf,
and it goes through the stalk at the point `z` of `V` corresponding to `𝔴`, recovered from `𝔴` by
the isomorphism `AlgebraicGeometry.IsAffineOpen.isoSpec` (`exists_primeIdealOf_eq`). Three
identifications are involved:

* the stalk of a locally free sheaf of modules is free over the local ring
  (`Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree`);
* the stalk of the sheaf of relative differentials is the module of Kähler differentials of the
  stalk map (`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, Tag
  01V0 read at a point);
* taking differentials relative to a localization of the base changes nothing
  (`omega_localization_base`, Tag 00RT (1)), which replaces the local ring of the base by `F`,
  while `Ω_{𝒪_{X,z}/F}` is the localization of `Ω_{A/F}` at `𝔴` (`omega_localization_total`,
  Tag 00RT (2)), which is what identifies the stalk with the fibre of the free locus.

## References

* [Stacks Project, Tag 04QP](https://stacks.math.columbia.edu/tag/04QP)
* [Stacks Project, Tag 00TT](https://stacks.math.columbia.edu/tag/00TT)
* [Stacks Project, Tag 00EU](https://stacks.math.columbia.edu/tag/00EU)
* [Stacks Project, Tag 00RT](https://stacks.math.columbia.edu/tag/00RT)
-/

@[expose] public section

open CategoryTheory TensorProduct TopologicalSpace
open Stacks.RelativeDifferentialStalkMap

universe u

namespace AlgebraicGeometry

/-- The local Krull dimension is monotone under generalization: if `y` specializes to `z` then
every open neighbourhood of `z` is an open neighbourhood of `y`, so the infimum defining the
local dimension at `y` runs over at least the neighbourhoods appearing at `z`. -/
private theorem localKrullDim_le_of_specializes {T : Type*} [TopologicalSpace T] {y z : T}
    (h : y ⤳ z) : localKrullDim T y ≤ localKrullDim T z :=
  le_iInf fun W => le_iInf fun hW => le_iInf fun hzW =>
    iInf_le_of_le W (iInf_le_of_le hW (iInf_le _ (h.mem_open hW hzW)))

/-- **Constant differential fibre dimension implies smoothness** for a reduced algebra of finite
type over a perfect field. If every prime of `A` lies in the free locus of `Ω_{A/F}`, then `A` is
smooth over `F` at every prime `𝔮`.

The module `Ω_{A/F}` is finite over `A` and, `A` being Noetherian, finitely presented, so a free
locus which is everything makes it projective and hence flat; its rank at a prime is then
unchanged under generalization. Choose a minimal prime `𝔭 ≤ 𝔮`. Since `A` is reduced, `A_𝔭` is a
field (Tag 00EU), hence a formally smooth extension of the perfect field `F`, so Tag 00TT gives
`dim_{κ(𝔭)} κ(𝔭) ⊗_A Ω_{A/F} = dim_𝔭 Spec A`. The fibre dimension at `𝔮` is the same, and the
local dimension does not decrease along the specialization `𝔭 ⤳ 𝔮`, so
`dim_{κ(𝔮)} κ(𝔮) ⊗_A Ω_{A/F} ≤ dim_𝔮 Spec A`, which is the second condition of Tag 00TT. -/
private theorem isSmoothAt_of_forall_mem_freeLocus {F A : Type*} [Field F] [PerfectField F]
    [CommRing A] [_root_.IsReduced A] [Algebra F A] [Algebra.FiniteType F A]
    (hfree : ∀ w : PrimeSpectrum A, w ∈ Module.freeLocus A Ω[A⁄F]) (q : PrimeSpectrum A) :
    Algebra.IsSmoothAt F q.asIdeal := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : Module.FinitePresentation A Ω[A⁄F] := Module.finitePresentation_of_finite A Ω[A⁄F]
  have : Module.Projective A Ω[A⁄F] :=
    Module.freeLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr hfree)
  obtain ⟨p, hpmin, hpq⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := q.asIdeal) bot_le
  have : p.IsPrime := hpmin.isPrime
  let pt : PrimeSpectrum A := ⟨p, ‹p.IsPrime›⟩
  let : Field (Localization.AtPrime p) :=
    (minimal_prime_reduced_localization_isField A p hpmin).toField
  have hsmoothp : Algebra.IsSmoothAt F p := Algebra.FormallySmooth.of_perfectField
  have hdimp : (Module.finrank pt.asIdeal.ResidueField
      (pt.asIdeal.ResidueField ⊗[A] Ω[A⁄F]) : WithBot ℕ∞) =
      localKrullDim (PrimeSpectrum A) pt :=
    ((Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing (k := F) (S := A) pt
      (Localization.AtPrime p)).1.out 1 3).mp hsmoothp
  have hle : pt ≤ q := (PrimeSpectrum.asIdeal_le_asIdeal pt q).mp hpq
  have hfib : Module.finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[A] Ω[A⁄F]) =
      Module.finrank pt.asIdeal.ResidueField (pt.asIdeal.ResidueField ⊗[A] Ω[A⁄F]) :=
    calc Module.finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[A] Ω[A⁄F])
        = Module.rankAtStalk Ω[A⁄F] q := (Module.rankAtStalk_eq q).symm
      _ = Module.rankAtStalk Ω[A⁄F] pt :=
          (Module.rankAtStalk_eq_of_le_of_finite_of_flat Ω[A⁄F] hle).symm
      _ = Module.finrank pt.asIdeal.ResidueField
            (pt.asIdeal.ResidueField ⊗[A] Ω[A⁄F]) := Module.rankAtStalk_eq pt
  refine ((Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing (k := F) (S := A) q
    (Localization.AtPrime q.asIdeal)).1.out 2 1).mp ?_
  rw [hfib, hdimp]
  exact localKrullDim_le_of_specializes ((PrimeSpectrum.le_iff_specializes pt q).mp hle)

/-- Every prime of the ring of sections of an affine open is the prime of a point of that open:
`AlgebraicGeometry.IsAffineOpen.primeIdealOf` is the action on points of the isomorphism
`AlgebraicGeometry.IsAffineOpen.isoSpec`, hence surjective. -/
private theorem exists_primeIdealOf_eq {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (w : ↥(Spec Γ(X, V))) : ∃ z : ↥V, hV.primeIdealOf z = w := by
  refine ⟨hV.isoSpec.inv w, ?_⟩
  have h : (hV.isoSpec.inv ≫ hV.isoSpec.hom) w = w := by
    rw [Iso.inv_hom_id]
    rfl
  exact (Scheme.Hom.comp_apply hV.isoSpec.inv hV.isoSpec.hom w).symm.trans h

/-- The stalk at a point of the sheaf of relative differentials of a morphism with locally free
relative differentials is a free module over the local ring of the source at that point, in the
spelling `Ω[𝒪_{X,z}⁄𝒪_{S,f z}]` of the Kähler differentials of the stalk map. -/
private theorem free_kaehlerDifferential_stalkMap_of_isLocallyFree
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} f.relativeDifferentials) (z : X) :
    let _ := algebraStalkMap f z
    Module.Free (ToType (X.sheaf.presheaf.stalk z))
      (KaehlerDifferential (ToType (S.presheaf.stalk (f z)))
        (ToType (X.sheaf.presheaf.stalk z))) := by
  classical
  let := algebraStalkMap f z
  exact (Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree.{u}
    f.relativeDifferentials z).of_equiv (relativeDifferentialsStalkKaehlerEquiv f z)

/-- The stalk map of a morphism from a reduced scheme locally of finite type over a perfect field
with locally free relative differentials is formally smooth at every point.

Work on an affine open `V` containing the point and write `A = Γ(X, V)`, a finite type algebra
over the field `F = Γ(Spec k, ⊤)`. At the point `z` of `V` corresponding to a prime `𝔴` of `A`
the module `Ω[𝒪_{X,z}⁄F]` is free, being the stalk of a locally free sheaf, and it is the
localization of `Ω_{A/F}` at `𝔴`; so every prime of `A` lies in the free locus of `Ω_{A/F}` and
`isSmoothAt_of_forall_mem_freeLocus` applies. -/
private theorem formallySmooth_stalkMap_of_isLocallyFree_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} f.relativeDifferentials) (x : X) :
    (f.stalkMap x).hom.FormallySmooth := by
  classical
  obtain ⟨_, ⟨V, hVmem, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV : IsAffineOpen V := hVmem
  let U : (Spec (.of k)).Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ U := fun _ _ => trivial
  let F := ToType Γ(Spec (.of k), U)
  let A := ToType Γ(X, V)
  let eF := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field F := (eF.toMulEquiv.isField (Field.toIsField k)).toField
  have : PerfectField F := PerfectField.of_ringEquiv eF.symm
  let : Algebra F A := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType F A :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hU hV hVU)
  have : _root_.IsReduced A := IsReduced.component_reduced V
  have hfree : ∀ w : PrimeSpectrum A, w ∈ Module.freeLocus A Ω[A⁄F] := by
    intro w
    obtain ⟨z, hw⟩ := exists_primeIdealOf_eq hV w
    let Sz := ToType (X.sheaf.presheaf.stalk z.1)
    let T := ToType ((Spec (.of k)).presheaf.stalk (f z.1))
    let p := hU.primeIdealOf ⟨f z.1, trivial⟩
    let : Algebra F T := ((Spec (.of k)).presheaf.germ U (f z.1) trivial).hom.toAlgebra
    have : IsLocalization.AtPrime T p.asIdeal := hU.isLocalization_stalk ⟨f z.1, trivial⟩
    let : Algebra T Sz := algebraStalkMap f z.1
    let : Algebra F Sz := ((algebraMap T Sz).comp (algebraMap F T)).toAlgebra
    have : IsScalarTower F T Sz := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A Sz := (X.presheaf.germ V z.1 z.2).hom.toAlgebra
    have : IsLocalization.AtPrime Sz w.asIdeal := hw ▸ hV.isLocalization_stalk z
    have hcompat : f.appLE U V hVU ≫ X.presheaf.germ V z.1 z.2 =
        (Spec (.of k)).presheaf.germ U (f z.1) trivial ≫ f.stalkMap z.1 := by
      rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hVU) z.1 z.2]
      exact (Scheme.Hom.germ_stalkMap f U z.1 trivial).symm
    have : IsScalarTower F A Sz := IsScalarTower.of_algebraMap_eq fun a =>
      (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat) a).symm
    have : IsLocalizedModule w.asIdeal.primeCompl (KaehlerDifferential.map F F A Sz) :=
      omega_localization_total F A w.asIdeal.primeCompl Sz
    have hfreeT : Module.Free Sz Ω[Sz⁄T] :=
      free_kaehlerDifferential_stalkMap_of_isLocallyFree f hΩ z.1
    exact (Module.mem_freeLocus_of_isLocalization w Sz Ω[Sz⁄F]
      (KaehlerDifferential.map F F A Sz)).mpr
      (hfreeT.of_equiv (LinearEquiv.ofBijective (KaehlerDifferential.map F T Sz Sz)
        (omega_localization_base F Sz p.asIdeal.primeCompl T)).symm)
  exact (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mpr
    (isSmoothAt_of_forall_mem_freeLocus hfree (hV.primeIdealOf ⟨x, hxV⟩))

/-- **Stacks Project, Tag 04QP.** A reduced scheme locally of finite type over a perfect field
is smooth if its sheaf of relative differentials is locally free. -/
@[stacks 04QP,
  ega "IV 17.15.6" "perfect k, reduced X",
  sga "1 II 5.7" "k perfect, X reduced",
  sga "1 II 5.5" "(ii)=>(i), X reduced"]
theorem smooth_of_isLocallyFree_relativeDifferentials_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} f.relativeDifferentials) :
    Smooth f :=
  f.smoothLocus_eq_top_iff.mp (top_le_iff.mp fun x _ =>
    Scheme.Hom.mem_smoothLocus.mpr
      (formallySmooth_stalkMap_of_isLocallyFree_of_perfectField f hΩ x))

end AlgebraicGeometry

end
