module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaAffineSheafComparison
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# The sheaf attached to an `f`-torsion-free module is `I`-torsion free

Let `R` be a commutative ring, let `D ⊆ Spec R` be an effective Cartier divisor whose ideal
sheaf `I` is generated over `Spec R` by a section `g` with image `f ∈ Γ(Spec R, ⊤)`, and let
`M` be an `R`-module on which multiplication by `f` is injective. Then the quasi-coherent
module `M̃` attached to `M` is `I`-torsion free.

This is the input the second assertion of [Stacks, Tag 0GTV] needs in order to be *stated*: the
sheaf-theoretic décalage `η_I` of [Stacks, Tag 0GT2] is defined only on complexes of
`I`-torsion-free modules, so without this lemma the comparison `η_I(M̃^•) ≅ (η_f M^•)^~` of
`Stacks.Divisors.Eta.etaObjTildeIso` cannot even be applied to a complex of the shape `M̃^•`.

## Main results

* `Stacks.Divisors.Eta.isSMulRegular_of_isLocalizedModule`: a localization of a module on which
  `f` acts injectively is a module on which `f` acts injectively.
* `Stacks.Divisors.Eta.isSMulRegular_tilde_sections`: multiplication by `f` is injective on
  `M̃(V)` for *every* open `V ⊆ Spec R`, not only for the basic opens.
* `Stacks.Divisors.Eta.isGeneratorRegularOn_tilde`: multiplication by the generator is injective
  on the sections of `M̃`, in the spelling of [Stacks, Tag 0GT5].
* `Stacks.Divisors.Eta.isIdealTorsionFree_tilde`: **`M̃` is `I`-torsion free.**
* `Stacks.Divisors.Eta.isIdealTorsionFree_tildeComplex`: the termwise form, for a complex of
  `f`-torsion-free modules.
* `Stacks.Divisors.Eta.isIdealTorsionFree_of_isGeneratorRegularOn_top`: on any ringed space, a
  single global section of an invertible ideal sheaf that acts injectively on the sections of `F`
  already makes `F` torsion free.
* `Stacks.Divisors.Eta.etaObjTildeComplexIso`: the comparison
  `η_I(M̃^•) ≅ (η_f Γ(Spec R, M̃^•))^~`, which is a well-formed term only once the terms of `M̃^•`
  are known to be `I`-torsion free.

## Implementation notes

**Why the basic opens are not enough, and why the general open needs the sheaf condition.** On
a basic open `D(g)` the sections of `M̃` are the localization `M[1/g]`, which
`AlgebraicGeometry.tilde.toOpen` exhibits as an `IsLocalizedModule`, and the regularity of `f`
there is `isSMulRegular_of_isLocalizedModule`. For an arbitrary open `V` the sections are not a
localization of `M`, so the statement is proved by descent: two sections with the same multiple
by `f` agree on every basic open contained in `V`, hence agree, by
`TopCat.Presheaf.IsSheaf.section_ext`. Mathlib's
`AlgebraicGeometry.Scheme.Modules.isSMulRegular_of_le_basicOpen` is a different statement — it
asks `V ≤ D(f)`, where `f` is invertible on the sections and no hypothesis on `M` is needed.

**Reduction to a single global generator.** [Stacks, Tag 0GT5] characterizes torsion-freeness by
the injectivity of multiplication by *every* local generator on *every* open. Only the global
generator `g` is available here, and it is enough: a local generator `a` of `I` over `U`
divides the restriction of `g` to every `V ⊆ U` — that is what
`Stacks.IdealTorsion.GeneratesIdealOn` says — so an element killed by `a` is killed by `g`.
That step mentions neither `Spec` nor `tilde`, and is therefore stated for a ringed space and an
arbitrary invertible ideal sheaf, as `isIdealTorsionFree_of_isGeneratorRegularOn_top`. It is
stated with the ideal, its inclusion and the module as *variables*, in the spelling
`Stacks.IdealTorsion` uses, because `rw` and `simp` build motives at a transparency at which
`idealSheaf D` — written at `structureSheaf X.toRingedSpace.sheaf` — is not accepted where
`structureSheafRing X.toRingedSpace` is expected, even though the two are the same sheaf of
rings and an `exact` crosses between them. The `let r'` in that proof moves the scalar supplied
by `GeneratesIdealOn`, which arrives at the `CommRingCat` spelling of `𝒪_X(V)`, to the `RingCat`
spelling in which it can act on the sections of `F`.

**The three spellings of the sections.** `Stacks.IdealTorsion.IsGeneratorRegularOn` is stated for
`F.val.obj (op V)`, a module over the `RingCat`-valued
`Stacks.SheafOfModules.TensorStalkRingedSpace.O (Spec R)`; Mathlib's `Γ(M̃, V)` is the same module
over the `CommRingCat`-valued `Γ(Spec R, V)`; and the regularity statement that
`IsLocalizedModule` supplies is over `R`. The first two are the same module structure — Mathlib's
instance on `Γ(M, V)` *is* `(M.val.obj (op V)).isModule` — so the passage between them is a type
ascription, and the third is reached through
`AlgebraicGeometry.Scheme.Modules.smul_Spec_def`, which rewrites the action of `r : R` as the
action of the restriction of `(ΓSpecIso R).inv r`. Instance search does not cross the first
passage on its own, which is why `isGeneratorRegularOn_tilde` states its hypothesis with
`Stacks.IdealTorsion.Eta.generatorSection` — a definition already written at the `CommRingCat`
spelling — rather than with `idealSection`.

## References

* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 0GT2](https://stacks.math.columbia.edu/tag/0GT2)
* [Stacks Project, Tag 0F7R](https://stacks.math.columbia.edu/tag/0F7R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.IdealTorsion (IsIdealTorsionFree GeneratesIdealOn IsGeneratorRegularOn idealSection
  idealSection_naturality idealTorsionFree_tfae)
open Stacks.IdealTorsion.Eta (generatorSection)

universe u

namespace Stacks.Divisors.Eta

/-- **A localization of a module on which `f` acts injectively is one on which `f` acts
injectively.** If `M'` is the localization of `M` at a submonoid `S` and multiplication by `f` is
injective on `M`, then it is injective on `M'`: an element of `M'` is a fraction `m/s`, and
`f · (m/s) = 0` says that `s' f m = 0` for some `s' ∈ S`, whence `s' m = 0` and `m/s = 0`. -/
theorem isSMulRegular_of_isLocalizedModule {R : Type*} [CommRing R]
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (S : Submonoid R) (h : M →ₗ[R] M') [IsLocalizedModule S h] {f : R}
    (hf : IsSMulRegular M f) : IsSMulRegular M' f := by
  have hzero : ∀ x : M', f • x = 0 → x = 0 := by
    intro x hx
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S h x
    rw [Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul] at hx
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.mk'_eq_zero' h s).mp hx
    have hkill : f • ((s' : R) • m) = f • (0 : M) := by
      rw [smul_zero, smul_comm]
      simpa [Submonoid.smul_def] using hs'
    exact (IsLocalizedModule.mk'_eq_zero' h s).mpr ⟨s', by
      simpa [Submonoid.smul_def] using hf hkill⟩
  intro x y hxy
  have hsub : f • (x - y) = 0 := by
    have h' : f • x = f • y := hxy
    rw [smul_sub, h', sub_self]
  exact sub_eq_zero.mp (hzero _ hsub)

/-- **One global section regular on `F` makes `F` torsion free.** [Stacks, Tag 0GT5]
characterizes `I`-torsion-freeness by the injectivity of multiplication by *every* local
generator of `I`; a single global section `g` of `I` whose multiplication is injective on the
sections of `F` is enough, because a local generator `a` of `I` over `U` divides the restriction
of `g` to every `V ⊆ U`, so an element killed by `a` is killed by `g`. -/
theorem isIdealTorsionFree_of_isGeneratorRegularOn_top {X : RingedSpace.{u, u}}
    {I : SheafOfModules.{u} (structureSheafRing X)}
    (ι : I ⟶ SheafOfModules.unit (structureSheafRing X)) [Mono ι]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) I 1]
    (F : SheafOfModules.{u} (structureSheafRing X))
    (g : I.val.obj (op (⊤ : Opens X)))
    (hF : IsGeneratorRegularOn X ι F ⊤ g) :
    IsIdealTorsionFree X ι F := by
  refine ((idealTorsionFree_tfae X ι F).out 4 1).1 ?_
  intro U a ha V hVU s t hst
  obtain ⟨r, hr⟩ := ha V hVU ((I.val.map (homOfLE (le_top (a := V))).op).hom g)
  refine hF V le_top ?_
  let r' : ((Stacks.SheafOfModules.TensorStalkRingedSpace.O X).obj (op V) : Type u) := r
  have h3 : idealSection X ι (op V) ((I.val.map (homOfLE (le_top (a := V))).op).hom g) =
      r' • idealSection X ι (op V) ((I.val.map (homOfLE hVU).op).hom a) := by
    rw [hr]
    exact map_smul (ι.val.app (op V)).hom r _
  have h4 : ∀ x : F.val.obj (op V),
      (r' • idealSection X ι (op V) ((I.val.map (homOfLE hVU).op).hom a)) • x =
        r' • (idealSection X ι (op V) ((I.val.map (homOfLE hVU).op).hom a) • x) :=
    fun x => smul_assoc _ _ _
  change idealSection X ι (op V) _ • s = idealSection X ι (op V) _ • t
  rw [h3, h4 s, h4 t]
  exact congrArg _ hst

variable (R : CommRingCat.{u})

/-- Multiplication by `f` is injective on the sections of `M̃` over a basic open, those sections
being the localization `M[1/g]`. The open is taken as an argument together with an equation
identifying it with `D(g)` so that the statement elaborates at the `(Spec R).Opens` spelling, at
which the module structure on the sections is found by instance search. -/
theorem isSMulRegular_tilde_sections_basicOpen (M : ModuleCat.{u} R) {f : R}
    (hf : IsSMulRegular M f) (g : R) (V : (Spec R).Opens)
    (hV : V = PrimeSpectrum.basicOpen g) :
    IsSMulRegular Γ((tilde.functor R).obj M, V) f := by
  subst hV
  exact isSMulRegular_of_isLocalizedModule (Submonoid.powers g)
    (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom hf

/-- **Multiplication by `f` is injective on the sections of `M̃` over every open.** Two sections
with the same multiple by `f` agree on every basic open inside `V`, by
`isSMulRegular_tilde_sections_basicOpen`, hence agree. -/
theorem isSMulRegular_tilde_sections (M : ModuleCat.{u} R) {f : R}
    (hf : IsSMulRegular M f) (V : (Spec R).Opens) :
    IsSMulRegular Γ((tilde.functor R).obj M, V) f := by
  intro s t hst
  have hst' : f • s = f • t := hst
  refine TopCat.Presheaf.IsSheaf.section_ext ((tilde.functor R).obj M).isSheaf ?_
  intro x hx
  obtain ⟨W, ⟨g, rfl⟩, hxW, hWV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx V.2
  set V' : (Spec R).Opens := PrimeSpectrum.basicOpen g with hV'
  refine ⟨V', hWV, hxW, isSMulRegular_tilde_sections_basicOpen R M hf g V' hV' ?_⟩
  change f • _ = f • _
  simp only [← AlgebraicGeometry.Scheme.Modules.map_smul_Spec]
  exact congrArg _ hst'

/-- `isSMulRegular_tilde_sections` for a scalar presented as the restriction of a global section
of `𝒪_{Spec R}`, in the implication form and with every term written at the `Γ` spelling, which
is where the passage between the `R`-action and the `Γ(Spec R, V)`-action can be rewritten. -/
theorem eq_of_smul_eq_smul_tilde_sections (M : ModuleCat.{u} R)
    (f₀ : (Spec R).presheaf.obj (op (⊤ : (Spec R).Opens)))
    (hf : IsSMulRegular M ((Scheme.ΓSpecIso R).hom f₀))
    (V : (Spec R).Opens) (hV : V ≤ ⊤)
    {s t : Γ((tilde.functor R).obj M, V)}
    (hst : (Spec R).presheaf.map (homOfLE hV).op f₀ • s =
      (Spec R).presheaf.map (homOfLE hV).op f₀ • t) : s = t := by
  refine isSMulRegular_tilde_sections R M hf V (?_ :
    (Scheme.ΓSpecIso R).hom f₀ • s = (Scheme.ΓSpecIso R).hom f₀ • t)
  rw [AlgebraicGeometry.Scheme.Modules.smul_Spec_def,
    AlgebraicGeometry.Scheme.Modules.smul_Spec_def, Iso.hom_inv_id_apply]
  exact hst

variable (D : (Spec R).IdealSheafData)

/-- **Multiplication by the global generator of `I` is injective on the sections of `M̃`.** This is
clause (4) of [Stacks, Tag 0GT5] for the generator `g`, in the form
`Stacks.IdealTorsion.IsGeneratorRegularOn` records it. -/
theorem isGeneratorRegularOn_tilde (M : ModuleCat.{u} R)
    (g : (idealSheaf D).val.obj (op (⊤ : (Spec R).Opens)))
    (hM : IsSMulRegular M ((Scheme.ΓSpecIso R).hom
      (generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g))) :
    IsGeneratorRegularOn (Spec R).toRingedSpace (idealSheafι D)
      ((tilde.functor R).obj M) ⊤ g := by
  intro V hV s t hst
  rw [idealSection_naturality (Spec R).toRingedSpace (idealSheafι D) (homOfLE hV).op g] at hst
  exact eq_of_smul_eq_smul_tilde_sections R M
    (generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g) hM V hV hst

/-- **The sheaf attached to an `f`-torsion-free module is `I`-torsion free.** Let `D ⊆ Spec R` be
an effective Cartier divisor whose ideal sheaf `I` is generated over `Spec R` by the section `g`,
with image `f ∈ Γ(Spec R, ⊤)` — the hypothesis `D = V(f)` of [Stacks, Tag 0GTV] — and let `M` be
an `R`-module on which multiplication by `f` is injective. Then `M̃` has no `I`-torsion.

By [Stacks, Tag 0GT5] it suffices that multiplication by every local generator of `I` be
injective on the sections of `M̃`; a local generator divides the restriction of `g`, so this
follows from `isGeneratorRegularOn_tilde`. -/
theorem isIdealTorsionFree_tilde [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (M : ModuleCat.{u} R)
    (g : (idealSheaf D).val.obj (op (⊤ : (Spec R).Opens)))
    (hM : IsSMulRegular M ((Scheme.ΓSpecIso R).hom
      (generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g))) :
    IsIdealTorsionFree (Spec R).toRingedSpace (idealSheafι D) ((tilde.functor R).obj M) :=
  @isIdealTorsionFree_of_isGeneratorRegularOn_top (Spec R).toRingedSpace _ (idealSheafι D)
    inferInstance
    ((Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      (Spec R).toRingedSpace (idealSheaf D)).1 inferInstance)
    ((tilde.functor R).obj M) g (isGeneratorRegularOn_tilde R D M g hM)

/-- **The termwise form:** the complex of sheaves attached to a complex of `f`-torsion-free
modules has `I`-torsion-free terms. This is the hypothesis under which
`Stacks.Divisors.Eta.etaObjTildeIso` may be applied to `M̃^•`. -/
theorem isIdealTorsionFree_tildeComplex [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (Mc : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : (idealSheaf D).val.obj (op (⊤ : (Spec R).Opens)))
    (hMc : ∀ n : ℤ, IsSMulRegular (Mc.X n) ((Scheme.ΓSpecIso R).hom
      (generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g)))
    (n : ℤ) :
    IsIdealTorsionFree (Spec R).toRingedSpace (idealSheafι D)
      ((((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Mc).X n) :=
  isIdealTorsionFree_tilde R D (Mc.X n) g (hMc n)

/-- Every term of `M̃^•` is quasi-coherent; instance search does not see this across the
degreewise application of `Functor.mapHomologicalComplex`. -/
theorem isQuasicoherent_tildeComplex (Mc : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Mc).X
      n).IsQuasicoherent :=
  inferInstanceAs (((tilde.functor R).obj (Mc.X n)).IsQuasicoherent)

/-- **The chain-level input of the second assertion of [Stacks, Tag 0GTV], at a complex of the
shape `M̃^•`:** `η_I(M̃^•) ≅ (η_f Γ(Spec R, M̃^•))^~`. This is
`Stacks.Divisors.Eta.etaObjTildeIso` specialized to `M̃^•`, which is a well-formed term only
because of `isIdealTorsionFree_tildeComplex`: the décalage `η_I` is defined on complexes of
`I`-torsion-free modules and on no others. -/
noncomputable def etaObjTildeComplexIso [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (Mc : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : (idealSheaf D).val.obj (op (⊤ : (Spec R).Opens)))
    (hg : Stacks.IdealTorsion.GeneratesIdealOn (Spec R).toRingedSpace ⊤ g)
    (hMc : ∀ n : ℤ, IsSMulRegular (Mc.X n) ((Scheme.ΓSpecIso R).hom
      (generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g))) :
    @Stacks.IdealTorsion.Eta.etaObj (Spec R).toRingedSpace (idealSheaf D) (idealSheafι D)
        (mono_idealSheafι D) (isInvertible_idealSheaf D)
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Mc)
        (isIdealTorsionFree_tildeComplex R D Mc g hMc) ≅
      ((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (EtaComplex.etaObject
            (generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g)
            (Stacks.IdealTorsion.Eta.sectionsComplex (Spec R).toRingedSpace
              (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Mc) ⊤))) :=
  etaObjTildeIso R D (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj Mc)
    (isQuasicoherent_tildeComplex R Mc) (isIdealTorsionFree_tildeComplex R D Mc g hMc) g hg

end Stacks.Divisors.Eta

end
