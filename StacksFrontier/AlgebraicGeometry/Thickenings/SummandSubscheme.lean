module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cutting a first-order thickening down along a subsheaf of its conormal sheaf

Let `i : Z ⟶ W` be a first-order thickening of schemes, with defining ideal sheaf
`ℐ ⊆ 𝒪_W`. For a first-order thickening the conormal sheaf *is* that ideal sheaf,
`Stacks.Thickenings.firstOrderConormalIso`, and so it comes with an inclusion
`𝒞_{Z/W} ⟶ 𝒪_W`, `Stacks.Thickenings.firstOrderConormalSheafι`. Given a quasi-coherent
subsheaf `N ⊆ 𝒞_{Z/W}` we may therefore read `N` as a quasi-coherent sheaf of ideals
`𝒥 ⊆ ℐ ⊆ 𝒪_W` and cut out the closed subscheme `Z' = V(𝒥) ⊆ W`. Since `𝒥 ⊆ ℐ`, the
thickening `Z ⟶ W` factors through `Z'`, and since `ℐ² = 0 ⊆ 𝒥` the factor `Z ⟶ Z'` is again a
first-order thickening.

This is the step of [Stacks Project, Tag 06D8] that reads

> Let `Z' ⊂ Z''` be the closed subscheme cut out by `𝒞_{Z/X} ⊂ ℐ` viewed as a quasi-coherent
> sheaf of ideals on `Z''`. It is clear that `Z'` is a first-order thickening of `Z` […]

with `W = Z''` the universal first-order thickening of `Z` over `X'` and `N = 𝒞_{Z/X}` the
summand supplied by a splitting of the conormal sequence of [Stacks Project, Tag 06CC]; the
section of a splitting is a split monomorphism, which is the `Mono N ⟶ 𝒞_{Z/W}` hypothesis below.

## Main definitions

* `Stacks.Thickenings.subsheafOfIdealsOfMono`: the image of a monomorphism `κ : M ⟶ 𝒪_W`, as a
  sheaf of ideals in the sense of `CategoryTheory.SheafOfModules.Submodule`.
* `Stacks.Thickenings.idealSheafDataOfMono`: the same image as an
  `AlgebraicGeometry.Scheme.IdealSheafData`, through
  `Stacks.Divisors.idealSheafDataOfSubmodule`, the implication (2) ⟹ (3) of
  [Stacks Project, Tag 01QQ].
* `Stacks.Thickenings.monoSubscheme` and `Stacks.Thickenings.monoSubschemeι`: the closed
  subscheme `V(Im κ) ⊆ W` and its closed immersion.
* `Stacks.Thickenings.idealSheafIsoOfMono`: the identification of the source of `κ` with the
  defining ideal sheaf of `V(Im κ)`, and `Stacks.Thickenings.conormalSheafIsoOfMono` the
  identification with its conormal sheaf.
* `Stacks.Thickenings.toMonoSubscheme`: the factorization `Z ⟶ V(Im κ)` of a closed immersion
  `i : Z ⟶ W` whose structure-sheaf map kills `M`.
* `Stacks.Thickenings.conormalSummandι` and
  `Stacks.Thickenings.immersionConormalSummandι`: the inclusion `𝒥 ⟶ 𝒪_W` attached to a
  subsheaf of the conormal sheaf of a first-order thickening, in the two spellings of the
  conormal sheaf: `Stacks.Thickenings.schemeConormalSheaf`, built from
  the defining ideal sheaf of `i`, and `Stacks.Thickenings.immersionConormalSheaf`, the sheaf of
  [Stacks Project, Tag 01R2] built from the coborder factorization.

## Main results

* `Stacks.Thickenings.isFirstOrderThickening_toMonoSubscheme`: the factorization is a first-order
  thickening, provided `i` is.
* `Stacks.Thickenings.toMonoSubscheme_comp`: it is a factorization of `i`.
* `Stacks.Thickenings.ker_monoSubschemeι` together with
  `Stacks.Thickenings.ideal_idealSheafDataOfMono`: the subscheme is cut out by exactly the image
  of `κ`.
* `Stacks.Thickenings.ker_toMonoSubscheme_ideal`: the defining ideal of `Z` *inside* `Z'` is the
  image of the defining ideal of `Z` inside `W`, i.e. `ℐ/𝒥`.
* `Stacks.Thickenings.isFirstOrderThickening_monoSubschemeι`: `Z' ⊆ W` is a first-order
  thickening too, so `Z ⊆ Z' ⊆ W` is a chain of first-order thickenings.
* `Stacks.Thickenings.conormalSheafIsoOfMono_hom_ι` and
  `Stacks.Thickenings.idealSheafIsoOfMono_hom_ι`: the two identifications are the ones
  compatible with the inclusions into `𝒪_W`.
* `Stacks.Thickenings.exists_isFirstOrderThickening_conormalSummand` and
  `Stacks.Thickenings.exists_isFirstOrderThickening_immersionConormalSummand`: the two bundled
  forms, for a subsheaf of the conormal sheaf of a first-order thickening.

## Implementation notes

The image of a monomorphism of sheaves of modules is already a sheaf of submodules of the target,
`Stacks.SheafOfModules.monoRange`, and it is isomorphic to the source by
`Stacks.SheafOfModules.monoRangeIso`, which is how quasi-coherence is transported to it.
Quasi-coherence of the pushforward `i_* N` is
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`,
[Stacks Project, Tag 02KG], available because a closed immersion is affine; the two spellings
`AlgebraicGeometry.Scheme.Modules.pushforward i` and
`RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom` agree by `rfl`, but the
`IsQuasicoherent` instance has to be re-stated at the `AlgebraicGeometry.Scheme.Modules` spelling
for instance resolution to find it.

That `Z ⟶ W` factors through `V(𝒥)` is `AlgebraicGeometry.Scheme.Hom.toImage` followed by
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion`, the first an isomorphism because `i` is a
closed immersion; and that the factor is a first-order thickening is
`Stacks.Thickenings.isFirstOrderThickening_inclusion_of_sq_le`, whose hypothesis `ℐ² ≤ 𝒥` is
vacuous here because `ℐ² = ⊥`.

The second half of the paragraph of [Stacks Project, Tag 06D8], the identification
`𝒞_{Z/Z'} = i^* 𝒞_{X/X'}` of the conormal sheaf of the new thickening with the *complementary*
summand, is not proved here; `Stacks.Thickenings.ker_toMonoSubscheme_ideal` is its ideal-level
form, and `Stacks.Thickenings.conormalSheafIsoOfMono` identifies the left-hand term of the
conormal sequence of [Stacks Project, Tag 062S] for the chain `Z ⊆ Z' ⊆ W` with the subsheaf that
was cut out.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

variable {Z W : Scheme.{u}}

/-! ### The sheaf of ideals cut out by a monomorphism into the structure sheaf -/

section Ideal

variable {M : SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace)}
  (κ : M ⟶ SheafOfModules.unit (structureSheafRing W.toLocallyRingedSpace.toRingedSpace))
  (hκ : Mono κ)

/-- **The image of a monomorphism into `𝒪_W`, as a sheaf of ideals.** This is
`Stacks.SheafOfModules.monoRange`: the sectionwise ranges of a monomorphism of sheaves of modules
already form a sheaf of submodules of the target, and here the target is `𝒪_W`, so they form a
sheaf of ideals. -/
def subsheafOfIdealsOfMono : (SheafOfModules.unit W.ringCatSheaf).Submodule :=
  Stacks.SheafOfModules.monoRange κ hκ

/-- The sections of `Stacks.Thickenings.subsheafOfIdealsOfMono` over an open are the image of the
sections of `κ` there. -/
theorem obj_subsheafOfIdealsOfMono (V : W.Opens) :
    (subsheafOfIdealsOfMono κ hκ).toSubmodule.obj (op V) =
      LinearMap.range (κ.val.app (op V)).hom :=
  rfl

/-- **The image of a monomorphism out of a quasi-coherent module is quasi-coherent**, being
isomorphic to the source by `Stacks.SheafOfModules.monoRangeIso`. -/
instance isQuasicoherent_subsheafOfIdealsOfMono [M.IsQuasicoherent] :
    ((subsheafOfIdealsOfMono κ hκ).toSheafOfModules).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
    (Stacks.SheafOfModules.monoRangeIso κ hκ) ‹_›

/-- **The ideal sheaf datum cut out by the image of a monomorphism of a quasi-coherent module
into `𝒪_W`.** This is `Stacks.Divisors.idealSheafDataOfSubmodule`, the implication (2) ⟹ (3) of
[Stacks Project, Tag 01QQ], applied to
`Stacks.Thickenings.subsheafOfIdealsOfMono`. -/
def idealSheafDataOfMono [M.IsQuasicoherent] : W.IdealSheafData :=
  Stacks.Divisors.idealSheafDataOfSubmodule (X := W) (subsheafOfIdealsOfMono κ hκ)

/-- The ideal that `Stacks.Thickenings.idealSheafDataOfMono` cuts out on an affine open is the
image of the sections of `κ` there. -/
theorem ideal_idealSheafDataOfMono [M.IsQuasicoherent] (V : W.affineOpens) :
    (idealSheafDataOfMono κ hκ).ideal V = LinearMap.range (κ.val.app (op V.1)).hom :=
  rfl

/-- **The closed subscheme of `W` cut out by the image of `κ`.** -/
abbrev monoSubscheme [M.IsQuasicoherent] : Scheme.{u} := (idealSheafDataOfMono κ hκ).subscheme

/-- The closed immersion of `Stacks.Thickenings.monoSubscheme` into `W`. -/
abbrev monoSubschemeι [M.IsQuasicoherent] : monoSubscheme κ hκ ⟶ W :=
  (idealSheafDataOfMono κ hκ).subschemeι

/-- **`Stacks.Thickenings.monoSubscheme` is cut out by exactly the image of `κ`.** -/
theorem ker_monoSubschemeι [M.IsQuasicoherent] :
    (monoSubschemeι κ hκ).ker = idealSheafDataOfMono κ hκ :=
  Scheme.IdealSheafData.ker_subschemeι _

/-! ### The source of `κ` is the defining ideal sheaf of the subscheme -/

/-- **Every section of the image of `κ` dies on the subscheme it cuts out**, as a morphism-level
identity. -/
theorem comp_structureSheafModuleHom_monoSubschemeι [M.IsQuasicoherent] :
    κ ≫ structureSheafModuleHom (monoSubschemeι κ hκ).toLRSHom.toShHom = 0 := by
  ext V m
  exact Stacks.Divisors.subschemeι_app_eq_zero_of_mem (subsheafOfIdealsOfMono κ hκ) V.unop _
    ⟨m, rfl⟩

/-- The factorization of `κ` through the defining ideal sheaf of the subscheme it cuts out. -/
def toIdealSheafOfMono [M.IsQuasicoherent] :
    M ⟶ Stacks.ClosedImmersion.idealSheaf (monoSubschemeι κ hκ).toLRSHom.toShHom :=
  kernel.lift _ κ (comp_structureSheafModuleHom_monoSubschemeι κ hκ)

/-- `Stacks.Thickenings.toIdealSheafOfMono` followed by the inclusion of the ideal sheaf is `κ`. -/
@[simp]
theorem toIdealSheafOfMono_comp_ι [M.IsQuasicoherent] :
    toIdealSheafOfMono κ hκ ≫
        Stacks.ClosedImmersion.idealSheafι (monoSubschemeι κ hκ).toLRSHom.toShHom = κ :=
  kernel.lift_ι _ _ _

/-- `Stacks.Thickenings.toIdealSheafOfMono` is a monomorphism. -/
theorem mono_toIdealSheafOfMono [M.IsQuasicoherent] : Mono (toIdealSheafOfMono κ hκ) :=
  have := hκ
  mono_of_mono_fac (toIdealSheafOfMono_comp_ι κ hκ)

/-- `Stacks.Thickenings.toIdealSheafOfMono` is an epimorphism: over an affine open, the sections of
the defining ideal sheaf of `Stacks.Thickenings.monoSubscheme` are the image of `κ`. -/
theorem epi_toIdealSheafOfMono [M.IsQuasicoherent] : Epi (toIdealSheafOfMono κ hκ) := by
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun U t x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  obtain ⟨a, ha⟩ : ∃ a : Γ(W, V), (Stacks.ClosedImmersion.idealSheafι
      (monoSubschemeι κ hκ).toLRSHom.toShHom).val.app (op V)
      ((Stacks.ClosedImmersion.idealSheaf
        (monoSubschemeι κ hκ).toLRSHom.toShHom).val.map (homOfLE hVU).op t) = a := ⟨_, rfl⟩
  have h0 : ((monoSubschemeι κ hκ).app V).hom a = 0 := by
    rw [← ha]
    exact congr($(show Stacks.ClosedImmersion.idealSheafι
      (monoSubschemeι κ hκ).toLRSHom.toShHom ≫
        structureSheafModuleHom (monoSubschemeι κ hκ).toLRSHom.toShHom = 0 from
      kernel.condition _).val.app (op V) _)
  have hmem : a ∈ LinearMap.range (κ.val.app (op V)).hom := by
    have h1 : a ∈ (monoSubschemeι κ hκ).ker.ideal ⟨V, hV⟩ := by
      rw [Scheme.Hom.ker_apply]
      exact RingHom.mem_ker.2 h0
    rwa [ker_monoSubschemeι, ideal_idealSheafDataOfMono] at h1
  obtain ⟨m, hm⟩ := hmem
  exact ⟨V, hVU, hxV, m, Stacks.ClosedImmersion.injective_idealSheafι_val_app
    (monoSubschemeι κ hκ).toLRSHom.toShHom V
    ((congr($(toIdealSheafOfMono_comp_ι κ hκ).val.app (op V) m)).trans (hm.trans ha.symm))⟩

/-- **The source of `κ` is the defining ideal sheaf of the closed subscheme it cuts out**, by the
factorization `Stacks.Thickenings.toIdealSheafOfMono` of `κ` through that ideal sheaf. -/
def idealSheafIsoOfMono [M.IsQuasicoherent] :
    M ≅ Stacks.ClosedImmersion.idealSheaf (monoSubschemeι κ hκ).toLRSHom.toShHom :=
  haveI := mono_toIdealSheafOfMono κ hκ
  haveI := epi_toIdealSheafOfMono κ hκ
  haveI := isIso_of_mono_of_epi (toIdealSheafOfMono κ hκ)
  asIso (toIdealSheafOfMono κ hκ)

/-- The forward map of `Stacks.Thickenings.idealSheafIsoOfMono` is
`Stacks.Thickenings.toIdealSheafOfMono`. -/
@[simp]
theorem idealSheafIsoOfMono_hom [M.IsQuasicoherent] :
    (idealSheafIsoOfMono κ hκ).hom = toIdealSheafOfMono κ hκ :=
  rfl

/-- `Stacks.Thickenings.idealSheafIsoOfMono` followed by the inclusion of the ideal sheaf into
`𝒪_W` is `κ`. -/
@[simp]
theorem idealSheafIsoOfMono_hom_ι [M.IsQuasicoherent] :
    (idealSheafIsoOfMono κ hκ).hom ≫
        Stacks.ClosedImmersion.idealSheafι (monoSubschemeι κ hκ).toLRSHom.toShHom = κ := by
  rw [idealSheafIsoOfMono_hom, toIdealSheafOfMono_comp_ι]

end Ideal

/-! ### The closed subscheme it cuts out, and that it is a first-order thickening -/

section Thickening

variable {M : SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace)}
  (κ : M ⟶ SheafOfModules.unit (structureSheafRing W.toLocallyRingedSpace.toRingedSpace))
  (hκ : Mono κ) [M.IsQuasicoherent] (i : Z ⟶ W) [IsClosedImmersion i]

/-- **A monomorphism into `𝒪_W` killed by the structure-sheaf map of `i` has image inside the
defining ideal sheaf of `i`.** -/
theorem idealSheafDataOfMono_le_ker
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    idealSheafDataOfMono κ hκ ≤ i.ker := by
  refine Scheme.IdealSheafData.le_def.2 fun V => ?_
  rw [ideal_idealSheafDataOfMono, Scheme.Hom.ker_apply i V]
  rintro x ⟨m, rfl⟩
  refine RingHom.mem_ker.2 ?_
  exact congr(($hvanish).val.app (op V.1) m)

/-- **The defining ideal sheaf of the subscheme cut out by a subsheaf of the defining ideal of a
first-order thickening has vanishing square.** -/
theorem ker_monoSubschemeι_sq_eq_bot (hsq : i.ker ^ 2 = ⊥)
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    (monoSubschemeι κ hκ).ker ^ 2 = ⊥ := by
  have hle := Scheme.IdealSheafData.le_def.mp
    ((ker_monoSubschemeι κ hκ).le.trans (idealSheafDataOfMono_le_ker κ hκ i hvanish))
  refine le_bot_iff.mp (Scheme.IdealSheafData.le_def.2 fun V => ?_)
  have hV : ((i.ker ^ 2).ideal V : Ideal Γ(W, V.1)) = ⊥ :=
    congrArg (fun J : W.IdealSheafData => J.ideal V) hsq
  refine le_trans ?_ hV.le
  rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Pi.pow_apply, pow_two, pow_two]
  exact Ideal.mul_mono (hle V) (hle V)

/-- **The subscheme cut out by a subsheaf of the defining ideal of a first-order thickening is
itself a first-order thickening of `W`**, so that `Z ⊆ V(Im κ) ⊆ W` is a chain of first-order
thickenings. -/
theorem isFirstOrderThickening_monoSubschemeι (hsq : i.ker ^ 2 = ⊥)
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    IsFirstOrderThickening (monoSubschemeι κ hκ) :=
  ⟨inferInstance, ker_monoSubschemeι_sq_eq_bot κ hκ i hsq hvanish⟩

/-- **The conormal sheaf of the subscheme cut out by `κ` is the source of `κ`.** For a first-order
thickening the conormal sheaf is the defining ideal sheaf,
`Stacks.Thickenings.firstOrderConormalIso`, and the defining ideal sheaf of `V(Im κ)` is the
source of `κ` by `Stacks.Thickenings.idealSheafIsoOfMono`.

This is the left-hand term of the conormal sequence of [Stacks Project, Tag 062S] for the chain
`Z ⊆ V(Im κ) ⊆ W`, identified with the subsheaf that was cut out. -/
def conormalSheafIsoOfMono (hsq : i.ker ^ 2 = ⊥)
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    M ≅ (modulePushforward (monoSubschemeι κ hκ).toLRSHom.toShHom).obj
      (schemeConormalSheaf (monoSubschemeι κ hκ)) :=
  idealSheafIsoOfMono κ hκ ≪≫
    firstOrderConormalIso (monoSubschemeι κ hκ) (ker_monoSubschemeι_sq_eq_bot κ hκ i hsq hvanish)

/-- **The identification of `Stacks.Thickenings.conormalSheafIsoOfMono` is the one compatible with
the inclusions into `𝒪_W`**: followed by the inclusion of the conormal sheaf of `V(Im κ)` into
`𝒪_W` it is `κ`. -/
@[simp]
theorem conormalSheafIsoOfMono_hom_ι (hsq : i.ker ^ 2 = ⊥)
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    (conormalSheafIsoOfMono κ hκ i hsq hvanish).hom ≫
        firstOrderConormalSheafι (monoSubschemeι κ hκ)
          (ker_monoSubschemeι_sq_eq_bot κ hκ i hsq hvanish) = κ := by
  have hdef : firstOrderConormalSheafι (monoSubschemeι κ hκ)
        (ker_monoSubschemeι_sq_eq_bot κ hκ i hsq hvanish) =
      (firstOrderConormalIso (monoSubschemeι κ hκ)
          (ker_monoSubschemeι_sq_eq_bot κ hκ i hsq hvanish)).inv ≫
        Stacks.ClosedImmersion.idealSheafι (monoSubschemeι κ hκ).toLRSHom.toShHom := rfl
  rw [conormalSheafIsoOfMono, hdef, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, idealSheafIsoOfMono_hom_ι]

/-- **The factorization of `i` through the subscheme cut out by the image of `κ`.** The
scheme-theoretic image of a closed immersion is the immersion itself,
`AlgebraicGeometry.Scheme.Hom.toImage` being an isomorphism, and the containment
`Im κ ⊆ Ker i^♯` gives the inclusion of closed subschemes. -/
def toMonoSubscheme (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    Z ⟶ monoSubscheme κ hκ :=
  i.toImage ≫ Scheme.IdealSheafData.inclusion (idealSheafDataOfMono_le_ker κ hκ i hvanish)

/-- `Stacks.Thickenings.toMonoSubscheme` is a factorization of `i`. -/
theorem toMonoSubscheme_comp
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    toMonoSubscheme κ hκ i hvanish ≫ monoSubschemeι κ hκ = i := by
  rw [toMonoSubscheme, Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

/-- **The subscheme cut out by a subsheaf of the defining ideal of a first-order thickening is
again a first-order thickening of `Z`**: the factorization `Stacks.Thickenings.toMonoSubscheme`
is a first-order thickening. -/
theorem isFirstOrderThickening_toMonoSubscheme (hsq : i.ker ^ 2 = ⊥)
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    IsFirstOrderThickening (toMonoSubscheme κ hκ i hvanish) := by
  have hfo := isFirstOrderThickening_inclusion_of_sq_le
    (idealSheafDataOfMono_le_ker κ hκ i hvanish) ((le_of_eq hsq).trans bot_le)
  refine ⟨?_, ?_⟩
  · have := hfo.1
    exact inferInstanceAs (IsClosedImmersion (i.toImage ≫ _))
  · rw [toMonoSubscheme, Scheme.Hom.ker_comp_of_isIso]
    exact hfo.2

/-- **The defining ideal of `Z` inside the subscheme `V(Im κ)` is `ℐ/Im κ`.** Over the chart of
`V(Im κ)` lying above an affine open `V` of `W`, the ideal cutting out `Z` is the image of the
ideal `ℐ(V)` cutting out `Z` in `W` under the surjection
`Γ(W, V) ⟶ Γ(V(Im κ), V)`.

This is the ideal-level form of the identification of `𝒞_{Z/V(Im κ)}` with the complementary
summand: the defining ideal drops by exactly the subsheaf that was cut out. -/
theorem ker_toMonoSubscheme_ideal
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) (V : W.affineOpens) :
    (toMonoSubscheme κ hκ i hvanish).ker.ideal
        ⟨monoSubschemeι κ hκ ⁻¹ᵁ V.1, V.2.preimage (monoSubschemeι κ hκ)⟩ =
      Ideal.map ((monoSubschemeι κ hκ).app V.1).hom (i.ker.ideal V) := by
  rw [toMonoSubscheme, Scheme.Hom.ker_comp_of_isIso]
  exact Stacks.ClosedImmersion.ker_inclusion_ideal _ V

/-- The bundled form of the construction: the subscheme cut out by a monomorphism `κ` into `𝒪_W`
killed by the structure-sheaf map of a first-order thickening `i`. -/
private theorem exists_isFirstOrderThickening_of_mono (hκ : Mono κ) (hsq : i.ker ^ 2 = ⊥)
    (hvanish : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    ∃ (Z' : Scheme.{u}) (i' : Z ⟶ Z') (q : Z' ⟶ W), IsFirstOrderThickening i' ∧
      IsClosedImmersion q ∧ i' ≫ q = i ∧
      ∀ V : W.affineOpens, q.ker.ideal V = LinearMap.range (κ.val.app (op V.1)).hom :=
  ⟨monoSubscheme κ hκ, toMonoSubscheme κ hκ i hvanish, monoSubschemeι κ hκ,
    isFirstOrderThickening_toMonoSubscheme κ hκ i hsq hvanish, inferInstance,
    toMonoSubscheme_comp κ hκ i hvanish, fun V => by
      rw [ker_monoSubschemeι, ideal_idealSheafDataOfMono]⟩

end Thickening

/-! ### The case of a subsheaf of the conormal sheaf -/

section Conormal

variable (i : Z ⟶ W) [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)

/-- **The inclusion of the conormal sheaf of a first-order thickening into `𝒪_W` is killed by the
structure-sheaf map of the thickening.** The inclusion factors through the defining ideal sheaf,
which is the kernel of that map. -/
theorem firstOrderConormalSheafι_comp_structureSheafModuleHom :
    firstOrderConormalSheafι i hsq ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0 := by
  have hdef : firstOrderConormalSheafι i hsq =
      (firstOrderConormalIso i hsq).inv ≫
        Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom := rfl
  rw [hdef, Category.assoc,
    show Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom ≫
        structureSheafModuleHom i.toLRSHom.toShHom = 0 from kernel.condition _,
    comp_zero]

/-- **The inclusion of the conormal sheaf of [Stacks Project, Tag 01R2] of a first-order thickening
into `𝒪_W` is killed by the structure-sheaf map of the thickening.** -/
theorem firstOrderImmersionConormalSheafι_comp_structureSheafModuleHom :
    firstOrderImmersionConormalSheafι i hsq ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0 := by
  have hdef : firstOrderImmersionConormalSheafι i hsq =
      (modulePushforward i.toLRSHom.toShHom).map (Stacks.Immersion.conormalSheafSelfIso i).inv ≫
        firstOrderConormalSheafι i hsq := rfl
  rw [hdef, Category.assoc, firstOrderConormalSheafι_comp_structureSheafModuleHom, comp_zero]

/-- **The pushforward of a quasi-coherent module along a closed immersion of schemes is
quasi-coherent** ([Stacks Project, Tag 02KG]), at the
`RingedSpaceModuleAdjunction.modulePushforward` spelling. -/
@[sga "3 I 4.2" "special case", sga "6 III 1.2.1" "forward implication"]
theorem isQuasicoherent_modulePushforward
    {N : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    (hN : N.IsQuasicoherent) :
    ((modulePushforward i.toLRSHom.toShHom).obj N).IsQuasicoherent := by
  have : (show Z.Modules from N).IsQuasicoherent := hN
  exact Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom i
    (show Z.Modules from N)

section SchemeConormal

variable {N : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
  (β : N ⟶ schemeConormalSheaf i)

/-- **A subsheaf of the conormal sheaf of a first-order thickening, read as a sheaf of ideals of
`𝒪_W`.** The conormal sheaf of a first-order thickening sits inside `𝒪_W` by
`Stacks.Thickenings.firstOrderConormalSheafι`, so a subsheaf of it does too. -/
def conormalSummandι : (modulePushforward i.toLRSHom.toShHom).obj N ⟶
    SheafOfModules.unit (structureSheafRing W.toLocallyRingedSpace.toRingedSpace) :=
  (modulePushforward i.toLRSHom.toShHom).map β ≫ firstOrderConormalSheafι i hsq

/-- `Stacks.Thickenings.conormalSummandι` is a monomorphism when `β` is. -/
theorem mono_conormalSummandι (hβ : Mono β) : Mono (conormalSummandι i hsq β) := by
  have := hβ
  have := modulePushforward_isRightAdjoint i.toLRSHom.toShHom
  have := mono_firstOrderConormalSheafι i hsq
  exact mono_comp _ _

/-- `Stacks.Thickenings.conormalSummandι` is killed by the structure-sheaf map of `i`. -/
theorem conormalSummandι_comp_structureSheafModuleHom :
    conormalSummandι i hsq β ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0 := by
  rw [conormalSummandι, Category.assoc,
    firstOrderConormalSheafι_comp_structureSheafModuleHom, comp_zero]

/-- **The closed subscheme of `W` cut out by a quasi-coherent subsheaf of the conormal sheaf of a
first-order thickening `Z ⟶ W` is again a first-order thickening of `Z`**, and it is cut out by
exactly that subsheaf.

This is the construction of the closed subscheme `Z' ⊂ Z''` in the proof of
[Stacks Project, Tag 06D8]. -/
theorem exists_isFirstOrderThickening_conormalSummand (hβ : Mono β) (hN : N.IsQuasicoherent) :
    ∃ (Z' : Scheme.{u}) (i' : Z ⟶ Z') (q : Z' ⟶ W), IsFirstOrderThickening i' ∧
      IsClosedImmersion q ∧ i' ≫ q = i ∧
      ∀ V : W.affineOpens, q.ker.ideal V =
        LinearMap.range ((conormalSummandι i hsq β).val.app (op V.1)).hom := by
  have := isQuasicoherent_modulePushforward i (N := N) hN
  exact exists_isFirstOrderThickening_of_mono _ i (mono_conormalSummandι i hsq β hβ) hsq
    (conormalSummandι_comp_structureSheafModuleHom i hsq β)

end SchemeConormal

section ImmersionConormal

variable {N : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
  (β : N ⟶ immersionConormalSheaf i)

/-- **`Stacks.Thickenings.conormalSummandι` for the conormal sheaf of
[Stacks Project, Tag 01R2].** -/
def immersionConormalSummandι : (modulePushforward i.toLRSHom.toShHom).obj N ⟶
    SheafOfModules.unit (structureSheafRing W.toLocallyRingedSpace.toRingedSpace) :=
  (modulePushforward i.toLRSHom.toShHom).map β ≫ firstOrderImmersionConormalSheafι i hsq

/-- `Stacks.Thickenings.immersionConormalSummandι` is a monomorphism when `β` is. -/
theorem mono_immersionConormalSummandι (hβ : Mono β) :
    Mono (immersionConormalSummandι i hsq β) := by
  have := hβ
  have := modulePushforward_isRightAdjoint i.toLRSHom.toShHom
  have := mono_firstOrderImmersionConormalSheafι i hsq
  exact mono_comp _ _

/-- `Stacks.Thickenings.immersionConormalSummandι` is killed by the structure-sheaf map of `i`. -/
theorem immersionConormalSummandι_comp_structureSheafModuleHom :
    immersionConormalSummandι i hsq β ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0 := by
  rw [immersionConormalSummandι, Category.assoc,
    firstOrderImmersionConormalSheafι_comp_structureSheafModuleHom, comp_zero]

/-- **The closed subscheme of `W` cut out by a quasi-coherent subsheaf of the conormal sheaf of
[Stacks Project, Tag 01R2] of a first-order thickening `Z ⟶ W` is again a first-order thickening
of `Z`**, and it is cut out by exactly that subsheaf.

This is the construction of the closed subscheme `Z' ⊂ Z''` in the proof of
[Stacks Project, Tag 06D8], in the spelling of the conormal sheaf that the splitting of the
conormal sequence of [Stacks Project, Tag 06CC] produces. -/
theorem exists_isFirstOrderThickening_immersionConormalSummand
    (hβ : Mono β) (hN : N.IsQuasicoherent) :
    ∃ (Z' : Scheme.{u}) (i' : Z ⟶ Z') (q : Z' ⟶ W), IsFirstOrderThickening i' ∧
      IsClosedImmersion q ∧ i' ≫ q = i ∧
      ∀ V : W.affineOpens, q.ker.ideal V =
        LinearMap.range ((immersionConormalSummandι i hsq β).val.app (op V.1)).hom := by
  have := isQuasicoherent_modulePushforward i (N := N) hN
  exact exists_isFirstOrderThickening_of_mono _ i (mono_immersionConormalSummandι i hsq β hβ) hsq
    (immersionConormalSummandι_comp_structureSheafModuleHom i hsq β)

end ImmersionConormal

end Conormal

end Stacks.Thickenings

end
