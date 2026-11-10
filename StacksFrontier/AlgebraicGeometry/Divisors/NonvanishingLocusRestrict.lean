module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Restriction

/-!
# The nonvanishing locus of a section over an open, and of its image on the open subscheme

Let `X` be a scheme, `N` an `𝒪_X`-module and `U` an open of `X`. A section `s` of `N` over `U`
has a nonvanishing locus `U_s ⊆ U`, the points of `U` at which the germ of `s` does not lie in
`𝔪_y N_y`, and a global section of the pullback `U.ι^* N` of `N` to the open subscheme
`U.toScheme` has a nonvanishing locus in the sense of `Stacks.Ample.nonvanishingLocus`. This file
identifies the two: they correspond under the identification of the points of `U.toScheme` with
the points of `U`, for sections that correspond under the pullback-unit map
`Γ(N, U) → Γ(U.ι^* N, ⊤)`, which is a bijection with inverse
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`.

## Why this is here

`Stacks.Ample.nonvanishingLocus` takes a **global** section, so a section of `N` over an open `U`
has no nonvanishing locus in the repository's vocabulary at all, and the affine open that
ampleness produces on `U.toScheme` cannot be compared with anything on `X`. Two library
docstrings record this as the bookkeeping that is owed:
`StacksFrontier/AlgebraicGeometry/AmplePullbackPart1/Restriction.lean`, under
"What this does *not* give", says that "the nonvanishing locus of the resulting section over `U`
is not compared with the nonvanishing locus of the section of the restriction it came from", and
`StacksFrontier/AlgebraicGeometry/PullbackExtension/Basic.lean` lists as the first of the two
ingredients
still missing for part (1) of [Stacks, Tag 0892] "the nonvanishing open of a section of a module
over an open subscheme, and its compatibility with restriction along the open immersion". That
comparison is what this file supplies.

Its intended consumer is the general case of [Stacks, Tag 0AYM]: the quasi-affine clause is
`Stacks.QuasiAffineInvertibleSheaf`, and the general case needs a section of an invertible module
`N` over an affine open `X_s ⊆ X` that does not vanish at a prescribed finite set, which
`Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite_sections`
([Stacks, Tag 0F20]) produces as a global section of `U.ι^* N` on `U.toScheme`. No tag is
attached: this is infrastructure, not a numbered result of the source.

## Main definitions

* `Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn`: the nonvanishing locus `V_s ⊆ X` of a
  section `s` of a module over an open `V`, agreeing with `Stacks.Ample.nonvanishingLocus` at
  `V = ⊤` (`nonvanishingLocusOn_top`).
* `Stacks.NonvanishingLocusRestrict.restrictSection`: a section of `N` over `U`, read as a global
  section of `U.ι^* N` by the unit of the module-pullback adjunction.

## Main results

* `Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff`: for an **arbitrary**
  morphism of schemes `i` and a section `m` of `M` over an open `V`, the germ of `i^* m` at `x'`
  lies in `𝔪_{x'} (i^* M)_{x'}` exactly when the germ of `m` lies in `𝔪_{i x'} M_{i x'}`. This is
  the engine; it needs no invertibility and no hypothesis on `i`.
* `Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn`: consequently
  `i^{-1}(V_m) = (i^{-1} V)_{i^* m}`, which is [Stacks, Tag 0H78]
  (`Stacks.NonvanishingPullback.preimage_nonvanishingLocus`) for sections over an open rather
  than global ones.
* `Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocus_restrictSection_iff` and
  `nonvanishingLocus_restrictSection`: **the bridge.** For `U` an open of `X` and `s` a section
  of `N` over `U`, the nonvanishing locus of `restrictSection U N s` on `U.toScheme` is the
  preimage of `U_s` along `U.ι`.
* `Stacks.NonvanishingLocusRestrict.pullbackUnit_eq_restrictIsoPullback_hom_app`: the
  pullback-unit map at `U` **is** Mathlib's restriction-versus-pullback isomorphism read on
  sections, after the restriction of `s` from `U` to `U.ι ''ᵁ (U.ι ⁻¹ᵁ U)`.
* `Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection` and
  `restrictSection_sectionOfRestrictGlobalSection`: `restrictSection U N` and
  `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection U N` are mutually inverse
  bijections, so every global section of `U.ι^* N` is a `restrictSection`.
* `Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection`
  and `nonvanishingLocus_eq_preimage_of_sectionOfRestrictGlobalSection`: **the bridge in the
  direction a consumer uses it.** For an arbitrary global section `t` of `U.ι^* N`, the
  nonvanishing locus of `t` is the preimage along `U.ι` of the nonvanishing locus over `U` of the
  section `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection U N t` of `N`.

## Implementation notes

**The comparison is made through the module pullback and not through Mathlib's restriction.**
The stalk of `U.ι^* N` is identified with a base change of the stalk of `N` by [Stacks, Tag 0098]
(`Stacks.PullbackTensorIso.pullbackStalkEquiv`), whose germ formula
`Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul` is already stated over an arbitrary open,
and the transfer of `Stacks.ModuleStalk.maximalSmul` across it is
`Stacks.NonvanishingPullback.mem_maximalIdeal_smul_iff_one_tmul` together with the two bridges of
`StacksFrontier/AlgebraicGeometry/NonvanishingPullback/StalkBridge.lean`. So
`mem_maximalSmul_germ_pullbackUnit_iff` is
`Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff` with the open `⊤` replaced by an
arbitrary `V`, and nothing about stalks of a restricted presheaf is needed.

**The two sections are matched by the unit of the adjunction, not by the isomorphism.** The
pullback-unit map `Γ(N, U) → Γ(U.ι^* N, U.ι ⁻¹ᵁ U)` is what the stalk formula of Tag 0098 is
stated about, while `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` is built from
Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. They are identified
here: that isomorphism is `CategoryTheory.Adjunction.leftAdjointUniq` of the restriction
adjunction against the pullback adjunction, so
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` says exactly that composing it with the
unit of the restriction adjunction — which is a plain restriction map of `N`, by
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app` — gives the unit of the
pullback adjunction. The repository's `RingedSpaceModuleAdjunction.modulePullback` adjunction and
Mathlib's agree on the nose, so the latter unit is `Stacks.RingedSpace.pullbackUnit` by `rfl`.

**The target open of the unit is `U.ι ⁻¹ᵁ U` and not `⊤`.** These are equal opens of
`U.toScheme` but not the same term, so `restrictSection` interposes the restriction map along
`⊤ ≤ U.ι ⁻¹ᵁ U`; this is the same device that forces `sectionOfRestrictGlobalSection` to
interpose a transport along `AlgebraicGeometry.Scheme.Opens.ι_image_top`.

## References

* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AmplePullbackPart1 (restrictIsoPullback restrictGlobalSectionsIso
  sectionOfRestrictGlobalSection)
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.NonvanishingLocusRestrict

/-! ### The nonvanishing locus of a section over an open -/

section Locus

variable {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)

/-- **The nonvanishing locus `V_s` of a section `s` of `M` over the open `V`**: the points `y` of
`V` at which the germ of `s` does not lie in `𝔪_y M_y`. For `V = ⊤` this is
`Stacks.Ample.nonvanishingLocus`, and for `M` invertible it is the open set of
[Stacks, Tag 01CY] computed inside `V`. -/
def nonvanishingLocusOn (s : Γ(M, V)) : Set X :=
  {y | ∃ hy : y ∈ V, (M.presheaf.germ V y hy).hom s ∉ Stacks.ModuleStalk.maximalSmul M y}

/-- Membership in `V_s` at a point already known to lie in `V`. The proof that `y ∈ V` does not
matter, germs being independent of it. -/
theorem mem_nonvanishingLocusOn_iff {s : Γ(M, V)} {y : X} (hy : y ∈ V) :
    y ∈ nonvanishingLocusOn M V s ↔
      (M.presheaf.germ V y hy).hom s ∉ Stacks.ModuleStalk.maximalSmul M y :=
  ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

/-- A section over `V` can only fail to vanish inside `V`. -/
theorem nonvanishingLocusOn_subset (s : Γ(M, V)) : nonvanishingLocusOn M V s ⊆ V :=
  fun _ h => h.1

/-- **At `V = ⊤` this is the nonvanishing locus of a global section**, the one ampleness is
stated over. -/
theorem nonvanishingLocusOn_top (s : Γ(M, ⊤)) :
    nonvanishingLocusOn M ⊤ s = Stacks.Ample.nonvanishingLocus M s :=
  Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

end Locus

/-! ### The nonvanishing locus of the pullback of a section over an open -/

section Pullback

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (M : X.Modules)

/-- **[Stacks, Tag 0H78] for a section over an open, on germs.** For a morphism of schemes `i`, a
section `m` of `M` over an open `V` of `X` and a point `x'` of `X'` above `V`, the germ at `x'`
of the pullback of `m` lies in `𝔪_{x'} (i^* M)_{x'}` exactly when the germ of `m` at `i x'` lies
in `𝔪_{i x'} M_{i x'}`.

This is `Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff` with the open `⊤`
replaced by `V`: the germ formula of [Stacks, Tag 0098] that the argument runs through,
`Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul`, holds over an arbitrary open. Neither
invertibility of `M` nor any hypothesis on `i` is used. -/
theorem mem_maximalSmul_germ_pullbackUnit_iff {V : X.Opens} (m : Γ(M, V)) (x' : X')
    (hx' : i.base x' ∈ V) :
    ((Stacks.AmpleLocallyClosed.pullbackModule i M).presheaf.germ (i ⁻¹ᵁ V) x' hx').hom
          (Stacks.RingedSpace.pullbackUnit i.toLRSHom.toShHom M (op V) m) ∈
        Stacks.ModuleStalk.maximalSmul (Stacks.AmpleLocallyClosed.pullbackModule i M) x' ↔
      (M.presheaf.germ V (i.base x') hx').hom m ∈
        Stacks.ModuleStalk.maximalSmul M (i.base x') := by
  refine Iff.symm ?_
  refine Iff.trans (Stacks.NonvanishingPullback.mem_maximalSmul_iff M (i.base x') _) ?_
  refine Iff.trans ?_
    (Stacks.NonvanishingPullback.mem_maximalSmul_iff
      (Stacks.AmpleLocallyClosed.pullbackModule i M) x' _).symm
  refine Iff.trans
    (Stacks.NonvanishingPullback.mem_maximalIdeal_smul_iff_one_tmul
      (instAlg := Stacks.PullbackTensorIso.commStalkAlgebra i.toLRSHom.toShHom x')
      (instLoc := Stacks.NonvanishingPullback.isLocalHom_commStalkRingMap i x')
      (instMod := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val
        (i.base x'))
      ((M.presheaf.germ V (i.base x') hx').hom m)) ?_
  refine Iff.trans
    (Stacks.NonvanishingPullback.mem_ideal_smul_top_iff_of_linearEquiv _
      (Stacks.PullbackTensorIso.pullbackStalkEquiv i.toLRSHom.toShHom x' M) _) ?_
  exact Iff.of_eq (congrArg (fun z => z ∈
    IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
      X'.toRingedSpace x') • ⊤)
    (Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul i.toLRSHom.toShHom x' M V hx' m))

/-- **[Stacks, Tag 0H78] for a section over an open**: the inverse image of the nonvanishing
locus of `m` over `V` is the nonvanishing locus over `i^{-1} V` of the pullback of `m`. At
`V = ⊤` this is `Stacks.NonvanishingPullback.preimage_nonvanishingLocus`. -/
theorem preimage_nonvanishingLocusOn {V : X.Opens} (m : Γ(M, V)) :
    i.base ⁻¹' nonvanishingLocusOn M V m =
      nonvanishingLocusOn (Stacks.AmpleLocallyClosed.pullbackModule i M) (i ⁻¹ᵁ V)
        (Stacks.RingedSpace.pullbackUnit i.toLRSHom.toShHom M (op V) m) :=
  Set.ext fun x' =>
    ⟨fun h => ⟨h.1, fun hc =>
        h.2 ((mem_maximalSmul_germ_pullbackUnit_iff i M m x' h.1).mp hc)⟩,
      fun h => ⟨h.1, fun hc =>
        h.2 ((mem_maximalSmul_germ_pullbackUnit_iff i M m x' h.1).mpr hc)⟩⟩

end Pullback

/-! ### The bridge at an open subscheme -/

section Restrict

variable {X : Scheme.{u}} (U : X.Opens) (N : X.Modules)

/-- Every point of the open subscheme `U.toScheme` lies over `U`, so the inverse image of `U`
along `U.ι` is everything. Stated as an inequality rather than the equality `U.ι ⁻¹ᵁ U = ⊤`
because it is used as a morphism of opens. -/
theorem top_le_ι_preimage_self : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.2

/-- **A section of `N` over `U`, read as a global section of `U.ι^* N`**: the unit of the
module-pullback adjunction at `U`, followed by the restriction along
`Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self` that turns the open `U.ι ⁻¹ᵁ U` into
`⊤`. This is a bijection, inverse to
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`. -/
def restrictSection (s : Γ(N, U)) :
    Γ(Stacks.AmpleLocallyClosed.pullbackModule U.ι N, (⊤ : U.toScheme.Opens)) :=
  ((Stacks.AmpleLocallyClosed.pullbackModule U.ι N).presheaf.map
      (homOfLE (top_le_ι_preimage_self U)).op).hom
    (Stacks.RingedSpace.pullbackUnit U.ι.toLRSHom.toShHom N (op U) s)

/-- **The bridge, pointwise.** A point of `U.toScheme` lies in the nonvanishing locus of
`restrictSection U N s` exactly when its image in `X` lies in the nonvanishing locus of `s` over
`U`. -/
theorem mem_nonvanishingLocus_restrictSection_iff (s : Γ(N, U)) (x : U.toScheme) :
    x ∈ Stacks.Ample.nonvanishingLocus (Stacks.AmpleLocallyClosed.pullbackModule U.ι N)
        (restrictSection U N s) ↔
      U.ι.base x ∈ nonvanishingLocusOn N U s := by
  refine Iff.trans (Stacks.Ample.mem_nonvanishingLocus_iff _ _ x) ?_
  refine Iff.trans ?_
    (mem_nonvanishingLocusOn_iff N U (show U.ι.base x ∈ U from x.2)).symm
  refine not_congr ?_
  refine Iff.trans ?_ (mem_maximalSmul_germ_pullbackUnit_iff U.ι N s x x.2)
  exact Iff.of_eq (congrArg
    (· ∈ Stacks.ModuleStalk.maximalSmul (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) x)
    (TopCat.Presheaf.germ_res_apply (C := Ab.{u})
      (Stacks.AmpleLocallyClosed.pullbackModule U.ι N).presheaf
      (homOfLE (top_le_ι_preimage_self U)) x trivial _))

/-- **The bridge, as sets.** The nonvanishing locus of `restrictSection U N s` on `U.toScheme` is
the preimage along `U.ι` of the nonvanishing locus of `s` over `U`. -/
theorem nonvanishingLocus_restrictSection (s : Γ(N, U)) :
    Stacks.Ample.nonvanishingLocus (Stacks.AmpleLocallyClosed.pullbackModule U.ι N)
        (restrictSection U N s) =
      U.ι.base ⁻¹' nonvanishingLocusOn N U s :=
  Set.ext fun x => mem_nonvanishingLocus_restrictSection_iff U N s x

/-! ### The pullback unit at `U` is the restriction isomorphism -/

/-- **The unit of the module-pullback adjunction at `U` is Mathlib's restriction-versus-pullback
isomorphism, read on sections.** Both are maps out of `Γ(N, U)` once `s` has been restricted to
`U.ι ''ᵁ (U.ι ⁻¹ᵁ U)`, which is the module of sections of the restriction of `N` over
`U.ι ⁻¹ᵁ U`.

`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is
`CategoryTheory.Adjunction.leftAdjointUniq` of the restriction adjunction against the pullback
adjunction, so this is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read at `U`,
using that the unit of the restriction adjunction is a restriction map of `N`
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`) and that the repository's
pullback adjunction is Mathlib's. -/
theorem pullbackUnit_eq_restrictIsoPullback_hom_app (s : Γ(N, U)) :
    Stacks.RingedSpace.pullbackUnit U.ι.toLRSHom.toShHom N (op U) s =
      Scheme.Modules.Hom.app (restrictIsoPullback U N).hom (U.ι ⁻¹ᵁ U)
        ((N.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op).hom s) := by
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U)
    (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction U.ι)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) N)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at h
  exact (ConcreteCategory.congr_hom h s).symm

/-- Naturality of `Stacks.AmplePullbackPart1.restrictIsoPullback` on sections, for the inclusion
`⊤ ≤ U.ι ⁻¹ᵁ U`. -/
private theorem restrictIsoPullback_hom_app_res
    (z : Γ((Scheme.Modules.restrictFunctor U.ι).obj N, U.ι ⁻¹ᵁ U)) :
    ((Stacks.AmpleLocallyClosed.pullbackModule U.ι N).presheaf.map
          (homOfLE (top_le_ι_preimage_self U)).op).hom
        (Scheme.Modules.Hom.app (restrictIsoPullback U N).hom (U.ι ⁻¹ᵁ U) z) =
      Scheme.Modules.Hom.app (restrictIsoPullback U N).hom ⊤
        ((((Scheme.Modules.restrictFunctor U.ι).obj N).presheaf.map
          (homOfLE (top_le_ι_preimage_self U)).op).hom z) :=
  (ConcreteCategory.congr_hom
    ((restrictIsoPullback U N).hom.mapPresheaf.naturality
      (homOfLE (top_le_ι_preimage_self U)).op) z).symm

/-- An isomorphism of modules is undone by its inverse on sections over any open. -/
private theorem iso_inv_app_hom_app {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B) (W : Y.Opens)
    (z : Γ(A, W)) :
    Scheme.Modules.Hom.app e.inv W (Scheme.Modules.Hom.app e.hom W z) = z := by
  have h : Scheme.Modules.Hom.app e.hom W ≫ Scheme.Modules.Hom.app e.inv W = 𝟙 _ :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ W) e.hom_inv_id
  rw [← ConcreteCategory.comp_apply, h, CategoryTheory.id_apply]

/-- Two successive restriction maps of `N` between opens that are equal compose to the
identity. -/
private theorem map_map_self {A B : X.Opens} (f : op A ⟶ op B) (g : op B ⟶ op A)
    (x : Γ(N, A)) : (N.presheaf.map g).hom ((N.presheaf.map f).hom x) = x := by
  have h : N.presheaf.map f ≫ N.presheaf.map g = 𝟙 _ := by
    rw [← N.presheaf.map_comp, Subsingleton.elim (f ≫ g) (𝟙 (op A))]
    exact N.presheaf.map_id _
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using
    ConcreteCategory.congr_hom h x

/-- Three successive restriction maps of `N` whose opens return to where they started compose to
the identity. -/
private theorem map_map_map_self {A B C : X.Opens} (f : op A ⟶ op B) (g : op B ⟶ op C)
    (k : op C ⟶ op A) (x : Γ(N, A)) :
    (N.presheaf.map k).hom ((N.presheaf.map g).hom ((N.presheaf.map f).hom x)) = x := by
  simpa only [N.presheaf.map_comp, CategoryTheory.comp_apply] using
    map_map_self N (f ≫ g) k x

/-- **`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` undoes
`Stacks.NonvanishingLocusRestrict.restrictSection`.** The isomorphism is unwound by
`Stacks.NonvanishingLocusRestrict.pullbackUnit_eq_restrictIsoPullback_hom_app`, and what is left
is a composite of three restriction maps of `N` from `U` back to `U`. -/
theorem sectionOfRestrictGlobalSection_restrictSection (s : Γ(N, U)) :
    sectionOfRestrictGlobalSection U N (restrictSection U N s) = s := by
  have h1 : restrictSection U N s = Scheme.Modules.Hom.app (restrictIsoPullback U N).hom ⊤
      ((((Scheme.Modules.restrictFunctor U.ι).obj N).presheaf.map
          (homOfLE (top_le_ι_preimage_self U)).op).hom
        ((N.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op).hom s)) :=
    Eq.trans (congrArg (fun w => ((Stacks.AmpleLocallyClosed.pullbackModule U.ι N).presheaf.map
        (homOfLE (top_le_ι_preimage_self U)).op).hom w)
      (pullbackUnit_eq_restrictIsoPullback_hom_app U N s))
      (restrictIsoPullback_hom_app_res U N _)
  change (N.presheaf.map (eqToHom U.ι_image_top.symm).op).hom
      (Scheme.Modules.Hom.app (restrictIsoPullback U N).inv ⊤ (restrictSection U N s)) = s
  rw [h1, iso_inv_app_hom_app (restrictIsoPullback U N)]
  exact map_map_map_self N (homOfLE (U.ι.image_preimage_le U)).op
    (U.ι.opensFunctor.map (homOfLE (top_le_ι_preimage_self U))).op
    (eqToHom U.ι_image_top.symm).op s

/-- `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` is injective: it is a morphism of
modules that is part of an isomorphism, followed by a restriction map of `N` between two equal
opens. -/
theorem sectionOfRestrictGlobalSection_injective :
    Function.Injective (sectionOfRestrictGlobalSection U N) := by
  intro t t' h
  have h' : Scheme.Modules.Hom.app (restrictIsoPullback U N).inv ⊤ t =
      Scheme.Modules.Hom.app (restrictIsoPullback U N).inv ⊤ t' := by
    refine Eq.trans (map_map_self N (eqToHom U.ι_image_top.symm).op
      (eqToHom U.ι_image_top).op _).symm ?_
    exact Eq.trans (congrArg _ h)
      (map_map_self N (eqToHom U.ι_image_top.symm).op (eqToHom U.ι_image_top).op _)
  have hz : ∀ w : Γ(Stacks.AmpleLocallyClosed.pullbackModule U.ι N, (⊤ : U.toScheme.Opens)),
      Scheme.Modules.Hom.app (restrictIsoPullback U N).hom ⊤
        (Scheme.Modules.Hom.app (restrictIsoPullback U N).inv ⊤ w) = w :=
    iso_inv_app_hom_app (restrictIsoPullback U N).symm ⊤
  exact Eq.trans (hz t).symm (Eq.trans (congrArg _ h') (hz t'))

/-- **`Stacks.NonvanishingLocusRestrict.restrictSection` undoes
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`**, so the two are mutually inverse
bijections and *every* global section of `U.ι^* N` is the image of a section of `N` over `U`. -/
theorem restrictSection_sectionOfRestrictGlobalSection
    (t : Γ(Stacks.AmpleLocallyClosed.pullbackModule U.ι N, (⊤ : U.toScheme.Opens))) :
    restrictSection U N (sectionOfRestrictGlobalSection U N t) = t :=
  sectionOfRestrictGlobalSection_injective U N
    (sectionOfRestrictGlobalSection_restrictSection U N _)

/-- **The bridge in the direction a consumer uses it, pointwise.** For an arbitrary global
section `t` of `U.ι^* N`, a point of `U.toScheme` lies in the nonvanishing locus of `t` exactly
when its image in `X` lies in the nonvanishing locus over `U` of the section
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection U N t` of `N`. -/
theorem mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection
    (t : Γ(Stacks.AmpleLocallyClosed.pullbackModule U.ι N, (⊤ : U.toScheme.Opens)))
    (x : U.toScheme) :
    x ∈ Stacks.Ample.nonvanishingLocus (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) t ↔
      U.ι.base x ∈ nonvanishingLocusOn N U (sectionOfRestrictGlobalSection U N t) := by
  refine Iff.trans (Iff.of_eq (congrArg
    (fun w => x ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) w)
    (restrictSection_sectionOfRestrictGlobalSection U N t).symm)) ?_
  exact mem_nonvanishingLocus_restrictSection_iff U N _ x

/-- **The bridge in the direction a consumer uses it, as sets.** The nonvanishing locus on
`U.toScheme` of a global section `t` of `U.ι^* N` is the preimage along `U.ι` of the nonvanishing
locus over `U` of the corresponding section of `N`. -/
theorem nonvanishingLocus_eq_preimage_of_sectionOfRestrictGlobalSection
    (t : Γ(Stacks.AmpleLocallyClosed.pullbackModule U.ι N, (⊤ : U.toScheme.Opens))) :
    Stacks.Ample.nonvanishingLocus (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) t =
      U.ι.base ⁻¹' nonvanishingLocusOn N U (sectionOfRestrictGlobalSection U N t) :=
  Set.ext fun x => mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection U N t x

end Restrict

end Stacks.NonvanishingLocusRestrict

end
