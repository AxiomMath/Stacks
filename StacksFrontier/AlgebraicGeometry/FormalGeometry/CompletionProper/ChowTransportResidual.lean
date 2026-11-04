module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.C1018Assembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedImmersionAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GeneralBaseAssembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.IdealSheafCongrTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportAlgebraization
public import StacksFrontier.AlgebraicGeometry.Scheme.SubschemeIdealJoin
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chow residual of `hSupp`: the dévissage of Stacks 088E runs on `V(K)`

The hypothesis `hSupp` of [Stacks, Tag 088E] is, by
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_iff`, the single properness statement

  `IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f)` for every coherent `𝓘`-adic system `𝓕`
  whose first term has support proper over `A`,

and the module
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ProperSupportAlgebraization.lean`
reduces it to two binders: [Stacks, Tag 088B] at the hypotheses the source states it with
(`Stacks.Algebraization.IsDirectImageComparison`) and the Chow transport `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport`. **This file discharges the
second from the first**, and so proves the properness statement, `hSupp`, and `hTransport` itself
from [Stacks, Tag 088B] alone.

## Why the dévissage cannot be run on `X`, and what is run instead

`hTransport` and the `hChow` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_chowComparison` ask, at each
quasi-coherent ideal sheaf `K`, for Chow data on `X` whose dense open `U` satisfies the join
clause `∀ e, K < K ⊔ 𝒦 ᵉ⁺¹` for `𝒦` the vanishing ideal of `X \ U`. That clause is equivalent to
`𝒦 ᵉ⁺¹ ≰ K` for every `e`, and `Stacks.Algebraization.lt_sup_pow_vanishingIdeal_compl` below
isolates what it demands: the open `U` must **meet the support of `K`**, since `𝒦 ᵉ⁺¹ ≤ K` forces
`V(K) ⊆ supp 𝒦 = X \ U`. Chow's lemma on `X` returns an open which is dense in `X`, and a dense
open misses a nowhere dense `V(K)` — the modification of `𝔸¹` which is an isomorphism over the
punctured line does not see the origin. So the clause is not available at the `U` Chow's lemma on
`X` delivers, and an `U` meeting `V(K)` cannot be had from a modification of `V(K)` either: such
a modification factors through the closed immersion, so an open of `X` over which it is an
isomorphism lies inside `V(K)`, which has empty interior in general.

The source does not run its dévissage on `X`. It replaces `X` by `V(K)`, where the system is
killed by `⊥`, and runs Chow's lemma there; the ideal sheaves at which its induction hypothesis is
consumed are the inverse images in `X` of the ideal sheaves of `V(K)`, the **joins** of
`StacksFrontier/AlgebraicGeometry/Scheme/SubschemeIdealJoin.lean`, and those are not powers of any
ideal sheaf of `X` (`Stacks.IdealSheafData.pow_map_le_map_pow`). This file carries that
replacement for the proper-annihilator statement, exactly as
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/SubschemeDevissage.lean` carries it
for the essential-image statement of [Stacks, Tag 088C].

**After the replacement the side condition is trivial.** On `V(K)` the system is killed by `⊥` and
the clause reads `∀ e, ⊥ < ⊥ ⊔ 𝒦₀ ᵉ⁺¹`, i.e. `𝒦₀ ᵉ⁺¹ ≠ ⊥`, which is
`Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top` from
`Stacks.IdealSheafData.support_compl_ne_top_of_dense`. Nothing of the `.map` family of joins is
needed in the clause itself; it is needed only to transport the induction hypothesis, through
`Stacks.IdealSheafData.lt_map_subschemeι_iff`.

## The two transports along the closed immersion

Everything else is bookkeeping across `i = K.subschemeι`, and it is done here without any
exactness property of `i_*`, because the *conclusion* is transported rather than the comparison
map of [Stacks, Tag 088B]: the comparison, the kernel step and the two Serre subcategories of
[Stacks, Tag 0CYV] all stay on `V(K)`, inside
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_comparison` read at the base
morphism `K.subschemeι ≫ f`. What crosses `i` is

* **properness of a closed subscheme**, in both directions — `J.comap i` downstairs from `J`
  upstairs and `J₀.map i` upstairs from `J₀` downstairs. Both are one fact: a closed immersion
  equals its own scheme-theoretic image up to the isomorphism
  `AlgebraicGeometry.Scheme.Hom.toImage`, and `Scheme.IdealSheafData.map` *is* the kernel of the
  composite, so the subscheme of the pushed-forward ideal sheaf is the same scheme;
* **proper support**, in both directions, through
  `AlgebraicGeometry.supp_pushforward_of_isClosedImmersion`; and
* **the system itself**, by [Stacks, Tag 087T] at every level
  (`Stacks.Coherent.exists_system_pushforward_iso`), with
  `Stacks.Coherent.isCoherentAdicSystem_of_pushforward` to see the result in
  `Coh(V(K), 𝓘 𝒪_{V(K)})`. Annihilation crosses by
  `Stacks.Coherent.idealPowerMultiple_pushforward_eq_bot_iff` in both directions, and in each the
  containment `(J.map i).comap i ≤ J` is used in the direction that *weakens* the annihilating
  ideal sheaf, so no equality `(J.map i).comap i = J` is needed.

## Main results

* `Stacks.Algebraization.lt_sup_pow_vanishingIdeal_compl` — the join clause on `X` holds as soon
  as the open meets the support of `K`, and (`…_support_subset_compl_of_pow_le`) it fails as soon
  as a power of the vanishing ideal lies below `K`. This is what the binder `hTransport` demands
  of its open, and the reason the dévissage is not run on `X`.
* `Stacks.Algebraization.isProper_subschemeι_map_comp` and
  `Stacks.Algebraization.isProper_subschemeι_comap_comp` — properness of a closed subscheme
  across a closed immersion, in both directions.
* `Stacks.Algebraization.hasProperSupport_pushforward_of_isClosedImmersion` and
  `Stacks.Algebraization.hasProperSupport_of_pushforward_of_isClosedImmersion` — proper support
  across a closed immersion, in both directions.
* `Stacks.Algebraization.exists_coherentAdicSystems_comap_subschemeι_iso` — a coherent `𝓘`-adic
  system on `X` killed by `K` is the direct image of a coherent `𝓘 𝒪_{V(K)}`-adic system on
  `V(K)`.
* `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_chowStep` — **the dévissage
  step at `⊥` on a nonempty base**, from [Stacks, Tag 088B] and the statement at every nonzero
  ideal sheaf. This is where Chow's lemma, the projective case and 088B are consumed; stated for
  an arbitrary separated, locally of finite type, quasi-compact `g : Z ⟶ Spec A`, since after the
  replacement that is all `V(K)` is.
* `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_subscheme_of_hInd` — the induction
  hypothesis on `X` transported to `V(K)`, at every nonzero ideal sheaf of `V(K)`.
* `Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_isDirectImageComparison` — **the
  properness statement behind `hSupp`, from [Stacks, Tag 088B] alone.**
* `Stacks.Algebraization.hSupp_of_isDirectImageComparison` — `hSupp` itself, verbatim the binder
  of `Stacks.Algebraization.isEquivalence_completionFunctorProperOver`.
* `Stacks.Algebraization.transport_of_isDirectImageComparison` — **the binder `hTransport`,
  discharged**, through its left disjunct: the degenerate disjunct of the repaired statement is
  the conclusion of the previous theorem, so the Chow data is never produced. This is what the
  disjunction is for; the non-disjunctive form is refuted by
  `Stacks.Algebraization.not_transportDefective` and could not be proved this way.

## References

* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0CYV](https://stacks.math.columbia.edu/tag/0CYV)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### What the join clause on `X` demands of its open -/

/-- The support of the vanishing ideal sheaf of a closed subset is that closed subset. -/
private theorem support_vanishingIdeal_eq {X : Scheme.{u}} (W : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal W).support = W :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal W)

/-- **A power of an ideal sheaf below `K` forces the support of `K` inside the support of that
ideal sheaf.** The support is antitone and the support of a positive power is the support
(`AlgebraicGeometry.Scheme.IdealSheafData.support_pow_succ`), so `𝒦 ᵉ⁺¹ ≤ K` puts `V(K)` inside
`supp 𝒦`.

Read at `𝒦` the vanishing ideal of the complement of an open `U`, whose support is that
complement, this says that the join clause `K < K ⊔ 𝒦 ᵉ⁺¹` of the binders `hChow` and
`hTransport` can only hold when `U` meets `V(K)`. See the module docstring. -/
public theorem support_le_support_of_pow_succ_le {X : Scheme.{u}} {K 𝒦 : X.IdealSheafData}
    {e : ℕ} (h : 𝒦 ^ (e + 1) ≤ K) : K.support ≤ 𝒦.support := by
  have h1 : K.support ≤ (𝒦 ^ (e + 1)).support := Scheme.IdealSheafData.support_antitone h
  rwa [Scheme.IdealSheafData.support_pow_succ] at h1

/-- **The join clause of `hTransport`, from the open meeting the support of `K`.** If some point
of `V(K)` lies in `U` then no power of the vanishing ideal sheaf of `X \ U` lies below `K`, so
`K < K ⊔ 𝒦 ᵉ⁺¹` for every `e`.

This is the exact content of the clause: `Stacks.Algebraization.support_le_support_of_pow_succ_le`
gives the converse. Chow's lemma on `X` produces a *dense* open, which need not meet `V(K)`, and
that is why the dévissage of [Stacks, Tag 088E] is run on `V(K)` instead; see the module
docstring. -/
public theorem lt_sup_pow_vanishingIdeal_compl {X : Scheme.{u}} (K : X.IdealSheafData)
    (U : X.Opens) {x : X} (hxU : x ∈ U) (hxK : x ∈ (K.support : Set X)) (e : ℕ) :
    K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)) ^ (e + 1) := by
  refine lt_of_le_of_ne le_sup_left fun h => ?_
  have hle := support_le_support_of_pow_succ_le (e := e) (sup_eq_left.mp h.symm)
  have hmem := hle hxK
  rw [support_vanishingIdeal_eq] at hmem
  exact hmem hxU

/-! ### Properness of a closed subscheme across a closed immersion -/

/-- Properness over the base of the scheme-theoretic image of a closed immersion, from properness
of the closed immersion itself over the base. The canonical map to the image is an isomorphism
(`AlgebraicGeometry.Scheme.Hom.toImage`). -/
private theorem isProper_ker_subschemeι_comp {W X S : Scheme.{u}} (c : W ⟶ X)
    [IsClosedImmersion c] (g : X ⟶ S) (h : IsProper (c ≫ g)) :
    IsProper (c.ker.subschemeι ≫ g) := by
  have := h
  have hinv : IsProper (inv c.toImage ≫ c ≫ g) := inferInstance
  have heq : c.ker.subschemeι ≫ g = inv c.toImage ≫ c ≫ g := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, Scheme.Hom.toImage_imageι]
  rw [heq]
  exact hinv

/-- The converse: a closed immersion is proper over the base as soon as its scheme-theoretic
image is. -/
private theorem isProper_comp_of_isProper_ker_subschemeι {W X S : Scheme.{u}} (c : W ⟶ X)
    [IsClosedImmersion c] (g : X ⟶ S) (h : IsProper (c.ker.subschemeι ≫ g)) :
    IsProper (c ≫ g) := by
  have := h
  have hc : IsProper (c.toImage ≫ c.ker.subschemeι ≫ g) := inferInstance
  have heq : c ≫ g = c.toImage ≫ c.ker.subschemeι ≫ g := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  rw [heq]
  exact hc

/-- A larger quasi-coherent ideal sheaf cuts out a smaller closed subscheme, so properness over
the base is inherited upwards in the lattice. -/
private theorem isProper_subschemeι_comp_of_le {X S : Scheme.{u}} (g : X ⟶ S)
    {J L : X.IdealSheafData} (hJL : J ≤ L) (hJ : IsProper (J.subschemeι ≫ g)) :
    IsProper (L.subschemeι ≫ g) := by
  have := hJ
  have hincl : IsProper (Scheme.IdealSheafData.inclusion hJL ≫ J.subschemeι ≫ g) :=
    inferInstance
  rwa [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι] at hincl

/-- **Properness over the base ascends along a closed immersion.** If the closed subscheme of
`J₀ ⊆ 𝒪_Z` is proper over `S` along `i ≫ g` then the closed subscheme of its inverse image
`J₀.map i ⊆ 𝒪_X` is proper over `S` along `g`: the two closed subschemes are the same scheme,
`Scheme.IdealSheafData.map` being by definition the kernel of `J₀.subschemeι ≫ i`. -/
public theorem isProper_subschemeι_map_comp {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (g : X ⟶ S) (J₀ : Z.IdealSheafData)
    (hJ₀ : IsProper (J₀.subschemeι ≫ i ≫ g)) :
    IsProper ((J₀.map i).subschemeι ≫ g) :=
  isProper_ker_subschemeι_comp (J₀.subschemeι ≫ i) g (by rwa [Category.assoc])

/-- **Properness over the base descends along a closed immersion.** If the closed subscheme of
`J ⊆ 𝒪_X` is proper over `S` along `g` then the closed subscheme of `J.comap i ⊆ 𝒪_Z` is proper
over `S` along `i ≫ g`.

The closed subscheme of `J.comap i`, pushed into `X`, is cut out by `(J.comap i).map i`, which
lies above `J` by the Galois connection
(`AlgebraicGeometry.Scheme.IdealSheafData.le_map_comap`); a larger ideal sheaf cuts out a closed
subscheme of `V(J)`, and a closed subscheme of a closed subscheme proper over the base is proper
over the base. -/
public theorem isProper_subschemeι_comap_comp {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (g : X ⟶ S) (J : X.IdealSheafData)
    (hJ : IsProper (J.subschemeι ≫ g)) :
    IsProper ((J.comap i).subschemeι ≫ i ≫ g) := by
  have h := isProper_comp_of_isProper_ker_subschemeι ((J.comap i).subschemeι ≫ i) g
    (isProper_subschemeι_comp_of_le g (Scheme.IdealSheafData.le_map_comap J i) hJ)
  rwa [Category.assoc] at h

/-! ### Proper support across a closed immersion -/

/-- **Proper support ascends along a closed immersion.** A closed immersion is proper, so this is
`Stacks.Algebraization.hasProperSupport_properPushforwardCoherent` at `π = i`, whose underlying
module is the direct image on the nose
(`Stacks.Algebraization.properPushforwardCoherent_obj`). -/
public theorem hasProperSupport_pushforward_of_isClosedImmersion {Z X S : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] (g : X ⟶ S)
    [LocallyOfFiniteType g] (N : Z.Modules) [N.IsCoherent]
    (h : HasProperSupport (i ≫ g) N) :
    HasProperSupport g ((Scheme.Modules.pushforward i).obj N) :=
  hasProperSupport_properPushforwardCoherent i g ⟨N, inferInstance⟩ h

/-- **Proper support descends along a closed immersion.** If the direct image of `N` along the
closed immersion `i` has support proper over `S` then so does `N`, along `i ≫ g`: the support of
`N` is carried into the support of `i_* N`, and the preimage of a closed subset proper over `S`
carries the closed subscheme structure `(vanishingIdeal W).comap i`, proper over `S` by
`Stacks.Algebraization.isProper_subschemeι_comap_comp`. -/
public theorem hasProperSupport_of_pushforward_of_isClosedImmersion {Z X S : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (g : X ⟶ S) [LocallyOfFiniteType g] (N : Z.Modules)
    [N.IsCoherent]
    (h : HasProperSupport g ((Scheme.Modules.pushforward i).obj N)) :
    HasProperSupport (i ≫ g) N := by
  have : N.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := N)
  obtain ⟨W, hWeq, hWp⟩ := h
  refine ⟨⟨_root_.SheafOfModules.supp N, _root_.SheafOfModules.isClosed_supp N⟩, rfl, ?_⟩
  have hsub : (⟨_root_.SheafOfModules.supp N, _root_.SheafOfModules.isClosed_supp N⟩ :
      Closeds Z) ≤ W.preimage i.continuous := by
    intro z hz
    show i.base z ∈ (W : Set X)
    rw [hWeq, AlgebraicGeometry.supp_pushforward_of_isClosedImmersion i N]
    exact ⟨z, hz, rfl⟩
  refine isProperOver_of_le (i ≫ g) hsub ?_
  refine (isProperOver_iff_exists_isProper (i ≫ g) (W.preimage i.continuous)).2
    ⟨(Scheme.IdealSheafData.vanishingIdeal W).comap i, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.support_comap, support_vanishingIdeal_eq]
  · exact isProper_subschemeι_comap_comp i g _ hWp

/-! ### The system across the closed immersion -/

/-- **A coherent adic system killed by `K` is the direct image of one on `V(K)`.** Each term is
the direct image of a coherent module by [Stacks, Tag 087T], the terms are assembled into a
system by `Stacks.Coherent.exists_system_pushforward_iso`, and the system downstairs is a coherent
adic system along the inverse image of `𝓘` by
`Stacks.Coherent.isCoherentAdicSystem_of_pushforward`. -/
public theorem exists_coherentAdicSystems_comap_subschemeι_iso {X : Scheme.{u}}
    [IsLocallyNoetherian X] (ℐ K : X.IdealSheafData) [IsLocallyNoetherian K.subscheme]
    (𝓕 : CoherentAdicSystems ℐ) (hK : IsSystemAnnihilatedBy K 𝓕.obj) :
    ∃ 𝓕₀ : CoherentAdicSystems (ℐ.comap K.subschemeι),
      Nonempty (𝓕₀.obj ⋙ Scheme.Modules.pushforward K.subschemeι ≅ 𝓕.obj) := by
  have hAK : ∀ n : ℕᵒᵖ,
      Stacks.AlgebraicGeometry.Tag087TCoherentImage.AnnihilatedByKer K.subschemeι
        (𝓕.obj.obj n) := by
    intro n
    have h2 := Stacks.Coherent.annihilatedByKer_subschemeι_pow_iff K 1 (𝓕.obj.obj n)
    rw [pow_one] at h2
    exact h2.mpr (hK n.unop)
  obtain ⟨Q, hQcoh, ⟨eQ⟩⟩ := Stacks.Coherent.exists_system_pushforward_iso K.subschemeι 𝓕.obj
    (fun n => 𝓕.property.isCoherent n.unop) hAK
  exact ⟨⟨Q, Stacks.Coherent.isCoherentAdicSystem_of_pushforward K.subschemeι ℐ Q hQcoh
    (isCoherentAdicSystem_of_iso ℐ eQ.symm 𝓕.property)⟩, ⟨eQ⟩⟩

/-- A system annihilated by `L` has direct image annihilated by `L.map i`. -/
private theorem isSystemAnnihilatedBy_pushforward_map {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (L : Z.IdealSheafData) {F : ℕᵒᵖ ⥤ Z.Modules}
    (h : IsSystemAnnihilatedBy L F) :
    IsSystemAnnihilatedBy (L.map i) (F ⋙ Scheme.Modules.pushforward i) := fun n =>
  (idealPowerMultiple_pushforward_eq_bot_iff i (L.map i) 1 (F.obj (op n))).mpr
    (h.mono (Scheme.IdealSheafData.comap_map_le L i) n)

/-! ### The dévissage step after the replacement -/

section ChowStep

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]

/-- **The dévissage step of Stacks 088E at `⊥`, from [Stacks, Tag 088B].** Let `A` be Noetherian
and complete with respect to `I` and let `g : Z ⟶ Spec A` be separated, locally of finite type and
quasi-compact with `Z` **nonempty**. Granted [Stacks, Tag 088B] and the conclusion of `hSupp` at
every *nonzero* quasi-coherent ideal sheaf of `Z`, every coherent `𝓘 𝒪_Z`-adic system whose first
term has support proper over `A` is annihilated by the ideal sheaf of a closed subscheme of `Z`
proper over `A`.

This is the position the source occupies after replacing `X` by `V(K)`: there the system is killed
by `⊥`, the induction hypothesis is available at every nonzero ideal sheaf, and the side condition
of the inductive step reads `∀ e, ⊥ < ⊥ ⊔ 𝒦₀ ᵉ⁺¹`, i.e. `𝒦₀ ᵉ⁺¹ ≠ ⊥`, which
`Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top` supplies from
`Stacks.IdealSheafData.support_compl_ne_top_of_dense`. Nonemptiness of `Z` is what density of the
Chow open is consumed through, and the only thing it is consumed through.

The geometry is
`Stacks.Algebraization.exists_hasProperSupport_iso_coherentAdicPullback_of_denseChowModification`
— Chow's lemma with a projective compactification, the projective case of Grothendieck existence
on it and the no-escape argument from completeness of `A`, all unconditional — and the comparison
is `h088B`; the algebra is
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_comparison`, which consumes the
kernel step and the two Serre subcategories of [Stacks, Tag 0CYV].

The ideal sheaf is carried as a parameter equal to `baseIdealSheaf A I g` rather than as that
term, so that the inverse image `(baseIdealSheaf A I f).comap K.subschemeι` can be substituted at
the point of use without transporting a system along an equality of ideal sheaves. -/
public theorem exists_isProper_isSystemAnnihilatedBy_of_chowStep {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of A)) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Nonempty Z]
    (ℐ : Z.IdealSheafData) (hℐ : ℐ = baseIdealSheaf A I g)
    (h088B : IsDirectImageComparison.{u})
    (hInd : letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
      ∀ L : Z.IdealSheafData, ⊥ < L →
        ∀ 𝓖 : CoherentAdicSystems ℐ, IsSystemAnnihilatedBy L 𝓖.obj →
          HasProperSupport g (𝓖.obj.obj (op 0)) →
            ∃ J : Z.IdealSheafData, IsProper (J.subschemeι ≫ g) ∧
              IsSystemAnnihilatedBy J 𝓖.obj) :
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
    ∀ 𝓕 : CoherentAdicSystems ℐ, HasProperSupport g (𝓕.obj.obj (op 0)) →
      ∃ J : Z.IdealSheafData, IsProper (J.subschemeι ≫ g) ∧ IsSystemAnnihilatedBy J 𝓕.obj := by
  subst hℐ
  let _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  let _ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  let _ : IsNoetherian Z := { }
  intro 𝓕 h𝓕
  obtain ⟨Y, π, hπ, hY, U, hisoU, hU, G, hG, ⟨β⟩⟩ :=
    exists_hasProperSupport_iso_coherentAdicPullback_of_denseChowModification A I g 𝓕 h𝓕
  have := hπ
  have := hY
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Z)).support.compl = U := by
    rw [support_vanishingIdeal_eq]
    exact TopologicalSpace.Opens.ext (compl_compl _)
  have hiso' : IsIso (π ∣_ (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Z)).support.compl) := by
    rw [hsupp]; exact hisoU
  obtain ⟨α, hα⟩ := h088B π (baseIdealSheaf A I g) _ G 𝓕 β hiso'
  refine exists_isProper_isSystemAnnihilatedBy_of_comparison g (baseIdealSheaf A I g) ⊥ _
    (fun e => ?_) (fun L hL => hInd L hL) 𝓕 (isSystemAnnihilatedBy_bot 𝓕.obj) h𝓕
    (properPushforwardCoherent π G) (hasProperSupport_properPushforwardCoherent π g G hG) α hα
  rw [bot_sup_eq]
  exact bot_lt_iff_ne_bot.mpr (Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top
    (Stacks.IdealSheafData.support_compl_ne_top_of_dense U hU) e)

end ChowStep

/-! ### The induction hypothesis transported to `V(K)` -/

section Transport

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]

omit [IsAdicComplete I A] in
/-- **The induction hypothesis on `X` read on `V(K)`, at every nonzero ideal sheaf.** With `f`
separated, locally of finite type and quasi-compact over a Noetherian complete `A`, assume the
conclusion of `hSupp` for every coherent `𝓘`-adic system on `X` with proper support killed by an
ideal sheaf **strictly larger** than `K`. Then it holds for every coherent `𝓘 𝒪_{V(K)}`-adic
system on `V(K)` with proper support killed by a **nonzero** ideal sheaf of `V(K)`.

This is the source's "we may assume that every nonzero `𝒦` is in `Ξ`", and it is [Stacks, Tag
087T] at the level of systems in the ascending direction: the direct image of the system is a
coherent `𝓘`-adic system on `X`
(`Stacks.Coherent.isCoherentAdicSystem_pushforward_closedImmersion`) with support proper over `A`
(`Stacks.Algebraization.hasProperSupport_pushforward_of_isClosedImmersion`) killed by the inverse
image `L.map K.subschemeι`, which is the join `K ⊔ L` and lies **strictly** above `K` exactly
because `L ≠ ⊥` (`Stacks.IdealSheafData.lt_map_subschemeι_iff`). The annihilator the hypothesis
returns comes back as its inverse image `J.comap K.subschemeι`, proper over `A` by
`Stacks.Algebraization.isProper_subschemeι_comap_comp`. -/
public theorem exists_isProper_isSystemAnnihilatedBy_subscheme_of_hInd
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]
    (K : X.IdealSheafData)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f), IsSystemAnnihilatedBy K' 𝓖.obj →
          HasProperSupport f (𝓖.obj.obj (op 0)) →
            ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
              IsSystemAnnihilatedBy J 𝓖.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsLocallyNoetherian K.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
    ∀ L : K.subscheme.IdealSheafData, ⊥ < L →
      ∀ 𝓖 : CoherentAdicSystems ((baseIdealSheaf A I f).comap K.subschemeι),
        IsSystemAnnihilatedBy L 𝓖.obj →
          HasProperSupport (K.subschemeι ≫ f) (𝓖.obj.obj (op 0)) →
            ∃ J₀ : K.subscheme.IdealSheafData,
              IsProper (J₀.subschemeι ≫ K.subschemeι ≫ f) ∧ IsSystemAnnihilatedBy J₀ 𝓖.obj := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := { }
  let _ : CompactSpace K.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (K.subschemeι ≫ f)
  let _ : IsNoetherian K.subscheme := { }
  intro L hL 𝓖 h𝓖ann h𝓖supp
  have : (𝓖.obj.obj (op 0)).IsCoherent := 𝓖.property.isCoherent 0
  have hP : IsCoherentAdicSystem (baseIdealSheaf A I f)
      (𝓖.obj ⋙ Scheme.Modules.pushforward K.subschemeι) :=
    isCoherentAdicSystem_pushforward_closedImmersion K.subschemeι (baseIdealSheaf A I f)
      𝓖.obj 𝓖.property
  have hsupp : HasProperSupport f
      ((𝓖.obj ⋙ Scheme.Modules.pushforward K.subschemeι).obj (op 0)) :=
    hasProperSupport_pushforward_of_isClosedImmersion K.subschemeι f _ h𝓖supp
  obtain ⟨J, hJp, hJann⟩ := hInd (L.map K.subschemeι)
    ((Stacks.IdealSheafData.lt_map_subschemeι_iff K L).mpr (bot_lt_iff_ne_bot.mp hL))
    ⟨_, hP⟩ (isSystemAnnihilatedBy_pushforward_map K.subschemeι L h𝓖ann) hsupp
  refine ⟨J.comap K.subschemeι, isProper_subschemeι_comap_comp K.subschemeι f J hJp, fun n => ?_⟩
  exact (idealPowerMultiple_pushforward_eq_bot_iff K.subschemeι J 1 (𝓖.obj.obj (op n))).mp
    (hJann n)

end Transport

/-! ### `hSupp` from Stacks 088B alone -/

section Assembly

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]

/-- **The properness statement behind `hSupp`, from [Stacks, Tag 088B] alone.** Let `A` be
Noetherian and complete with respect to `I` and let `f : X ⟶ Spec A` be separated, locally of
finite type and quasi-compact. Then for every coherent `𝓘`-adic system whose first term has
support proper over `A`, the closed subscheme cut out by
`Stacks.Algebraization.systemAnnihilatorIdeal` is proper over `A`.

**The binder `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` is discharged by this
theorem**, through its left disjunct; see
`Stacks.Algebraization.transport_of_isDirectImageComparison`. The route taken here is not the one
that binder describes: the Noetherian induction is carried over the ideal sheaves of `X`, as in
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_devissage`, but each step is run
on `V(K)` after the source's replacement, because the join clause that step needs on `X` demands
an open meeting `V(K)` over which the modification is an isomorphism, which Chow's lemma on `X`
does not give. See the module docstring, and
`Stacks.Algebraization.lt_sup_pow_vanishingIdeal_compl` for the clause.

Completeness of `A` is consumed only inside
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_chowStep`, through the no-escape
argument on the projective compactification — the source's own accounting. -/
public theorem isProper_systemAnnihilatorIdeal_of_isDirectImageComparison
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u}) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro 𝓖 h𝓖
  refine (exists_isProper_isSystemAnnihilatedBy_iff f 𝓖).1 ?_
  refine exists_isProper_isSystemAnnihilatedBy_of_devissage f (baseIdealSheaf A I f)
    (fun K hInd 𝓕 hK h𝓕 => ?_) 𝓖 h𝓖
  by_cases hKtop : K = ⊤
  · -- `V(⊤)` is empty: the system is zero and the unit ideal sheaf is its proper annihilator
    subst hKtop
    refine ⟨⊤, ?_, hK⟩
    exact (exists_isProper_iff_forall_isProper f (⊥ : Closeds X)).1
      ((isProperOver_iff_exists_isProper f (⊥ : Closeds X)).1 (isProperOver_bot f)) ⊤
      Scheme.IdealSheafData.support_top
  -- the replacement of `X` by `V(K)`
  let _ : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  have hne : Nonempty K.subscheme := by
    obtain ⟨x, hx⟩ : ((K.support : Set X)).Nonempty := Set.nonempty_iff_ne_empty.2 fun h =>
      hKtop (K.support_eq_bot_iff.mp (TopologicalSpace.Closeds.ext h))
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx
    exact ⟨hx.choose⟩
  obtain ⟨𝓕₀, ⟨eQ⟩⟩ := exists_coherentAdicSystems_comap_subschemeι_iso
    (baseIdealSheaf A I f) K 𝓕 hK
  have h𝓕₀ : HasProperSupport (K.subschemeι ≫ f) (𝓕₀.obj.obj (op 0)) := by
    have : (𝓕₀.obj.obj (op 0)).IsCoherent := 𝓕₀.property.isCoherent 0
    refine hasProperSupport_of_pushforward_of_isClosedImmersion K.subschemeι f _ ?_
    obtain ⟨W, hWeq, hWp⟩ := h𝓕
    exact ⟨W, hWeq.trans (_root_.SheafOfModules.supp_eq_of_iso (eQ.app (op 0))).symm, hWp⟩
  obtain ⟨J₀, hJ₀p, hJ₀ann⟩ := exists_isProper_isSystemAnnihilatedBy_of_chowStep A I
    (K.subschemeι ≫ f) ((baseIdealSheaf A I f).comap K.subschemeι)
    (Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f K.subschemeι) h088B
    (exists_isProper_isSystemAnnihilatedBy_subscheme_of_hInd A I f K hInd) 𝓕₀ h𝓕₀
  refine ⟨J₀.map K.subschemeι,
    isProper_subschemeι_map_comp K.subschemeι f J₀ hJ₀p, fun n => ?_⟩
  refine idealPowerMultiple_eq_bot_of_iso (J₀.map K.subschemeι) (eQ.app (op n)).symm 1 ?_
  exact isSystemAnnihilatedBy_pushforward_map K.subschemeι J₀ hJ₀ann n

/-- **The hypothesis `hSupp` of Stacks 088E, from [Stacks, Tag 088B] alone.** This is verbatim
the binder `hSupp` of `Stacks.Algebraization.isEquivalence_completionFunctorProperOver`, read
through `Stacks.Algebraization.hSupp_of_isProper_systemAnnihilatorIdeal` out of the previous
theorem. -/
public theorem hSupp_of_isDirectImageComparison
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u}) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
          IsSystemAnnihilatedBy J 𝓖.obj :=
  hSupp_of_isProper_systemAnnihilatorIdeal A I f
    (isProper_systemAnnihilatorIdeal_of_isDirectImageComparison A I f h088B)

/-- **The binder `hTransport`, discharged from [Stacks, Tag 088B].** This is verbatim the
hypothesis `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` and of the 088E assembly,
proved for every `K` through its **left disjunct**: the canonical annihilator of a system with
proper support already cuts out a closed subscheme proper over `A`, by
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_isDirectImageComparison`. The Chow data
of the right disjunct is never produced, and on `X` it cannot be — see the module docstring.

**This is what the disjunction is for.** The non-disjunctive form of the binder is refuted
outright by `Stacks.Algebraization.not_transportDefective`, so no proof of it exists; the
degenerate disjunct, which is the conclusion the induction wants of the system at that stage, is
exactly what makes the repaired statement provable. -/
public theorem transport_of_isDirectImageComparison
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u}) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : IsNoetherian X := { }
    ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
      IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
          ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (_ : IsProper π) (_ : IsNoetherian Y) (U : X.Opens),
            IsIso (π ∣_ U) ∧
              (∀ e : ℕ, K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
                  (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)) ^ (e + 1)) ∧
                ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
                  HasProperSupport (π ≫ f) G.obj ∧
                    Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                      (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj G) :=
  fun _ 𝓕 _ h𝓕 => Or.inl
    (isProper_systemAnnihilatorIdeal_of_isDirectImageComparison A I f h088B 𝓕 h𝓕)

/-- **[Stacks, Tag 088E], Grothendieck's existence theorem with proper support, from [Stacks, Tag
088B] alone.**
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` with
its binder `hTransport` discharged by `Stacks.Algebraization.transport_of_isDirectImageComparison`:
for `A` Noetherian and complete along `I` and `f : X ⟶ Spec A` separated, locally of finite type
and quasi-compact, the functor of [Stacks, Tag 088D] is an equivalence granted 088B at the
hypotheses the source states it with, and nothing else.

Both of the binders the source's proof leaves — `hDev`, through
`Stacks.Algebraization.hDev_of_isDirectImageComparison`, and `hSupp`, through this file — are
therefore discharged from the one comparison statement.

No `stacks` attribute is attached: Stacks 088E is registered on
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver`. -/
public theorem isEquivalence_completionFunctorProperOver_of_isDirectImageComparison_alone
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u}) :
    (completionFunctorProperOver A I f).IsEquivalence :=
  isEquivalence_completionFunctorProperOver_of_isDirectImageComparison A I f h088B
    (transport_of_isDirectImageComparison A I f h088B)

/-- **[Stacks, Tag 088E] from the base change at the completion chart of each affine open
alone.**
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_adicCompletionChartBaseChange`
with its binder `hTransport` discharged: the Chow residual of that assembly is gone, so the whole
of Grothendieck existence with proper support over a separated, locally of finite type,
quasi-compact base rests on `Stacks.Algebraization.HasAdicCompletionChartBaseChange` and nothing
else.

No `stacks` attribute is attached: Stacks 088E is registered on
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver`. -/
public theorem isEquivalence_completionFunctorProperOver_of_adicCompletionChartBaseChange_alone
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : HasAdicCompletionChartBaseChange.{u}) :
    (completionFunctorProperOver A I f).IsEquivalence :=
  isEquivalence_completionFunctorProperOver_of_adicCompletionChartBaseChange A I f h
    (transport_of_isDirectImageComparison A I f
      (isDirectImageComparison_of_adicCompletionChartBaseChange h))

end Assembly

end Stacks.Algebraization

end
