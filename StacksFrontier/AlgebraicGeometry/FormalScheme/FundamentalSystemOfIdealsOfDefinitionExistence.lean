module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumComponentIso
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumMappingLimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSheaf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinition
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpaceGlue
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionKernel
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionLocality

/-!
# Fundamental systems of ideals of definition on quasi-compact quasi-separated formal schemes

**Stacks 0AJF** translates Stacks 0AJE into the language of formal schemes à la EGA:

> Every quasi-compact and quasi-separated formal scheme has a fundamental system of ideals of
> definition.

This file constructs that system. Let `𝔛` be a quasi-compact quasi-separated formal scheme, and
cover it by finitely many affine formal opens `𝔘ᵢ ≅ Spf Aᵢ`. For every choice of ideals of
definition `Jᵢ ⊆ Aᵢ`, the closed subschemes `Spec (Aᵢ/Jᵢ) → 𝔘ᵢ ⊆ 𝔛` have kernel ideal sheaves
`ker(Spec (Aᵢ/Jᵢ) → 𝔛) ⊆ 𝒪_𝔛`, and their intersection `ℐ_J = ⋂ᵢ ker(Spec (Aᵢ/Jᵢ) → 𝔛)` is an
ideal sheaf on `𝔛`. The family of all `ℐ_J` is nonempty, sectionwise directed, and a fundamental
system of ideals of definition: over every quasi-compact open — in particular over every affine
formal open subscheme — each `ℐ_J` has an ideal of definition for its ideal of sections, and these
ideals of sections form a neighbourhood basis of zero.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.instInfSet`: the sectionwise
  intersection of a family of ideal sheaves.
* `AlgebraicGeometry.spfChartHom`: the open immersion `Spf A ≅ 𝔛|_𝔘 ⊆ 𝔛` of an affine formal
  chart, as a morphism of locally topologically ringed spaces.
* `AlgebraicGeometry.spfChartPoint`: the closed subscheme `Spec (A/J) → Spf A → 𝔛` of a chart
  attached to an ideal of definition `J` of `A`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ker_app_pow_eq_bot`: for a morphism `f : X ⟶ Y` of affine schemes
  whose map on global sections has a kernel with vanishing `m`-th power, the map on sections over
  every open of `Y` has a kernel with vanishing `m`-th power.
* `AlgebraicGeometry.exists_ker_spfProjection_pow_le`: over any open of `Spf A`, a power of the
  kernel of the projection `𝒪_{Spf A} → 𝒪_J` lies in the kernel of the projection onto any other
  term `𝒪_L` of the inverse system.
* `AlgebraicGeometry.isIdealOfDefinition_ker_spfChartPoint`: over a quasi-compact open inside the
  chart, the kernel ideal sheaf of `Spec (A/J) → 𝔛` has an ideal of definition for its sections.
* `AlgebraicGeometry.exists_isFundamentalSystemOfIdealsOfDefinitionOn_isCompact_of_isFormalScheme`:
  the system over all quasi-compact opens.
* `AlgebraicGeometry.exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFormalScheme`:
  **Stacks 0AJF**, the system over the affine formal open subschemes.

## Implementation notes

**The construction, and how it relates to the source's.** The source argues by the induction
principle for quasi-compact quasi-separated formal schemes (Stacks 01P0): with `𝔛 = 𝔘 ∪ 𝔙`, `𝔙`
affine and the result known on `𝔘`, `𝔙` and `𝔘 ∩ 𝔙`, it glues the scheme-theoretic images
`Z_U` of `U ⨿ (𝔘 ∩ V) → U'` and `Z_V` of `(U ∩ 𝔙) ⨿ V → V'` to a scheme `Z → 𝔛` and takes its
ideal `ℐ_Z`. Unwinding the induction, `Z` is the scheme-theoretic image of the disjoint union of
the closed subschemes `Spec (Aᵢ/Jᵢ)` of the charts of a finite affine covering, and the ideal of
a scheme-theoretic image is the kernel of `𝒪_𝔛 → f_* 𝒪`. Here that ideal is written down
directly, as the intersection of the kernel ideal sheaves of the morphisms
`Spec (Aᵢ/Jᵢ) → 𝔛`, so neither the induction nor the gluing has to be carried out: the
compatibility `Z_U ∩ 𝔙 = 𝔘 ∩ Z_V` that the gluing needs is built into the fact that a kernel
ideal sheaf is a sheaf (`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.ker`).

**Where the hypotheses are used.** Quasi-compactness of `𝔛` gives the finite affine covering.
Quasi-separatedness is used, as in the source, to make the overlaps `𝔚 ∩ 𝔘ᵢ` of a quasi-compact
open `𝔚` with the charts quasi-compact: over a quasi-compact open the sections of the
pseudo-discrete structure sheaf of `Spec (Aᵢ/Jᵢ)` are discrete, so the kernel there is open. A
formal scheme à la EGA is quasi-separated exactly when its underlying space is (its reduction is
a scheme with the same underlying space), which is the hypothesis `QuasiSeparatedSpace`.

**Why the kernels are ideals of definition.** Over an open `𝔚` of a chart `Spf A`, the sections
of `𝒪_{Spf A} = lim 𝒪_λ` carry the limit topology, so a neighbourhood of zero contains the kernel
of one projection `𝒪_{Spf A}(𝔚) → 𝒪_λ(𝔚)`. The kernel of the projection onto `𝒪_J` has a power
inside it: with `μ = J ∩ I_λ` the kernel of `A/μ → A/J` is `J/μ`, whose `m`-th power vanishes as
soon as `J^m ⊆ I_λ ∩ J`, and then so does the `m`-th power of the kernel of
`𝒪_μ(𝔚) → 𝒪_J(𝔚)`, by a computation on the basic opens of `Spec (A/μ)`, where the map is a
localization of `A/μ → A/J` (`AlgebraicGeometry.Scheme.Hom.ker_app_pow_eq_bot`).

## References

* [Stacks Project, Tag 0AJF](https://stacks.math.columbia.edu/tag/0AJF)
* [Stacks Project, Tag 0AJE](https://stacks.math.columbia.edu/tag/0AJE)
* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
* [Stacks Project, Tag 01P0](https://stacks.math.columbia.edu/tag/01P0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

/-! ### Nilpotent kernels -/

/-- The kernel of `A/I → A/J`, for `I ⊆ J`, has vanishing `m`-th power as soon as `J^m ⊆ I`: it
is the image of `J` in `A/I`. -/
theorem Ideal.Quotient.ker_factor_pow_eq_bot {A : Type u} [CommRing A] {I J : Ideal A}
    (h : I ≤ J) {m : ℕ} (hm : J ^ m ≤ I) : (RingHom.ker (Ideal.Quotient.factor h)) ^ m = ⊥ := by
  have hle : RingHom.ker (Ideal.Quotient.factor h) ≤ J.map (Ideal.Quotient.mk I) := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine eq_bot_iff.mpr ((Ideal.pow_right_mono hle m).trans ?_)
  rw [← Ideal.map_pow]
  exact (Ideal.map_mono hm).trans (Ideal.map_quotient_self I).le

namespace AlgebraicGeometry

/-- The map `Spec.map φ` induces on global sections is `φ` read through `Γ(Spec R) = R`, so its
kernel has vanishing `m`-th power as soon as the kernel of `φ` has. -/
theorem ker_appTop_Spec_map_pow_eq_bot {R S : CommRingCat.{u}} (φ : R ⟶ S) {m : ℕ}
    (hm : (RingHom.ker φ.hom) ^ m = ⊥) :
    (RingHom.ker (Spec.map φ).appTop.hom) ^ m = ⊥ := by
  have hinj : ∀ T : CommRingCat.{u}, Function.Injective (Scheme.ΓSpecIso T).hom.hom := fun T =>
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso T).hom).1
  have hker : RingHom.ker (Spec.map φ).appTop.hom =
      Ideal.comap (Scheme.ΓSpecIso R).hom.hom (RingHom.ker φ.hom) := by
    ext y
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker,
      ← CategoryTheory.ConcreteCategory.comp_apply, ← Scheme.ΓSpecIso_naturality,
      CategoryTheory.ConcreteCategory.comp_apply]
    exact (map_eq_zero_iff _ (hinj S)).symm
  rw [hker]
  refine eq_bot_iff.mpr ((Ideal.le_comap_pow _ m).trans ?_)
  rw [hm]
  intro y hy
  rw [Ideal.mem_comap, Ideal.mem_bot] at hy
  exact (map_eq_zero_iff _ (hinj R)).mp hy

/-- **Nilpotent kernels spread to all opens.** Let `f : X ⟶ Y` be a morphism of affine schemes
whose map on global sections has a kernel with vanishing `m`-th power. Then over every open `V`
of `Y` the kernel of `Γ(Y, V) → Γ(X, f⁻¹ V)` has vanishing `m`-th power.

Over a basic open `D(r) ⊆ V` the map is the localization at `r` of the map on global sections,
whose kernel is the extension of the kernel on global sections; so an element of the `m`-th power
of the kernel over `V` restricts to zero on every basic open inside `V`, hence is zero. -/
theorem Scheme.Hom.ker_app_pow_eq_bot {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    {m : ℕ} (hm : (RingHom.ker f.appTop.hom) ^ m = ⊥) (V : Y.Opens) :
    (RingHom.ker (f.app V).hom) ^ m = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [Ideal.mem_bot]
  have hlocal : ∀ p : V, ∃ (B : Y.Opens) (hBV : B ≤ V), (p : Y) ∈ B ∧
      Y.presheaf.map (homOfLE hBV).op x = 0 := by
    intro p
    obtain ⟨_, ⟨r, rfl⟩, hpB, hBV⟩ :=
      (Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Y)) p.2
    refine ⟨Y.basicOpen r, hBV, hpB, ?_⟩
    let := (isAffineOpen_top Y).isLocalization_basicOpen r
    let := (isAffineOpen_top X).isLocalization_basicOpen (f.appLE ⊤ ⊤ le_top r)
    have hloc := (isAffineOpen_top Y).appLE_eq_away_map f (isAffineOpen_top X) le_top r
    have htop : f.appLE ⊤ ⊤ le_top = f.appTop := f.app_eq_appLE.symm
    have hle : Ideal.map (Y.presheaf.map (homOfLE hBV).op).hom (RingHom.ker (f.app V).hom) ≤
        Ideal.map (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r))
          (RingHom.ker (f.appLE ⊤ ⊤ le_top).hom) := by
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      rw [Ideal.mem_comap]
      have hz : (f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE ⊤ ⊤ le_top r))
          (by rw [htop, Scheme.preimage_basicOpen_top]))
            (Y.presheaf.map (homOfLE hBV).op s) = 0 := by
        rw [← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
          Scheme.Hom.appLE, CategoryTheory.ConcreteCategory.comp_apply,
          RingHom.mem_ker.mp hs, map_zero]
      rw [hloc] at hz
      rwa [← IsLocalization.ker_map (M := Submonoid.powers r)
        (S := Γ(Y, Y.basicOpen r)) (Q := Γ(X, X.basicOpen (f.appLE ⊤ ⊤ le_top r)))
        (g := (f.appLE ⊤ ⊤ le_top).hom) (T := Submonoid.powers (f.appLE ⊤ ⊤ le_top r))
        (Submonoid.map_powers _ _)]
    have hpow : Y.presheaf.map (homOfLE hBV).op x ∈
        Ideal.map (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r))
          (RingHom.ker (f.appLE ⊤ ⊤ le_top).hom) ^ m := by
      refine Ideal.pow_right_mono hle m ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    rwa [← Ideal.map_pow, htop, hm, Ideal.map_bot, Ideal.mem_bot] at hpow
  choose B hBV hpB hzero using hlocal
  refine Y.sheaf.eq_of_locally_eq' B V (fun p => homOfLE (hBV p))
    (fun p hp => Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpB ⟨p, hp⟩⟩) x 0 fun p => ?_
  rw [map_zero]
  exact hzero p

end AlgebraicGeometry

/-! ### Neighbourhoods of zero in a directed limit of topological rings -/

namespace TopCommRingCat

/-- In the vertex of a limit cone of topological rings over a nonempty codirected preorder, every
neighbourhood of zero contains the kernel of one of the projections: the vertex carries the
topology induced by the projections, and the preimages of the neighbourhoods of zero of the
components form a directed family because the transition maps are continuous. -/
theorem exists_forall_π_app_eq_zero_mem_of_isLimit {J : Type u} [Preorder J] [Nonempty J]
    (hdir : ∀ a b : J, ∃ c, c ≤ a ∧ c ≤ b) {F : J ⥤ TopCommRingCat.{u}} {c : Cone F}
    (hc : IsLimit c) {N : Set c.pt.α} (hN : N ∈ nhds (0 : c.pt.α)) :
    ∃ j, ∀ x : c.pt.α, (c.π.app j).1 x = 0 → x ∈ N := by
  have ht : (inferInstance : TopologicalSpace c.pt.α) =
      ⨅ j, TopologicalSpace.induced ((c.π.app j).1 : c.pt.α → (F.obj j).α) inferInstance :=
    TopCat.induced_of_isLimit ((forget₂ TopCommRingCat TopCat).mapCone c)
      (isLimitOfPreserves (forget₂ TopCommRingCat TopCat) hc)
  have hnhds : nhds (0 : c.pt.α) =
      ⨅ j, Filter.comap ((c.π.app j).1 : c.pt.α → (F.obj j).α) (nhds 0) := by
    rw [congrArg (fun t : TopologicalSpace c.pt.α => @nhds _ t (0 : c.pt.α)) ht, nhds_iInf]
    exact iInf_congr fun j => by rw [nhds_induced, map_zero]
  have hdirected : Directed (fun F G : Filter c.pt.α => F ≥ G)
      fun j : J => Filter.comap ((c.π.app j).1 : c.pt.α → (F.obj j).α) (nhds 0) := by
    intro a b
    obtain ⟨d, hda, hdb⟩ := hdir a b
    have hmono : ∀ {a : J} (h : d ≤ a),
        Filter.comap ((c.π.app d).1 : c.pt.α → (F.obj d).α) (nhds 0) ≤
          Filter.comap ((c.π.app a).1 : c.pt.α → (F.obj a).α) (nhds 0) := by
      intro a h
      have hw : ((c.π.app a).1 : c.pt.α → (F.obj a).α) =
          (F.map (homOfLE h)).1 ∘ (c.π.app d).1 := by
        funext x
        exact (congrArg (fun g : c.pt ⟶ F.obj a => g.1 x) (c.w (homOfLE h))).symm
      rw [hw, ← Filter.comap_comap]
      exact Filter.comap_mono (Filter.tendsto_iff_comap.mp
        ((F.map (homOfLE h)).2.tendsto' 0 0 (map_zero _)))
    exact ⟨d, hmono hda, hmono hdb⟩
  rw [hnhds, Filter.mem_iInf_of_directed hdirected] at hN
  obtain ⟨j, hj⟩ := hN
  obtain ⟨t, ht0, htN⟩ := Filter.mem_comap.mp hj
  exact ⟨j, fun x hx => htN (show (c.π.app j).1 x ∈ t from hx ▸ mem_of_mem_nhds ht0)⟩

end TopCommRingCat

namespace AlgebraicGeometry

/-! ### The kernels of the projections of a formal spectrum -/

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Over any open of the formal spectrum of a pre-admissible ring, every neighbourhood of zero in
the sections of `𝒪_{Spf A} = lim 𝒪_λ` contains the kernel of one projection onto a term `𝒪_J`. -/
theorem exists_forall_spfProjection_app_eq_zero_mem (hA : TopologicalRing.IsPreAdmissible A)
    (V : Opens (spfSpace A)) {N : Set ((spfPresheaf A).obj (op V)).α}
    (hN : N ∈ nhds (0 : ((spfPresheaf A).obj (op V)).α)) :
    ∃ J : IdealsOfDefinition A,
      ∀ s, ((spfProjection A J).app (op V)).1 s = 0 → s ∈ N := by
  have : Nonempty (IdealsOfDefinition A) := ⟨preAdmissibleSpfIndex A hA⟩
  exact TopCommRingCat.exists_forall_π_app_eq_zero_mem_of_isLimit
    (fun I J => ⟨spfIndexMeet A I J, show (I.1 ⊓ J.1) ≤ I.1 from inf_le_left,
      show (I.1 ⊓ J.1) ≤ J.1 from inf_le_right⟩) (spfObjIsLimit A V) hN

/-- **A power of the kernel of one projection lies in the kernel of another.** Over any open `V`
of `Spf A` and for ideals of definition `J` and `L` of `A`, some power of the kernel of the
projection `𝒪_{Spf A}(V) → 𝒪_J(V)` lies in the kernel of the projection onto `𝒪_L(V)`.

With `μ = J ∩ L` and `J^m ⊆ μ`, the projection onto `𝒪_J` factors through `𝒪_μ`, and the kernel
of the transition map `𝒪_μ(V) → 𝒪_J(V)` has vanishing `m`-th power, the kernel of `A/μ → A/J`
having it (`AlgebraicGeometry.Scheme.Hom.ker_app_pow_eq_bot`). -/
theorem exists_ker_spfProjection_pow_le (V : Opens (spfSpace A)) (J L : IdealsOfDefinition A) :
    ∃ m : ℕ, (RingHom.ker ((spfProjection A J).app (op V)).1) ^ m ≤
      RingHom.ker ((spfProjection A L).app (op V)).1 := by
  obtain ⟨n, hn⟩ := J.2.2 (L.1 : Set A) (L.2.1.mem_nhds L.1.zero_mem)
  let μ : IdealsOfDefinition A := spfIndexMeet A J L
  have hμJ : μ.1 ≤ J.1 := inf_le_left
  have hμL : μ.1 ≤ L.1 := inf_le_right
  have hpow : J.1 ^ (n + 1) ≤ μ.1 :=
    le_inf (Ideal.pow_le_self (Nat.succ_ne_zero n))
      ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn)
  have hnil : (RingHom.ker ((spfTransition A hμJ).app (op V)).hom) ^ (n + 1) = ⊥ :=
    Scheme.Hom.ker_app_pow_eq_bot _
      (ker_appTop_Spec_map_pow_eq_bot _ (Ideal.Quotient.ker_factor_pow_eq_bot hμJ hpow)) _
  let ψ : ((spfPresheaf A).obj (op V)).α →+* ((spfComponent A μ).obj (op V)) :=
    ((spfProjection A μ).app (op V)).1
  have hker : RingHom.ker ((spfProjection A J).app (op V)).1 =
      Ideal.comap ψ (RingHom.ker ((spfTransition A hμJ).app (op V)).hom) := by
    ext s
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    exact (spfProjection_app_spfTransition_app A hμJ (op V) s).symm ▸ Iff.rfl
  refine ⟨n + 1, fun x hx => ?_⟩
  rw [hker] at hx
  have hzero : ψ x = 0 := by
    have hmem := Ideal.le_comap_pow ψ (n + 1) hx
    rwa [hnil, Ideal.mem_comap, Ideal.mem_bot] at hmem
  rw [RingHom.mem_ker, ← spfProjection_app_spfTransition_app A hμL (op V) x]
  change ((spfTransition A hμL).app (op V)).hom (ψ x) = 0
  rw [hzero, map_zero]

end Spf

/-! ### The closed subschemes of an affine formal chart -/

section Chart

open LocallyTopologicallyRingedSpace

variable {X : LTRS.{u}} {U : Opens X} {A : TopCommRingCat.{u}}
  (hA : TopologicalRing.IsPreAdmissible A.α)
  (e : X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A.α)

/-- The open immersion `Spf A ≅ X|_U ⟶ X` of an affine formal chart of `X`, as a morphism of
locally topologically ringed spaces: an isomorphism of presheafed spaces is local on stalks. -/
noncomputable def spfChartHom : spfLTRS A.α hA ⟶ X :=
  (show spfLTRS A.α hA ⟶ X.restrict U from
    { toHom := e.inv
      isLocalHom := fun x =>
        @TopCommRingCat.isLocalHom_val_of_isIso _ _ _ (PresheafedSpace.stalkMap.isIso e.inv x) }) ≫
    X.ofRestrict U

/-- The underlying morphism of presheafed spaces of `AlgebraicGeometry.spfChartHom`. -/
theorem spfChartHom_toHom :
    (spfChartHom hA e).toHom = e.inv ≫ X.toPresheafedSpace.ofRestrict U.isOpenEmbedding :=
  rfl

/-- The closed subscheme `Spec (A/J) ⟶ Spf A ⟶ X` of an affine formal chart attached to an ideal
of definition `J` of `A`. -/
noncomputable def spfChartPoint (J : IdealsOfDefinition A.α) :
    schemeToLTRSObj (Spec (spfQuotient A.α J)) ⟶ X :=
  spfQuotientPoint A.α hA J ≫ spfChartHom hA e

/-- A section of `𝒪_X` over `W` lies in the kernel ideal sheaf of `Spec (A/J) ⟶ X` exactly when
its image in the sections of `𝒪_{Spf A}` over the preimage of `W` projects to zero in `𝒪_J`. -/
theorem ker_spfChartPoint_ideal_eq (J : IdealsOfDefinition A.α) (W : Opens X) :
    (IdealSheaf.ker (spfChartPoint hA e J)).ideal W =
      Ideal.comap ((spfChartHom hA e).toHom.c.app (op W)).1
        (RingHom.ker ((spfProjection A.α J).app
          (op ((Opens.map (spfChartHom hA e).toHom.base).obj W))).1) :=
  Ideal.ext fun _ => Iff.rfl

/-- Over an open inside the chart, the chart identifies the sections of `𝒪_X` with those of
`𝒪_{Spf A}`. -/
theorem isIso_spfChartHom_c_app {W : Opens X} (hW : W ≤ U) :
    IsIso ((spfChartHom hA e).toHom.c.app (op W)) := by
  rw [spfChartHom_toHom, PresheafedSpace.comp_c_app]
  have heq : U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj W) = W := by
    rw [show U.isOpenEmbedding.isOpenMap.functor = U.isOpenEmbedding.functor from rfl,
      Opens.functor_map_eq_inf, inf_eq_left.mpr hW]
  have hiso : IsIso (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W) :=
    ⟨⟨homOfLE heq.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have h1 : IsIso ((X.toPresheafedSpace.ofRestrict U.isOpenEmbedding).c.app (op W)) :=
    inferInstanceAs (IsIso (X.presheaf.map
      (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op))
  have : IsIso e.inv.c := PresheafedSpace.c_isIso_of_iso e.inv
  have h2 : IsIso (e.inv.c.app (op ((Opens.map
      (X.toPresheafedSpace.ofRestrict U.isOpenEmbedding).base).obj W))) :=
    NatIso.isIso_app_of_isIso e.inv.c _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

include hA e in
/-- The open of an affine formal chart is quasi-compact, being homeomorphic to the formal
spectrum of a pre-admissible ring. -/
theorem isCompact_of_spfChart : IsCompact (U : Set X) := by
  have hc : IsCompact (Set.univ : Set (spfSpace A.α)) :=
    @isCompact_univ _ _ (compactSpace_spfSpace A.α hA)
  have h := (hc.image e.inv.base.hom.continuous).image U.inclusion'.hom.continuous
  have hsurj : Function.Surjective e.inv.base.hom :=
    (TopCat.homeoOfIso ((PresheafedSpace.forget _).mapIso e).symm).surjective
  refine (show (U : Set X) = U.inclusion'.hom '' (e.inv.base.hom '' Set.univ) from ?_) ▸ h
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    exact ⟨_, ⟨y, trivial, hy⟩, rfl⟩
  · rintro ⟨_, _, rfl⟩
    exact Subtype.property _

/-- Some power of the kernel ideal of `Spec (A/J) ⟶ X` over an open lies in the kernel ideal of
`Spec (A/L) ⟶ X` there. -/
theorem exists_ker_spfChartPoint_pow_le (J L : IdealsOfDefinition A.α) (W : Opens X) :
    ∃ m : ℕ, ((IdealSheaf.ker (spfChartPoint hA e J)).ideal W) ^ m ≤
      (IdealSheaf.ker (spfChartPoint hA e L)).ideal W := by
  obtain ⟨m, hm⟩ := exists_ker_spfProjection_pow_le A.α
    ((Opens.map (spfChartHom hA e).toHom.base).obj W) J L
  refine ⟨m, ?_⟩
  rw [ker_spfChartPoint_ideal_eq, ker_spfChartPoint_ideal_eq]
  exact (Ideal.le_comap_pow _ m).trans (Ideal.comap_mono hm)

/-- Over an open inside the chart, every neighbourhood of zero in the sections of `𝒪_X` contains
the kernel ideal of `Spec (A/J) ⟶ X` for some ideal of definition `J`. -/
theorem exists_ker_spfChartPoint_subset {W : Opens X} (hW : W ≤ U)
    {N : Set (X.presheaf.obj (op W)).α} (hN : N ∈ nhds (0 : (X.presheaf.obj (op W)).α)) :
    ∃ J : IdealsOfDefinition A.α,
      ∀ s ∈ (IdealSheaf.ker (spfChartPoint hA e J)).ideal W, s ∈ N := by
  have := isIso_spfChartHom_c_app hA e hW
  set φ := (spfChartHom hA e).toHom.c.app (op W) with hφ
  have hinv : ∀ s, (inv φ).1 (φ.1 s) = s := fun s =>
    congrArg (fun g : X.presheaf.obj (op W) ⟶ X.presheaf.obj (op W) => g.1 s)
      (IsIso.hom_inv_id φ)
  have hN' := (inv φ).2.tendsto' 0 0 (map_zero _) hN
  obtain ⟨J, hJ⟩ := exists_forall_spfProjection_app_eq_zero_mem A.α hA _ hN'
  exact ⟨J, fun s hs => hinv s ▸ hJ (φ.1 s) hs⟩

/-- Over an open meeting the chart in a quasi-compact set, the kernel ideal of `Spec (A/J) ⟶ X`
is open: the preimage of the open in `Spec (A/J)` is quasi-compact, so the sections of the
pseudo-discrete structure sheaf there are discrete. -/
theorem isOpen_ker_spfChartPoint (J : IdealsOfDefinition A.α) {W : Opens X}
    (hW : IsCompact ((W : Set X) ∩ U)) :
    IsOpen ((IdealSheaf.ker (spfChartPoint hA e J)).ideal W :
      Set (X.presheaf.obj (op W)).α) := by
  let f := spfChartPoint hA e J
  have hU : IsCompact (U.inclusion' ⁻¹' (W : Set X)) := by
    have h := U.isOpenEmbedding.isInducing.isCompact_preimage' hW (by
      rw [Opens.set_range_inclusion']
      exact Set.inter_subset_right)
    rwa [Set.preimage_inter, show U.inclusion' ⁻¹' (U : Set X) = Set.univ from
      Set.eq_univ_of_forall fun x => x.2, Set.inter_univ] at h
  have hV : IsCompact ((Opens.map (spfChartHom hA e).toHom.base).obj W).1 :=
    (TopCat.homeoOfIso ((PresheafedSpace.forget _).mapIso e).symm).isCompact_preimage.mpr hU
  have hcompact : IsCompact ((((Opens.map f.toHom.base).obj W :
      Opens ↥(schemeToLTRSObj (Spec (spfQuotient A.α J))))) :
        Set ↥(schemeToLTRSObj (Spec (spfQuotient A.α J)))) :=
    isCompact_preimage_spfOfQuotient A.α J _ hV
  let _ : DiscreteTopology ((schemeToLTRSObj (Spec (spfQuotient A.α J))).presheaf.obj
      (op ((Opens.map f.toHom.base).obj W))).α :=
    ⟨pseudoDiscreteTopology_eq_bot (Spec (spfQuotient A.α J)).presheaf hcompact⟩
  have hpre : ((IdealSheaf.ker f).ideal W : Set (X.presheaf.obj (op W)).α) =
      (f.toHom.c.app (op W)).1 ⁻¹' {0} :=
    Set.ext fun _ => IdealSheaf.mem_ker_iff
  have hzero : IsOpen ({0} : Set ((schemeToLTRSObj (Spec (spfQuotient A.α J))).presheaf.obj
      (op ((Opens.map f.toHom.base).obj W))).α) := isOpen_discrete _
  rw [hpre]
  exact hzero.preimage (f.toHom.c.app (op W)).2

/-- **The closed subschemes of a chart cut out ideals of definition.** Over a quasi-compact open
inside an affine formal chart `Spf A`, the kernel ideal of `Spec (A/J) ⟶ X` is an ideal of
definition of the ring of sections, for every ideal of definition `J` of `A`. -/
theorem isIdealOfDefinition_ker_spfChartPoint (J : IdealsOfDefinition A.α) {W : Opens X}
    (hWU : W ≤ U) (hW : IsCompact (W : Set X)) :
    TopologicalRing.IsIdealOfDefinition ((IdealSheaf.ker (spfChartPoint hA e J)).ideal W) := by
  refine ⟨isOpen_ker_spfChartPoint hA e J
    (by rwa [Set.inter_eq_left.mpr (show (W : Set X) ⊆ U from hWU)]), fun N hN => ?_⟩
  obtain ⟨L, hL⟩ := exists_ker_spfChartPoint_subset hA e hWU hN
  obtain ⟨m, hm⟩ := exists_ker_spfChartPoint_pow_le hA e J L W
  exact ⟨m, fun s hs => hL s (hm hs)⟩

/-- A smaller ideal of definition cuts out a larger closed subscheme of the chart, hence a smaller
kernel ideal. -/
theorem ker_spfChartPoint_le {J L : IdealsOfDefinition A.α} (h : J.1 ≤ L.1) (W : Opens X) :
    (IdealSheaf.ker (spfChartPoint hA e J)).ideal W ≤
      (IdealSheaf.ker (spfChartPoint hA e L)).ideal W := by
  have hcomp : spfQuotientTransition A.α h ≫ spfChartPoint hA e J = spfChartPoint hA e L := by
    rw [spfChartPoint, ← Category.assoc, spfQuotientTransition_comp_spfQuotientPoint]
    rfl
  rw [← hcomp]
  exact IdealSheaf.ker_le_ker_comp _ _ W

end Chart

/-! ### Intersections of ideal sheaves -/

namespace LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}}

/-- The intersection of a family of ideal sheaves, taken sectionwise: an intersection of ideals
stable under restriction and local is again stable under restriction and local. -/
instance instInfSet : InfSet (IdealSheaf X) where
  sInf 𝒮 :=
    { ideal V := ⨅ I ∈ 𝒮, I.ideal V
      map_mem := fun h _ hs => (Submodule.mem_iInf _).mpr fun I => (Submodule.mem_iInf _).mpr
        fun hI => I.map_mem h ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs I) hI)
      mem_of_locally_mem := fun hlocal => (Submodule.mem_iInf _).mpr fun I =>
        (Submodule.mem_iInf _).mpr fun hI => I.mem_of_locally_mem fun x hx => by
          obtain ⟨V, h, hxV, hs⟩ := hlocal x hx
          exact ⟨V, h, hxV, (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs I) hI⟩ }

/-- The sections of an intersection of ideal sheaves are the intersection of the sections. -/
theorem sInf_ideal (𝒮 : Set (IdealSheaf X)) (V : Opens X) :
    (sInf 𝒮).ideal V = ⨅ I ∈ 𝒮, I.ideal V :=
  rfl

/-- The sections of an indexed intersection of ideal sheaves are the intersection of the
sections. -/
theorem iInf_ideal {ι : Sort*} (I : ι → IdealSheaf X) (V : Opens X) :
    (⨅ i, I i).ideal V = ⨅ i, (I i).ideal V := by
  rw [iInf, sInf_ideal, iInf_range]

end LocallyTopologicallyRingedSpace.IdealSheaf

/-! ### The fundamental system -/

open LocallyTopologicallyRingedSpace in
/-- **A quasi-compact quasi-separated formal scheme has a fundamental system of ideals of
definition over its quasi-compact opens.** Cover `X` by finitely many affine formal charts
`Spf Aᵢ`; the ideal sheaves `⋂ᵢ ker(Spec (Aᵢ/Jᵢ) ⟶ X)`, for all choices of ideals of definition
`Jᵢ` of the `Aᵢ`, form a nonempty, sectionwise directed family which over every quasi-compact open
consists of ideals of definition whose ideals of sections are a neighbourhood basis of zero. -/
theorem exists_isFundamentalSystemOfIdealsOfDefinitionOn_isCompact_of_isFormalScheme
    {X : LTRS.{u}} [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (hX : IsFormalScheme X) :
    ∃ 𝒮 : Set (IdealSheaf X), 𝒮.Nonempty ∧
      (∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
        K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W) ∧
      IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 fun W => IsCompact (W : Set X) := by
  classical
  have hchart : ∀ x : X, ∃ (U : Opens X) (A : TopCommRingCat.{u}), x ∈ U ∧
      TopologicalRing.IsPreAdmissible A.α ∧
        Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅
          Spf A.α) := by
    intro x
    obtain ⟨U, hxU, A, _, hA, he⟩ := hX x
    exact ⟨U, A, hxU, hA.1, he⟩
  choose U A hxU hA he using hchart
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩
  have hcover : ∀ x : X, ∃ i : s, x ∈ U i := fun x => by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, hxi⟩
  let e : ∀ x : X, X.toPresheafedSpace.restrict (f := (U x).inclusion') (U x).isOpenEmbedding' ≅
      Spf (A x).α := fun x => (he x).some
  let member : (∀ i : s, IdealsOfDefinition (A i).α) → IdealSheaf X := fun J =>
    ⨅ i : s, IdealSheaf.ker (spfChartPoint (hA i) (e i) (J i))
  have hle : ∀ J (i : s) (W : Opens X),
      (member J).ideal W ≤ (IdealSheaf.ker (spfChartPoint (hA i) (e i) (J i))).ideal W :=
    fun J i W => by
      rw [IdealSheaf.iInf_ideal]
      exact iInf_le (fun i : s => (IdealSheaf.ker (spfChartPoint (hA i) (e i) (J i))).ideal W) i
  have hne : (Set.range member).Nonempty :=
    ⟨_, fun i => preAdmissibleSpfIndex _ (hA i), rfl⟩
  have hdir : ∀ I ∈ Set.range member, ∀ J ∈ Set.range member, ∃ K ∈ Set.range member,
      ∀ W : Opens X, K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W := by
    rintro _ ⟨J, rfl⟩ _ ⟨J', rfl⟩
    refine ⟨member fun i => spfIndexMeet _ (J i) (J' i), ⟨_, rfl⟩, fun W => ⟨?_, ?_⟩⟩ <;>
      simp only [member, IdealSheaf.iInf_ideal] <;>
      exact iInf_mono fun i => ker_spfChartPoint_le (hA i) (e i) (by simp [spfIndexMeet]) W
  have hinter : ∀ (W : Opens X), IsCompact (W : Set X) → ∀ i : s,
      IsCompact ((W : Set X) ∩ U i) := fun W hW i =>
    hW.inter_of_isOpen (isCompact_of_spfChart (hA i) (e i)) W.isOpen (U i).isOpen
  have hopen : ∀ J (W : Opens X), IsCompact (W : Set X) →
      IsOpen ((member J).ideal W : Set (X.presheaf.obj (op W)).α) := by
    intro J W hW
    rw [IdealSheaf.iInf_ideal, Submodule.coe_iInf]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_ker_spfChartPoint (hA i) (e i) (J i) (hinter W hW i)
  refine ⟨Set.range member, hne, hdir, ⟨?_, fun W hW => ?_⟩⟩
  · rintro _ ⟨J, rfl⟩ W hW
    refine (member J).isIdealOfDefinition_of_isCompact W hW fun x hx => ?_
    obtain ⟨i, hxi⟩ := hcover x
    exact ⟨W ⊓ U i, inf_le_left, ⟨hx, hxi⟩,
      TopologicalRing.isIdealOfDefinition_of_le_of_isOpen
        (isIdealOfDefinition_ker_spfChartPoint (hA i) (e i) (J i) inf_le_right (hinter W hW i))
        (hopen J _ (hinter W hW i)) (hle J i _)⟩
  · refine IdealSheaf.hasBasis_ideal_of_isCompact hne hdir W hW
      (by rintro _ ⟨J, rfl⟩; exact hopen J W hW) fun x hx => ?_
    obtain ⟨i, hxi⟩ := hcover x
    refine ⟨W ⊓ U i, inf_le_left, ⟨hx, hxi⟩, ⟨fun N => ⟨fun hN => ?_, ?_⟩⟩⟩
    · obtain ⟨L, hL⟩ := exists_ker_spfChartPoint_subset (hA i) (e i)
        (inf_le_right : W ⊓ U i ≤ U i) hN
      let J : ∀ i : s, IdealsOfDefinition (A i).α :=
        Function.update (fun i => preAdmissibleSpfIndex _ (hA i)) i L
      refine ⟨member J, ⟨J, rfl⟩, fun t ht => hL t ?_⟩
      have := hle J i _ ht
      rwa [show J i = L from Function.update_self _ _ _] at this
    · rintro ⟨I, ⟨J, rfl⟩, hIN⟩
      exact Filter.mem_of_superset ((hopen J _ (hinter W hW i)).mem_nhds (Ideal.zero_mem _)) hIN

open LocallyTopologicallyRingedSpace in
/-- **Stacks 0AJF.** Every quasi-compact and quasi-separated formal scheme à la EGA has a
fundamental system of ideals of definition: a nonempty family of ideal sheaves, sectionwise
directed, each of which is an ideal of definition over every affine formal open subscheme, and
whose ideals of sections over every affine formal open subscheme form a neighbourhood basis of
zero.

The members are the intersections `⋂ᵢ ker(Spec (Aᵢ/Jᵢ) ⟶ X)` over a finite covering by affine
formal charts `Spf Aᵢ`, which is the ideal of the scheme-theoretic image that the source's
induction produces; see the implementation notes. Quasi-separatedness is that of the underlying
space, which for a formal scheme à la EGA is quasi-separatedness of the formal scheme. -/
@[stacks 0AJF]
theorem exists_isFundamentalSystemOfIdealsOfDefinitionOn_of_isFormalScheme
    {X : LTRS.{u}} [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] (hX : IsFormalScheme X) :
    ∃ 𝒮 : Set (IdealSheaf X), 𝒮.Nonempty ∧
      (∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
        K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W) ∧
      IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X) := by
  obtain ⟨𝒮, hne, hdir, hdef, hbasis⟩ :=
    exists_isFundamentalSystemOfIdealsOfDefinitionOn_isCompact_of_isFormalScheme hX
  have hcompact : ∀ W : Opens X, IsAffineFormalOpen X W → IsCompact (W : Set X) := by
    rintro W ⟨A, _, hA, ⟨e⟩⟩
    exact isCompact_of_spfChart hA.1 e
  exact ⟨𝒮, hne, hdir, fun I hI W hW => hdef I hI W (hcompact W hW),
    fun W hW => hbasis W (hcompact W hW)⟩

end AlgebraicGeometry

end
