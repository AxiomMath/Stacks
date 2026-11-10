module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.Assembly
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Pullback
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.PullbackUniverse
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical

/-!
# Relative ampleness near a fibre from an immersion of that fibre into projective space

Let `f : X ⟶ S` be proper with `S` locally Noetherian and let `ℒ` be an invertible
`𝒪_X`-module. This file proves [Stacks, Tag 0D2N] in the form where the morphism
`φ : X ⟶ ℙⁿ_S` is given by a family of global sections `s₀, …, sₙ` of `ℒ ^⊗ d` generating it
whose **restrictions to the fibre `X_y` define an immersion** `X_y ⟶ ℙⁿ_{κ(y)}`: then `ℒ` is
relatively ample over some open neighbourhood of `y`.

## Main results

* `exists_generatesStalks_eq_toProjectiveSpaceOver`: **a morphism `i : X ⟶ ℙʳ_S` over `S` with
  `M ≅ i^* 𝒪(1)` comes from a generating family of global sections of `M`** — the morphism
  [Stacks, Tag 01ND] attaches to that family is `i` itself.
* `exists_generatesStalks_isImmersion_toProjectiveSpaceOver_of_isAmple`: **[Stacks, Tag 01VS] in
  the sections form.** For `f` locally of finite type and `ℒ` ample, every large `d` admits a
  generating family of sections of `ℒ ^⊗ d` whose attached morphism to `ℙʳ_S` is an immersion.
* `exists_mem_generatesStalks_pullbackGlobalSections`: a family of global sections of an
  invertible module not all vanishing at any point of one fibre of a universally closed morphism
  generates over the preimage of a neighbourhood of that point.
* `toProjectiveSpaceOver_congr`: the [Stacks, Tag 01ND] morphism depends on the family only
  through an isomorphism of the module carrying the sections across.
* `subsingleton_preimage_of_fibreFactorization`: if the restriction of `φ : X ⟶ P` to the fibre
  of `f = φ ≫ p` over `y` factors as an **injective** map into a scheme mapping **injectively**
  into `P`, then every set-theoretic fibre of `φ` over a point of `P` lying above `y` has at most
  one point.
* `exists_mem_isRelativelyAmple_toProjectiveSpaceOver`: Tag 0D2N with the morphism to projective
  space given by generating sections. For `f : X ⟶ S` proper onto a locally Noetherian base, `ℒ`
  invertible, `d ≥ 1`, and sections `s : Fin (n+1) → Γ(ℒ ^⊗ d, ⊤)` generating the stalks, if the
  set-theoretic fibres of `Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs f` over the
  points of `ℙⁿ_S` above `y` are finite then `ℒ` is relatively ample over some open `V ∋ y`.
* `exists_mem_isRelativelyAmple_of_isImmersion_fibre`: **the same with the finiteness replaced by
  an immersion on the fibre.** If the morphism `X_y ⟶ ℙⁿ_{κ(y)}` built from the restrictions
  `(f.fiberι y)^* sᵢ` is an immersion, then `ℒ` is relatively ample over some open neighbourhood
  of `y`.

## Implementation notes

* The morphism attached to a generating family is [Stacks, Tag 01ND]
  (`Stacks.ProjectiveFromSections.toProjectiveSpaceOver`), it lies over the base by
  `toProjectiveSpaceOver_fst`, and the isomorphism `ℒ ^⊗ d ≅ φ^* 𝒪(1)` it pins is
  `AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver`. Those three
  turn `exists_mem_isRelativelyAmple_morphismRestrict` into the first statement above; the
  structure morphism `ℙⁿ_S ↘ S` **is** the first projection of the pullback defining `ℙⁿ_S`, by
  `rfl`, so no comparison is needed between `toProjectiveSpaceOver_fst` and the `↘` spelling.
* The construction is compatible with base change: by
  `Stacks.ProjectiveFromSections.comp_toProjectiveSpaceOver` the morphism built on `X_y` from
  the restricted sections, followed by `AlgebraicGeometry.projectiveSpaceOverMap n u` for
  `u = S.fromSpecResidueField y`, is `f.fiberι y ≫ φ`. The restricted family still generates by
  `AlgebraicGeometry.generatesStalks_pullbackGlobalSections'`, and the square it needs is
  `AlgebraicGeometry.Scheme.Hom.fiber_fac`.
* Both of the injectivity inputs are instances. `f.fiberι y` and
  `projectiveSpaceOverMap n (S.fromSpecResidueField y)` are preimmersions — the first by
  Mathlib's instance on `Scheme.Hom.fiberι`, the second because
  `AlgebraicGeometry.isPullback_projectiveSpaceOverMap` exhibits it as a base change of
  `S.fromSpecResidueField y`, which is a preimmersion, and `IsPreimmersion` is stable under base
  change — so both have embedding, hence injective, base maps. An **immersion** of the fibre is
  therefore more than enough: only its injectivity is used, and the source's closed immersion
  (which is what [Stacks, Tag 01VS] upgrades to over a field) is not needed.

The last point is why the finite-fibre hypothesis of the assembly is discharged by a
*subsingleton* statement: `φ⁻¹(z)` lies in `f⁻¹(y)`, which is the range of the injective
`f.fiberι y`, and two of its points have the same image under the injective composite
`ψ ≫ projectiveSpaceOverMap n u`.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleProjectiveImmersion
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.ProjectiveFromSections

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-! ### The generating family of a morphism to projective space over the base -/

/-- **A morphism to `ℙʳ_S` over `S`, together with an identification of an invertible module with
its pullback of `𝒪(1)`, comes from a generating family of global sections of that module.** More
precisely the morphism attached to the family by [Stacks, Tag 01ND] is the given morphism itself.

The sections are the pullbacks along `i` of the homogeneous coordinates `T₀, …, Tʳ` carried across
the identification. They generate because the coordinates do
(`Stacks.ProjectiveSpaceModuli.taut_generates`) and because generation is invariant under an
isomorphism (`Stacks.ProductFamilyTwist.generatesStalks_congr`); and the morphism they define is
`i` by the uniqueness half of [Stacks, Tag 01NE]
(`Stacks.ProjectiveSpaceModuli.eq_of_pin`, fed `pin_of_iso` on the tautological pinning
`taut_pin` and the chartwise description `ι_toProjectiveSpaceAtUniverse` of the attached
morphism), read on the integral model and then lifted back over `S` with
`Stacks.AmpleProjectiveImmersion.liftOver_eq`. -/
theorem exists_generatesStalks_eq_toProjectiveSpaceOver {X S : Scheme.{u}} (f : X ⟶ S) {r : ℕ}
    (M : X.Modules) [IsInvertibleModule X M] (i : X ⟶ projectiveSpaceOver r S)
    (hi : i ≫ (projectiveSpaceOver r S ↘ S) = f)
    (e : M ≅ pullbackModule i (projectiveSpaceTwistingSheaf r S)) :
    ∃ (t : Fin (r + 1) → Γ(M, ⊤)) (ht : GeneratesStalks t),
      toProjectiveSpaceOver t ht f = i := by
  have hlift : liftOver f (i ≫ projectiveSpaceOver.toIntegralAtUniverse r S) = i :=
    liftOver_eq f i hi
  let g : X ⟶ projectiveSpaceAtUniverse.{u} r := i ≫ projectiveSpaceOver.toIntegralAtUniverse r S
  let β : pullbackModule g (twistingSheafAtUniverse.{u} r) ≅ M :=
    (liftOverTwistIso f g).symm ≪≫
      Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hlift
        (projectiveSpaceTwistingSheaf r S) ≪≫ e.symm
  have ht : GeneratesStalks (fun j => Scheme.Modules.Hom.app β.hom ⊤
      (Stacks.TwistPullbackPinned.pullbackCoordSection g j)) :=
    Stacks.ProductFamilyTwist.generatesStalks_congr β
      (Stacks.ProjectiveSpaceModuli.taut_generates g)
  refine ⟨_, ht, ?_⟩
  have hgt : g = toProjectiveSpaceAtUniverse _ ht :=
    Stacks.ProjectiveSpaceModuli.eq_of_pin _ ht g _
      (fun j => Stacks.ProjectiveSpaceModuli.pin_of_iso _ _ β (fun _ => rfl) g
        (Stacks.ProjectiveSpaceModuli.taut_pin g) j)
      (fun j => ι_toProjectiveSpaceAtUniverse _ ht j)
  rw [toProjectiveSpaceOver, ← hgt]
  exact hlift

/-- **[Stacks, Tag 01VS] in the form of generating sections.** For `f : X ⟶ S` locally of finite
type and `ℒ` an ample invertible `𝒪_X`-module there is a `d₀ ≥ 1` such that every `d ≥ d₀` admits
a family of global sections of `ℒ ^⊗ d` generating its stalks whose [Stacks, Tag 01ND] morphism
`X ⟶ ℙʳ_S` is an **immersion**.

`Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple` — the homonym that
carries the `@[stacks 01VS]` attribute and takes no hypothesis beyond `f` locally of finite type
and `ℒ` ample — produces the immersion together with `ℒ ^⊗ d ≅ i^* 𝒪(1)`;
`Stacks.AmpleFibreNeighbourhood.exists_generatesStalks_eq_toProjectiveSpaceOver` turns that pair
into the sections and identifies the attached morphism with `i`, which transports the immersion. -/
theorem exists_generatesStalks_isImmersion_toProjectiveSpaceOver_of_isAmple {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (M : X.Modules) [IsInvertibleModule X M]
    (hM : IsAmple X M) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (r : ℕ) (t : Fin (r + 1) → Γ(tensorPowModule X M (d : ℤ), ⊤)) (ht : GeneratesStalks t),
        IsImmersion (toProjectiveSpaceOver t ht f) := by
  obtain ⟨d₀, hd₀, hall⟩ :=
    Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple f M hM
  refine ⟨d₀, hd₀, fun d hd => ?_⟩
  obtain ⟨r, i, himm, hover, ⟨e⟩⟩ := hall d hd
  obtain ⟨t, ht, heq⟩ :=
    exists_generatesStalks_eq_toProjectiveSpaceOver f (tensorPowModule X M (d : ℤ)) i hover e
  exact ⟨r, t, ht, heq ▸ himm⟩

/-- **The [Stacks, Tag 01ND] morphism depends only on the generating family up to an isomorphism
of the module carrying the sections across.** Both sides are `liftOver f` of a morphism to the
integral model, and those two morphisms are pinned by the same pair, so
`Stacks.ProjectiveSpaceModuli.eq_of_pin` identifies them — the chartwise pinning of the attached
morphism being `Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse` and its transport
along `β` being `Stacks.ProjectiveSpaceModuli.pin_of_iso`. -/
theorem toProjectiveSpaceOver_congr {X S : Scheme.{u}} (f : X ⟶ S) {r : ℕ}
    {M N : X.Modules} [IsInvertibleModule X M] [IsInvertibleModule X N] (β : M ≅ N)
    (t : Fin (r + 1) → Γ(M, ⊤)) (ht : GeneratesStalks t)
    (ht' : GeneratesStalks (fun j => Scheme.Modules.Hom.app β.hom ⊤ (t j))) :
    toProjectiveSpaceOver (fun j => Scheme.Modules.Hom.app β.hom ⊤ (t j)) ht' f =
      toProjectiveSpaceOver t ht f := by
  have h : toProjectiveSpaceAtUniverse (fun j => Scheme.Modules.Hom.app β.hom ⊤ (t j)) ht' =
      toProjectiveSpaceAtUniverse t ht :=
    Stacks.ProjectiveSpaceModuli.eq_of_pin _ ht' _ _
      (fun j => ι_toProjectiveSpaceAtUniverse _ ht' j)
      (fun j => Stacks.ProjectiveSpaceModuli.pin_of_iso t _ β (fun _ => rfl)
        (toProjectiveSpaceAtUniverse t ht)
        (fun j => ι_toProjectiveSpaceAtUniverse t ht j) j)
  rw [toProjectiveSpaceOver, toProjectiveSpaceOver, h]

/-! ### Shrinking the base so that the sections generate everywhere -/

/-- **A family of global sections of an invertible module that does not all vanish at any point
of one fibre of a universally closed morphism generates over the preimage of a neighbourhood of
that point.** This is the sentence "`X_y ⊆ U = ⋃ X_{sᵢ}`, and since `X ⟶ Y` is closed we can find
an open neighbourhood `V` of `y` with `f⁻¹(V) ⊆ U`" of the proof of [Stacks, Tag 0D2N].

The union of the nonvanishing loci is open and contains the fibre, so
`Stacks.AmpleFibreNeighbourhood.exists_mem_and_preimage_subset` produces `V`; over `f ⁻¹ᵁ V`
every point lies in some locus, its pullback still does not vanish there
(`Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections`), and for an
invertible module a family with that property generates
(`Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem`). -/
theorem exists_mem_generatesStalks_pullbackGlobalSections {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyClosed f] (M : X.Modules) [IsInvertibleModule X M] {ι : Type*}
    (s : ι → Γ(M, ⊤)) (y : S)
    (hfib : ∀ x : X, f.base x = y → ∃ i, x ∈ nvCover s i) :
    ∃ V : S.Opens, y ∈ V ∧
      GeneratesStalks
        (fun i => AlgebraicGeometry.pullbackGlobalSections (f ⁻¹ᵁ V).ι M (s i)) := by
  classical
  have hΩopen : IsOpen (⋃ i, (nvCover s i : Set X)) :=
    isOpen_iUnion fun i => (nvCover s i).isOpen
  have hsub : f.base ⁻¹' {y} ⊆ ⋃ i, (nvCover s i : Set X) := by
    intro x hx
    obtain ⟨i, hi⟩ := hfib x hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨V, hyV, hVsub⟩ := exists_mem_and_preimage_subset f y hΩopen hsub
  refine ⟨V, hyV,
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_⟩
  have hx : ((f ⁻¹ᵁ V).ι x : X) ∈ ⋃ i, (nvCover s i : Set X) := by
    refine hVsub ?_
    have hr : ((f ⁻¹ᵁ V).ι x : X) ∈ (((f ⁻¹ᵁ V).ι.opensRange : X.Opens) : Set X) := ⟨x, rfl⟩
    rwa [Scheme.Opens.opensRange_ι] at hr
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections
    (f ⁻¹ᵁ V).ι M (s i) hi⟩

/-! ### The finite-fibre hypothesis from injectivity on the fibre -/

/-- **A set-theoretic fibre of `φ` over a point above `y` has at most one point, as soon as the
restriction of `φ` to the fibre of `f = φ ≫ p` over `y` factors injectively through a scheme
mapping injectively into the target.**

Concretely: `ι : F ⟶ X` has range the set-theoretic fibre `f⁻¹(y)` and injective base map, and
`ι ≫ φ` factors as `ψ ≫ m` with both `ψ` and `m` injective on points. Any two points of
`φ⁻¹(z)` with `p(z) = y` lie in `f⁻¹(y)`, hence come from `F`, and their images under `ψ ≫ m`
are both `z`; injectivity of `m`, then of `ψ`, identifies their preimages in `F`. Injectivity of
`ι` is not used.

This is the form in which the "finite over the fibre" hypothesis of
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_morphismRestrict` is discharged in
the proof of [Stacks, Tag 0D2N]: there `F` is the scheme-theoretic fibre `X_y`, `ψ` the morphism
`X_y ⟶ ℙⁿ_{κ(y)}` and `m` the base-change morphism `ℙⁿ_{κ(y)} ⟶ ℙⁿ_S`. Only injectivity is used,
so an immersion of the fibre suffices and a closed immersion is not needed. -/
theorem subsingleton_preimage_of_fibreFactorization {X S P F Q : Scheme.{u}} {f : X ⟶ S}
    (φ : X ⟶ P) {p : P ⟶ S} (hφ : φ ≫ p = f) (y : S)
    (ι : F ⟶ X) (hι : Set.range ι.base = f.base ⁻¹' {y}) (_hιinj : Function.Injective ι.base)
    (ψ : F ⟶ Q) (m : Q ⟶ P) (hcomm : ψ ≫ m = ι ≫ φ)
    (hminj : Function.Injective m.base) (hψinj : Function.Injective ψ.base)
    {z : P} (hz : p.base z = y) : (φ ⁻¹' {z}).Subsingleton := by
  intro x₁ h₁ x₂ h₂
  have key : ∀ x : X, φ.base x = z → ∃ a : F, ι.base a = x ∧ m.base (ψ.base a) = z := by
    intro x hx
    have hfx : f.base x = y := by
      rw [← hφ]
      change p.base (φ.base x) = y
      rw [hx, hz]
    have hmem : x ∈ Set.range ι.base := by rw [hι]; exact hfx
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, ha, ?_⟩
    have hb : (ψ ≫ m).base a = (ι ≫ φ).base a := by rw [hcomm]
    change m.base (ψ.base a) = φ.base (ι.base a) at hb
    rw [hb, ha, hx]
  obtain ⟨a₁, ha₁, hm₁⟩ := key x₁ h₁
  obtain ⟨a₂, ha₂, hm₂⟩ := key x₂ h₂
  have : a₁ = a₂ := hψinj (hminj (hm₁.trans hm₂.symm))
  rw [← ha₁, ← ha₂, this]

/-! ### Stacks Tag 0D2N from the generating sections -/

/-- **[Stacks, Tag 0D2N] from a generating family of sections of `ℒ ^⊗ d` with finite fibres over
the fibre of the base point.** Let `f : X ⟶ S` be proper with `S` locally Noetherian, let `ℒ` be
an invertible `𝒪_X`-module, let `d ≥ 1` and let `s₀, …, sₙ` be global sections of `ℒ ^⊗ d`
generating its stalks. If every set-theoretic fibre of the associated morphism
`φ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs f` over a point of `ℙⁿ_S` lying
above `y` is finite, then `y` has an open neighbourhood `V` with `ℒ|_{f⁻¹V}` ample relative to
`f ∣_ V`.

`φ` lies over `S` by `Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst` — the structure
morphism of `ℙⁿ_S` is the first projection of the defining pullback by `rfl` — and
`ℒ ^⊗ d ≅ φ^* 𝒪(1)` is
`AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver`, whose pinning
`sᵢ = φ^* Tᵢ` is not used here. The rest is
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_morphismRestrict`. -/
theorem exists_mem_isRelativelyAmple_toProjectiveSpaceOver {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsLocallyNoetherian S] (L : X.Modules) [IsInvertibleModule X L]
    {n d : ℕ} (hd : 1 ≤ d)
    (s : Fin (n + 1) → Γ(tensorPowModule X L (d : ℤ), ⊤)) (hs : GeneratesStalks s) (y : S)
    (hfin : ∀ z : projectiveSpaceOver n S, (projectiveSpaceOver n S ↘ S).base z = y →
      (toProjectiveSpaceOver s hs f ⁻¹' {z}).Finite) :
    ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  obtain ⟨θ, -⟩ :=
    AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver s hs f
  exact exists_mem_isRelativelyAmple_morphismRestrict L hd (toProjectiveSpaceOver s hs f)
    (toProjectiveSpaceOver_fst s hs f) θ.symm y hfin

/-- **[Stacks, Tag 0D2N] from a generating family whose restriction to the fibre defines an
immersion.** Let `f : X ⟶ S` be proper with `S` locally Noetherian, let `ℒ` be an invertible
`𝒪_X`-module, let `d ≥ 1`, let `s₀, …, sₙ` be global sections of `ℒ ^⊗ d` generating its stalks,
and suppose the morphism

`X_y ⟶ ℙⁿ_{κ(y)}`

attached to the restricted family `(f.fiberι y)^* sᵢ` of sections of `(ℒ ^⊗ d)|_{X_y}` is an
immersion. Then `y` has an open neighbourhood `V` with `ℒ|_{f⁻¹V}` ample relative to `f ∣_ V`.

This is the last step of the proof of [Stacks, Tag 0D2N] before the sections themselves have to
be produced. The immersion gives injectivity on `X_y`;
`Stacks.ProjectiveFromSections.comp_toProjectiveSpaceOver` identifies the composite of it with
`AlgebraicGeometry.projectiveSpaceOverMap n (S.fromSpecResidueField y)` as
`f.fiberι y ≫ φ`; that base-change morphism is a preimmersion, hence injective, because
`AlgebraicGeometry.isPullback_projectiveSpaceOverMap` presents it as a base change of the
preimmersion `S.fromSpecResidueField y`; and
`Stacks.AmpleFibreNeighbourhood.subsingleton_preimage_of_fibreFactorization` then bounds every
fibre of `φ` above `y` by a point. -/
theorem exists_mem_isRelativelyAmple_of_isImmersion_fibre {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsLocallyNoetherian S] (L : X.Modules) [IsInvertibleModule X L]
    {n d : ℕ} (hd : 1 ≤ d)
    (s : Fin (n + 1) → Γ(tensorPowModule X L (d : ℤ), ⊤)) (hs : GeneratesStalks s) (y : S)
    (himm : IsImmersion (toProjectiveSpaceOver
      (fun i => AlgebraicGeometry.pullbackGlobalSections (f.fiberι y)
        (tensorPowModule X L (d : ℤ)) (s i))
      (AlgebraicGeometry.generatesStalks_pullbackGlobalSections' (f.fiberι y)
        (tensorPowModule X L (d : ℤ)) s hs)
      (f.fiberToSpecResidueField y))) :
    ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  set hs' := AlgebraicGeometry.generatesStalks_pullbackGlobalSections' (f.fiberι y)
    (tensorPowModule X L (d : ℤ)) s hs with hhs'
  set ψ := toProjectiveSpaceOver
    (fun i => AlgebraicGeometry.pullbackGlobalSections (f.fiberι y)
      (tensorPowModule X L (d : ℤ)) (s i)) hs' (f.fiberToSpecResidueField y) with hψ
  have : IsPreimmersion (projectiveSpaceOverMap n (S.fromSpecResidueField y)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_projectiveSpaceOverMap n (S.fromSpecResidueField y)).flip inferInstance
  refine exists_mem_isRelativelyAmple_toProjectiveSpaceOver f L hd s hs y
    fun z hz => Set.Subsingleton.finite ?_
  exact subsingleton_preimage_of_fibreFactorization (toProjectiveSpaceOver s hs f)
    (toProjectiveSpaceOver_fst s hs f) y
    (f.fiberι y) (f.range_fiberι y) (f.fiberι y).isEmbedding.injective ψ
    (projectiveSpaceOverMap n (S.fromSpecResidueField y))
    (comp_toProjectiveSpaceOver s hs f (f.fiber_fac y) hs')
    (projectiveSpaceOverMap n (S.fromSpecResidueField y)).isEmbedding.injective
    ψ.isEmbedding.injective hz

end Stacks.AmpleFibreNeighbourhood

end
