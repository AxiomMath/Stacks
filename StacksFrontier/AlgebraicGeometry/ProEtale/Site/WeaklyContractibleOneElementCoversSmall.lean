module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.ChangeOfPartialUniverse
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SmallWeaklyContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.WeaklyContractibleOneElementCovers
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Slice
public import StacksCore.Tactic.StacksAttribute

/-!
# One-element coverings by weakly contractible objects, over a base scheme

Every object of the big pro-étale site over a scheme, and every object of the small pro-étale
site of a scheme, admits a chosen covering family with a single member whose source is a weakly
contractible object of that site; the source may be taken affine when the underlying scheme of
the object is quasi-compact.

Both cases start from the one-element covering of the chosen big pro-étale site,
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_coproduct_singleton_covering`, applied to
the underlying object of the big site. What has to be supplied in each case is that its source
is weakly contractible *for the topology of the site at hand*, which tests a different category
of sheaves.

Over a base this is the slice construction: weak contractibility passes from an object of a site
to any arrow out of it, because sheaves on the slice are the sheaves over the sheafification of
the base object.

On the small site it is the disjoint union construction again, read inside the small site: the
source of the big covering is the disjoint union of affine objects with w-contractible rings of
global sections, each of which is a weakly contractible object of the small site by Stacks 0990,
and a disjoint union of weakly contractible objects is weakly contractible. The covering
morphism of the big site is weakly étale, which is what makes its source an object of the small
site at all.

## Main results

* `AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering_over` and
  `AlgebraicGeometry.ProEtale.exists_affine_weaklyContractible_singleton_covering_over` — the
  two statements of Stacks 0F4P for the big pro-étale site over a scheme.
* `AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering_small` and
  `AlgebraicGeometry.ProEtale.exists_affine_weaklyContractible_singleton_covering_small` — the
  two statements of Stacks 0F4P for the small pro-étale site of a scheme.
* `AlgebraicGeometry.ProEtale.isWeaklyContractible_small_of_coproduct` — an object of the small
  pro-étale site whose underlying scheme is a disjoint union of affine weakly contractible
  objects of the chosen big site is a weakly contractible object of the small site.

## Implementation notes

The chosen big pro-étale site and its slices are essentially small, not small, so the three
instances the slice construction consumes — sheafification for sheaves of types on the site and
on its slice, and the identification of the weak equivalences of presheaves of types with the
locally bijective morphisms — are supplied here as local instances from
`AlgebraicGeometry.essentiallySmall_schemeBelow` and
`AlgebraicGeometry.ProEtale.essentiallySmall_bigProetaleOver`.

The covering sieves and the empty covering sieve of the small site are produced from those of
the chosen big site by cocontinuity of
`AlgebraicGeometry.ProEtale.SmallProetale.toBigScheme`, the composite of the fully faithful
inclusion of the small site into the slice with the slice's forgetful functor: a sieve is
recovered from its pushforward along that composite, so cocontinuity turns a covering sieve of
the underlying object of the big site into a covering sieve of the small site.

## References

* [Stacks Project, Tag 0F4P](https://stacks.math.columbia.edu/tag/0F4P)
* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Essential smallness of the chosen big site and of its slices -/

/-- The underlying category of a chosen big pro-étale site is essentially small. -/
private theorem essentiallySmall_bigProetaleSite : EssentiallySmall.{u} B.Scheme :=
  AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff

attribute [local instance] essentiallySmall_bigProetaleSite essentiallySmall_bigProetaleOver

/-- Presheaves of types on a chosen big pro-étale site admit sheafification. -/
private theorem bigProetale_hasSheafify_type : HasSheafify B.topology (Type u) :=
  CategoryTheory.hasSheafifyEssentiallySmallSite B.topology (Type u)

/-- On a chosen big pro-étale site the weak equivalences of presheaves of types are the locally
bijective morphisms. -/
private theorem bigProetale_wEqualsLocallyBijective_type :
    B.topology.WEqualsLocallyBijective (Type u) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall B.topology

/-- Presheaves of types on the big pro-étale site over a scheme admit sheafification. -/
private theorem bigProetaleOver_hasSheafify_type :
    HasSheafify (BigProetaleOver.topology B S hS) (Type u) :=
  CategoryTheory.hasSheafifyEssentiallySmallSite _ (Type u)

attribute [local instance] bigProetale_hasSheafify_type
  bigProetale_wEqualsLocallyBijective_type bigProetaleOver_hasSheafify_type

/-! ### The big pro-étale site over a scheme -/

/-- **Stacks 0F4P for the big pro-étale site over a scheme.** Every object `U` of the big
pro-étale site over `S` in a chosen big pro-étale site admits a one-element covering `{V → U}`
whose source is a weakly contractible object of that site.

The covering is the one of
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering` for the underlying
object of the chosen big site, viewed over `S` through the composite to `U`; its source stays
weakly contractible in the slice by
`Stacks.WeaklyContractible.weaklyContractible_over`. -/
@[stacks 0F4P "the big site over a scheme"]
theorem exists_weaklyContractible_singleton_covering_over (U : BigProetaleOver B S hS) :
    ∃ (V : BigProetaleOver B S hS) (p : V ⟶ U),
      BigProetaleOver.IsCovering B S hS ⟨U, PreZeroHypercover.singleton p⟩ ∧
        (BigProetaleOver.topology B S hS).IsWeaklyContractible V := by
  obtain ⟨V₀, p₀, hcov, hwc⟩ := exists_weaklyContractible_singleton_covering B U.left
  refine ⟨Over.mk (p₀ ≫ U.hom), Over.homMk p₀, ?_, ?_⟩
  · exact hcov
  · exact Stacks.WeaklyContractible.weaklyContractible_over B.topology (p₀ ≫ U.hom) hwc

/-- **Stacks 0F4P for the big pro-étale site over a scheme, the quasi-compact case.** If the
underlying scheme of an object `U` of the big pro-étale site over `S` is quasi-compact, the
one-element covering of
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering_over` can be chosen
with affine source. -/
@[stacks 0F4P "the big site over a scheme, quasi-compact case"]
theorem exists_affine_weaklyContractible_singleton_covering_over
    (U : BigProetaleOver B S hS) [CompactSpace ((BigProetaleOver.toScheme B S hS).obj U)] :
    ∃ (V : BigProetaleOver B S hS) (p : V ⟶ U),
      BigProetaleOver.IsCovering B S hS ⟨U, PreZeroHypercover.singleton p⟩ ∧
        IsAffine ((BigProetaleOver.toScheme B S hS).obj V) ∧
        (BigProetaleOver.topology B S hS).IsWeaklyContractible V := by
  have _ : CompactSpace U.left.obj :=
    inferInstanceAs (CompactSpace ((BigProetaleOver.toScheme B S hS).obj U))
  obtain ⟨V₀, p₀, hcov, haff, hwc⟩ :=
    exists_affine_weaklyContractible_singleton_covering B U.left
  refine ⟨Over.mk (p₀ ≫ U.hom), Over.homMk p₀, ?_, haff, ?_⟩
  · exact hcov
  · exact Stacks.WeaklyContractible.weaklyContractible_over B.topology (p₀ ≫ U.hom) hwc

/-! ### Covering sieves of the small pro-étale site from the chosen big site -/

/-- The underlying object of the chosen big site of an object of the small pro-étale site: the
fully faithful inclusion of the small site into the slice over `S`, followed by the forgetful
functor of the slice. -/
abbrev SmallProetale.toBigScheme : SmallProetale B S hS ⥤ B.Scheme :=
  SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS

/-- Passing from the small pro-étale site to the chosen big site is cocontinuous: the inclusion
into the slice is cocontinuous by Stacks 098P, and so is the forgetful functor of the slice. -/
instance smallProetaleToBigScheme_isCocontinuous :
    (SmallProetale.toBigScheme B S hS).IsCocontinuous (SmallProetale.topology B S hS)
      B.topology := by
  have he : smallProetaleToBigProetaleFunctor B (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme)) = SmallProetale.inclusion B S hS := by
    dsimp [smallProetaleToBigProetaleFunctor]
    rw [Over.mapId_eq]
    rfl
  have _ : (SmallProetale.inclusion B S hS).IsCocontinuous (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) :=
    he ▸ smallProetaleToBigProetaleFunctor_isCocontinuous B (⟨S, hS⟩ : B.Scheme)
      (⟨S, hS⟩ : B.Scheme) (𝟙 (⟨S, hS⟩ : B.Scheme))
  exact isCocontinuous_comp (SmallProetale.inclusion B S hS) (BigProetaleOver.forget B S hS)
    (SmallProetale.topology B S hS) (BigProetaleOver.topology B S hS)

/-- A sieve of the small pro-étale site is recovered from its pushforward to the chosen big
site: the inclusion into the slice is fully faithful, and a sieve of a slice is recovered from
its pushforward along the forgetful functor. -/
theorem functorPullback_functorPushforward_toBigScheme {X : SmallProetale B S hS}
    (R : Sieve X) :
    (R.functorPushforward (SmallProetale.toBigScheme B S hS)).functorPullback
      (SmallProetale.toBigScheme B S hS) = R := by
  rw [Sieve.functorPushforward_comp, Sieve.functorPullback_comp,
    Sieve.functorPullback_functorPushforward_overForget,
    Sieve.functorPullback_functorPushforward_eq]

/-- An object of the small pro-étale site with empty underlying scheme is covered by the empty
sieve, which is the empty covering of the chosen big site lifted along cocontinuity. -/
theorem bot_mem_smallProetale_topology (X : SmallProetale B S hS)
    (h : IsEmpty ((SmallProetale.toScheme B S hS).obj X)) :
    (⊥ : Sieve X) ∈ SmallProetale.topology B S hS X := by
  have _ : IsEmpty (B.inclusion.obj ((SmallProetale.toBigScheme B S hS).obj X)) := h
  have hb : (⊥ : Sieve ((SmallProetale.toBigScheme B S hS).obj X)) ∈
      B.topology ((SmallProetale.toBigScheme B S hS).obj X) := by
    rw [← Sieve.generate_bot]
    apply Precoverage.generate_mem_toGrothendieck
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_bot]
    exact Scheme.bot_mem_propQCPrecoverage (P := @WeaklyEtale) _
  have hpull : (⊥ : Sieve ((SmallProetale.toBigScheme B S hS).obj X)).functorPullback
      (SmallProetale.toBigScheme B S hS) = (⊥ : Sieve X) := by
    ext Y q
    simp
  rw [← hpull]
  exact Functor.IsCocontinuous.cover_lift (G := SmallProetale.toBigScheme B S hS)
    (J := SmallProetale.topology B S hS) hb

/-- A family of morphisms of the small pro-étale site generates a covering sieve as soon as its
image in the chosen big site does. -/
theorem ofArrows_mem_smallProetale_topology {I : Type*} {X : SmallProetale B S hS}
    (V : I → SmallProetale B S hS) (f : ∀ i, V i ⟶ X)
    (h : Sieve.ofArrows (fun i ↦ (SmallProetale.toBigScheme B S hS).obj (V i))
        (fun i ↦ (SmallProetale.toBigScheme B S hS).map (f i)) ∈
      B.topology ((SmallProetale.toBigScheme B S hS).obj X)) :
    Sieve.ofArrows V f ∈ SmallProetale.topology B S hS X := by
  have h' : (Sieve.ofArrows V f).functorPushforward (SmallProetale.toBigScheme B S hS) ∈
      B.topology ((SmallProetale.toBigScheme B S hS).obj X) := by
    rwa [Sieve.functorPushforward_ofArrows]
  have hc := Functor.IsCocontinuous.cover_lift (G := SmallProetale.toBigScheme B S hS)
    (J := SmallProetale.topology B S hS) h'
  rwa [functorPullback_functorPushforward_toBigScheme] at hc

/-! ### The small pro-étale site -/

/-- The image in the schemes of a composite of two weakly étale morphisms of the chosen big site
is weakly étale. -/
private theorem weaklyEtale_inclusion_map_comp {X Y Z : B.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : WeaklyEtale (B.inclusion.map f)) (hg : WeaklyEtale (B.inclusion.map g)) :
    WeaklyEtale (B.inclusion.map (f ≫ g)) := by
  have _ := hf
  have _ := hg
  rw [B.inclusion.map_comp]
  infer_instance

/-- **A disjoint union of affine weakly contractible objects is a weakly contractible object of
the small pro-étale site.** If the underlying scheme of an object `X` of the small pro-étale
site of `S` is the disjoint union of a family of affine weakly contractible objects of the
chosen big site, then `X` is weakly contractible in the small site.

The summands are open subschemes of `X`, hence weakly étale over `S` and objects of the small
site; they are weakly contractible there because their rings of global sections are
w-contractible (Stacks 098H and Stacks 0990), and they form a disjoint covering family of `X`,
so `CategoryTheory.GrothendieckTopology.isWeaklyContractible_of_disjointCover` applies. -/
theorem isWeaklyContractible_small_of_coproduct (X : SmallProetale B S hS)
    {I : Type u} (Y : I → B.Scheme)
    (hY : ∀ i, IsAffine (Y i).obj ∧ B.topology.IsWeaklyContractible (Y i))
    (e : X.obj.left.obj ≅ ∐ fun i ↦ (Y i).obj) :
    (SmallProetale.topology B S hS).IsWeaklyContractible X := by
  classical
  let Z : I → Scheme.{u} := fun i ↦ (Y i).obj
  let g : ∀ i, Y i ⟶ X.obj.left := fun i ↦ B.inclusion.preimage (Sigma.ι Z i ≫ e.inv)
  have hg (i : I) : B.inclusion.map (g i) = Sigma.ι Z i ≫ e.inv := B.inclusion.map_preimage _
  have hopen (i : I) : IsOpenImmersion (B.inclusion.map (g i)) := by
    rw [hg]
    infer_instance
  have _ : WeaklyEtale (B.inclusion.map X.obj.hom) := X.property
  let V : I → SmallProetale B S hS := fun i ↦
    ⟨Over.mk (g i ≫ X.obj.hom), by
      have _ : IsOpenImmersion (B.inclusion.map (g i)) := hopen i
      change WeaklyEtale (B.inclusion.map (g i ≫ X.obj.hom))
      rw [B.inclusion.map_comp]
      infer_instance⟩
  let f : ∀ i, V i ⟶ X := fun i ↦ ObjectProperty.homMk (Over.homMk (g i))
  have hf (i : I) : (SmallProetale.toBigScheme B S hS).map (f i) = g i := rfl
  refine (SmallProetale.topology B S hS).isWeaklyContractible_of_disjointCover V f ?_ ?_ ?_ ?_
  -- the summands cover `X`, being a Zariski cover of its underlying scheme
  · refine ofArrows_mem_smallProetale_topology B S hS V f ?_
    apply Precoverage.generate_mem_toGrothendieck
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    change Presieve.ofArrows Z (fun i ↦ B.inclusion.map (g i)) ∈ _
    simp only [hg]
    have _ : MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    refine Scheme.zariskiPrecoverage_le_propQCPrecoverage _ ?_
    rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Z).surjective (e.hom.base x)
    refine ⟨i, y, ?_⟩
    change e.inv.base ((Sigma.ι Z i).base y) = x
    rw [← sigmaMk_mk, hy]
    exact congrArg (fun k : Scheme.Hom _ _ ↦ k.base x) e.hom_inv_id
  -- each summand is an open subscheme of `X`
  · intro i
    refine (SmallProetale.toBigScheme B S hS ⋙ B.inclusion).mono_of_mono_map ?_
    change Mono (B.inclusion.map ((SmallProetale.toBigScheme B S hS).map (f i)))
    rw [hf i]
    exact (hopen i).mono
  -- distinct summands do not meet
  · intro i j hij Z' a b hab
    refine bot_mem_smallProetale_topology B S hS Z' ⟨fun z ↦ ?_⟩
    have heq := congrArg
      (fun k ↦ ((SmallProetale.toBigScheme B S hS ⋙ B.inclusion).map k).base z) hab
    simp only [Functor.map_comp, Scheme.Hom.comp_apply] at heq
    change (B.inclusion.map ((SmallProetale.toBigScheme B S hS).map (f i))).base _ =
      (B.inclusion.map ((SmallProetale.toBigScheme B S hS).map (f j))).base _ at heq
    rw [hf i, hf j, hg i, hg j] at heq
    have heq' : (Sigma.ι Z i).base _ = (Sigma.ι Z j).base _ :=
      (Scheme.Hom.homeomorph e.inv).injective heq
    have hpair : (⟨i, _⟩ : Σ k : I, Z k) = ⟨j, _⟩ :=
      (sigmaMk Z).injective (by simpa only [sigmaMk_mk] using heq')
    exact hij (congrArg Sigma.fst hpair)
  -- an affine object with w-contractible ring of global sections is weakly contractible
  · intro i
    have _ : IsAffine (V i).obj.left.obj := (hY i).1
    have _ : IsAffine (Y i).obj := (hY i).1
    exact SmallProetale.surjective_sections_of_isWContractible B S hS (V i)
      (B.isWContractible_of_isWeaklyContractible (Y i) (hY i).2)

/-- **Stacks 0F4P for the small pro-étale site.** Every object `U` of the small pro-étale site
of `S` in a chosen big pro-étale site admits a one-element covering `{V → U}` whose source is a
weakly contractible object of that site.

The covering is the one of
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_coproduct_singleton_covering` for the
underlying object of the chosen big site: its covering morphism is weakly étale, so its source
is again weakly étale over `S`, and the source is a disjoint union of affine objects with
w-contractible rings of global sections, hence weakly contractible in the small site by
`AlgebraicGeometry.ProEtale.isWeaklyContractible_small_of_coproduct`. -/
@[stacks 0F4P "the small site"]
theorem exists_weaklyContractible_singleton_covering_small (U : SmallProetale B S hS) :
    ∃ (V : SmallProetale B S hS) (p : V ⟶ U),
      SmallProetale.IsCovering B S hS ⟨U, PreZeroHypercover.singleton p⟩ ∧
        (SmallProetale.topology B S hS).IsWeaklyContractible V := by
  obtain ⟨I, Y, V₀, p₀, e, hcov, hwc, hpwe, hY⟩ :=
    exists_weaklyContractible_coproduct_singleton_covering B U.obj.left
  let V : SmallProetale B S hS :=
    ⟨Over.mk (p₀ ≫ U.obj.hom), weaklyEtale_inclusion_map_comp B hpwe U.property⟩
  refine ⟨V, ObjectProperty.homMk (Over.homMk p₀), ?_, ?_⟩
  · exact hcov
  · exact isWeaklyContractible_small_of_coproduct B S hS V Y hY e

/-- **Stacks 0F4P for the small pro-étale site, the quasi-compact case.** If the underlying
scheme of an object `U` of the small pro-étale site of `S` is quasi-compact, the one-element
covering of
`AlgebraicGeometry.ProEtale.exists_weaklyContractible_singleton_covering_small` can be chosen
with affine source.

An affine weakly contractible object of the chosen big site has w-contractible ring of global
sections by Stacks 098H, which is weak contractibility in the small site by Stacks 0990. -/
@[stacks 0F4P "the small site, quasi-compact case"]
theorem exists_affine_weaklyContractible_singleton_covering_small
    (U : SmallProetale B S hS) [CompactSpace ((SmallProetale.toScheme B S hS).obj U)] :
    ∃ (V : SmallProetale B S hS) (p : V ⟶ U),
      SmallProetale.IsCovering B S hS ⟨U, PreZeroHypercover.singleton p⟩ ∧
        IsAffine ((SmallProetale.toScheme B S hS).obj V) ∧
        (SmallProetale.topology B S hS).IsWeaklyContractible V := by
  have _ : CompactSpace U.obj.left.obj :=
    inferInstanceAs (CompactSpace ((SmallProetale.toScheme B S hS).obj U))
  obtain ⟨V₀, p₀, hcov, haff, hwc, hpwe⟩ :=
    exists_affine_weaklyContractible_weaklyEtale_singleton_covering B U.obj.left
  let V : SmallProetale B S hS :=
    ⟨Over.mk (p₀ ≫ U.obj.hom), weaklyEtale_inclusion_map_comp B hpwe U.property⟩
  have _ : IsAffine V.obj.left.obj := haff
  refine ⟨V, ObjectProperty.homMk (Over.homMk p₀), ?_, haff, ?_⟩
  · exact hcov
  · have _ : IsAffine V₀.obj := haff
    exact SmallProetale.surjective_sections_of_isWContractible B S hS V
      (B.isWContractible_of_isWeaklyContractible V₀ hwc)

end AlgebraicGeometry.ProEtale

end
