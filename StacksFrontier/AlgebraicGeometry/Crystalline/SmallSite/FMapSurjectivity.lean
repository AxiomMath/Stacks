module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackSectionsCollapse

/-!
# From a surjective comparison map to a surjective `f`-map on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`, a presheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site `Cris(X/S)` and a morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)`.
There are two conditions the source of [Stacks, Tag 07JN] passes between freely, calling them
equivalent:

* (a) local surjectivity of the comparison map `c_f : f^* F_{T'} ⟶ F_T` on `T`, which is
  hypothesis (2) of that proposition,
  `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.IsSurjectiveComparison`;
* (b) local surjectivity of the `f`-map `F_{T'} ⟶ f_* F_T` on `T'`, whose sections over an open
  `W` of `T'` are the transition maps `F(U' ∩ W, W, δ'|_W) ⟶ F(U ∩ f^{-1}W, f^{-1}W, δ|_{f^{-1}W})`
  of `F` itself.

The implication (b) ⟹ (a) is immediate from the adjunction, and
`Crystalline.GlobalCrystallineSituation.Thickening.range_moduleComparison_app` is its objectwise
form.  **This file proves (a) ⟹ (b)**, which is the implication the proof of [Stacks, Tag 07JN]
uses and which needs more than the adjunction: a priori the image of `c_f` is only the submodule
*generated* by the image of the `f`-map
(`...CohomologyRestriction.range_moduleComparison_app_eq_fmapSubmodule`), and the collapse of that
submodule to the image is `PresheafOfModules.range_homEquivSymm_app_eq_range_appₛₗ` of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackSectionsCollapse`.

## Main results

* `TopologicalSpace.Opens.full_map_of_surjective` — for a **surjective** continuous map, the
  functor of preimages on open sets is full.  This is what lets the general collapse apply: the
  generators of the image of `c_f` over an open of `T` are restrictions along arbitrary morphisms
  of `Opens T`, and fullness is what writes those as preimages of morphisms of `Opens T'`.
* `...CohomologyRestriction.surjective_restrictionFMap_app` — over an **affine** open `W` of `T'`
  the `f`-map of the structure presheaf, `𝒪_{T'}(W) ⟶ 𝒪_T(f^{-1}W)`, is surjective when `f` is a
  closed immersion on ambient schemes.
* `...CohomologyRestriction.range_moduleComparison_app_eq_range_map_restrictOpenMap` — **over the
  preimage of an affine open the image of `c_f` is exactly the image of the transition map of `F`**,
  for a closed immersion `f` whose map on ambient schemes is surjective.  The lemma
  `Thickening.range_moduleComparison_app` is the inclusion `⊇` of this, with no hypotheses; the
  inclusion `⊆` is what is new.
* `...CohomologyRestriction.isLocallySurjective_moduleFMap_of_isLocallySurjective_moduleComparison`
  — **(a) ⟹ (b)** for a single morphism: a locally surjective `c_f` on `T` forces a locally
  surjective `f`-map on `T'`, when the map on ambient schemes is a closed immersion **and
  surjective**.
* `...CohomologyRestriction.isLocallySurjective_moduleFMap` — the same implication with hypothesis
  (2) of [Stacks, Tag 07JN] itself as the hypothesis.
* `...CohomologyRestriction.surjective_targetHom_base_of_isIso_toX` — a morphism between objects
  **over the whole of `X`** is surjective on the points of the ambient schemes, which is what
  discharges that surjectivity hypothesis where [Stacks, Tag 07JN] needs it.
* `...CohomologyRestriction.isLocallySurjective_moduleFMap_of_isIso_toX` — **(a) ⟹ (b) with no
  extra hypothesis**, for a closed immersion between objects over the whole of `X`, that is, inside
  the subcategory `𝒞` of [Stacks, Tag 07JK] in which the proof of [Stacks, Tag 07JN] runs.

## What is and is not proved

The hypotheses, exactly.

* `surjective_restrictionFMap_app` assumes that the map on ambient schemes is a closed immersion
  and that `W` is an affine open.  Both are needed and neither is a stand-in: the statement is
  false for a non-affine `W`, since a closed immersion need not be surjective on sections over a
  non-affine open.
* `range_moduleComparison_app_eq_range_map_restrictOpenMap` and
  `isLocallySurjective_moduleFMap` assume in addition that the underlying continuous map
  `T ⟶ T'` is **surjective**, carried as the explicit hypothesis
  `Function.Surjective g.hom.targetHom.hom.base`.  This hypothesis is *not* a weakening dressed up
  as a result, and it is not vacuous: it is what makes the functor of preimages
  `Opens T' ⥤ Opens T` full, without which a generator of the image of `c_f` over an open of `T`
  need not be a value of the `f`-map at all.  It is also **not an assumption the consumer is left
  with**: it is *proved*, in `surjective_targetHom_base_of_isIso_toX`, for exactly the morphisms
  [Stacks, Tag 07JN] uses, namely those between objects over the whole of `X`, where the two
  structure maps `U ⟶ X` and `U' ⟶ X` are isomorphisms; and
  `isLocallySurjective_moduleFMap_of_isIso_toX` is the resulting hypothesis-free form.  The
  surjectivity is nevertheless kept as a hypothesis of the general statements, because it is what
  they actually use and because it holds more widely than for whole-space objects.
* No hypothesis of quasi-coherence, flatness, local freeness or affineness of the ambient schemes
  is used anywhere below.  Affineness enters only through the affine opens of `T'`, which form a
  basis of `T'` whatever `T'` is, and is not a hypothesis on the situation.

What is **not** proved.

* **The consequence [Stacks, Tag 07JN] actually consumes is still open.**  That proposition needs
  the *global* surjectivity of `Γ(T', F_{T'}) ⟶ Γ(T, F_T)` over an affine `T'`, and the step from
  the local surjectivity proved here to that global surjectivity is the source's cohomological
  argument: the kernel `K` of `F_{T'} ⟶ f_* F_T` is quasi-coherent and `H^1(T', K) = 0` because
  `T'` is affine.  The quasi-coherence of `K` rests on hypothesis (1) of the proposition, local
  quasi-coherence of `F`, and is a separate step; nothing here supplies it.  What this file removes
  is the obstruction recorded in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean`, namely that there
  was no route from (a) to (b) at all.
* **No `@[stacks]` attribute is placed.**  The equivalence of (a) and (b) is a step inside the
  proof of [Stacks, Tag 07JN], not the content of a tag.

## References

* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace TopologicalSpace.Opens

/-- **The functor of preimages on open sets of a surjective continuous map is full.**  If
`f : X ⟶ Y` is surjective and `f^{-1}U ≤ f^{-1}V` for opens `U`, `V` of `Y`, then `U ≤ V`: a point
of `U` is the image of a point of `f^{-1}U`, hence of a point of `f^{-1}V`.  Morphisms of a lattice
of opens are unique, so this inequality is the required preimage.

Without surjectivity the statement fails: for an empty `X` every `f^{-1}U` is empty, so every
morphism `f^{-1}U ⟶ f^{-1}V` exists while `U ≤ V` may be false. -/
theorem full_map_of_surjective {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : Function.Surjective f) :
    (Opens.map f).Full where
  map_surjective {U V} i :=
    ⟨homOfLE fun y hy ↦ by
      obtain ⟨x, rfl⟩ := hf y
      exact i.le (show x ∈ (Opens.map f).obj U from hy), Subsingleton.elim _ _⟩

end TopologicalSpace.Opens

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (M : PresheafOfModules.{u} (crisRing S))
  {A B : CrystallineThickening S} (g : A ⟶ B)

/-- **A morphism between objects of `Cris(X/S)` over the whole of `X` is surjective on the points
of the ambient schemes.**  The structure maps `U ⟶ X` and `U' ⟶ X` being isomorphisms, the map
`U ⟶ U'` on thickened schemes is an isomorphism, and both immersions `U ⟶ T` and `U' ⟶ T'` are
surjective on points, being thickenings; the commuting square then writes a point of `T'` as the
image of a point of `T`.

The hypotheses are the predicate
`Crystalline.GlobalCrystallineSituation.SmallSite.IsOverWholeSpace` at the two objects, which cuts
out the subcategory `𝒞` of [Stacks, Tag 07JK] in which the proof of [Stacks, Tag 07JN] works, and
are spelled out as `IsIso` of the structure maps so that this module need not import the
module defining `𝒞`.  This is what discharges the surjectivity hypothesis of
`isLocallySurjective_moduleFMap` for the morphisms that proposition uses. -/
theorem surjective_targetHom_base_of_isIso_toX {A B : CrystallineThickening S} (g : A ⟶ B)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Function.Surjective g.hom.targetHom.hom.base := by
  have := hA
  have := hB
  have : IsIso g.hom.sourceHom := by
    rw [show g.hom.sourceHom = A.obj.toX ≫ inv B.obj.toX by
      rw [← g.hom.toX_naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    infer_instance
  intro y
  obtain ⟨b, hb⟩ := B.obj.thickening.isThickening.2 y
  obtain ⟨a, ha⟩ := g.hom.sourceHom.surjective b
  refine ⟨A.obj.thickening.immersion.base a, ?_⟩
  have hnat := congrArg
    (fun φ : A.obj.thickening.source ⟶ B.obj.thickening.target.scheme ↦ φ a)
    g.hom.immersion_naturality
  simp only [Scheme.Hom.comp_apply] at hnat
  rw [show g.hom.targetHom.hom.base (A.obj.thickening.immersion.base a) =
    g.hom.targetHom.hom (A.obj.thickening.immersion a) from rfl, hnat, ha, hb]

/-- **Over an affine open of the ambient scheme of the target, the `f`-map of the structure
presheaf is surjective**, when the map on ambient schemes is a closed immersion: it is the map on
global sections of the restriction of that closed immersion over the open, and a closed immersion
into an affine scheme is surjective on global sections.  This is the small-site reading of
`Crystalline.GlobalCrystallineSituation.surjective_appTop_restrictOpenMap`. -/
theorem surjective_restrictionFMap_app (hg : IsClosedImmersion g.hom.targetHom.hom)
    {W : B.obj.thickening.target.scheme.Opens} (hW : IsAffineOpen W) :
    Function.Surjective ((restrictionFMap (crisRing S) g).app (op W)).hom :=
  have := hg
  GlobalCrystallineSituation.surjective_appTop_restrictOpenMap S g.hom W hW

/-- **Over the preimage of an affine open, the image of the comparison morphism
`c_f : f^* F_{T'} ⟶ F_T` is exactly the image of the transition map of `F` along the restriction
of `f` over that open.**

The inclusion `⊇` is `Crystalline.GlobalCrystallineSituation.Thickening.range_moduleComparison_app`
and needs no hypothesis.  The inclusion `⊆` is the one the source uses and is what is proved here:
by `PresheafOfModules.range_homEquivSymm_app_eq_generatedSubmodule` the image of `c_f` is the
submodule generated by the image of the `f`-map, the generators over the preimage of `W` are values
of the `f`-map at `W` again because the functor of preimages is full
(`TopologicalSpace.Opens.full_map_of_surjective`), and the submodule they generate is their own set
of values because `𝒪_{T'}(W) ⟶ 𝒪_T(f^{-1}W)` is surjective over an affine `W`
(`surjective_restrictionFMap_app`).

The hypothesis that the map on ambient schemes is surjective is used only for the fullness; see the
module docstring for why it is harmless in the situation of [Stacks, Tag 07JN] and for what it
still owes. -/
theorem range_moduleComparison_app_eq_range_map_restrictOpenMap
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hsurj : Function.Surjective g.hom.targetHom.hom.base)
    {W : B.obj.thickening.target.scheme.Opens} (hW : IsAffineOpen W) :
    Set.range ((moduleComparison M g).app (op (g.hom.targetHom.hom ⁻¹ᵁ W))).hom =
      Set.range ((M.map (CrystallineThickening.restrictOpenMap g W).op).hom) :=
  have := Opens.full_map_of_surjective hsurj
  PresheafOfModules.range_homEquivSymm_app_eq_range_appₛₗ (restrictionFMap (crisRing S) g)
    (moduleFMap M g) (X₀ := op W) (surjective_restrictionFMap_app g hg hW)

/-- **Hypothesis (2) of [Stacks, Tag 07JN] implies the local surjectivity of the `f`-map.**  Let
`f : (U, T, δ) ⟶ (U', T', δ')` be a morphism of `Cris(X/S)` whose map on ambient schemes is a
closed immersion and is surjective.  If the comparison morphism `c_f : f^* F_{T'} ⟶ F_T` is
locally surjective on `T`, then the `f`-map `F_{T'} ⟶ f_* F_T` is locally surjective on `T'`:
every section of `F_T` over `f^{-1}W'` is, on the members of an open covering of `W'`, a
transition of a section of `F_{T'}`.

This is the passage the source makes when it calls the surjectivity of `c_f` and of the `f`-map
equivalent.  The proof is pointwise in `T'`: a point of `W'` is the image of a point of `f^{-1}W'`,
local surjectivity of `c_f` gives an open of `T` around that point over which the section is a
value of `c_f`, that open is the preimage of an open of `T'` because a closed immersion is
topologically inducing, intersecting with `W'` and shrinking to an affine open keeps that property
because the image sieve is a sieve, and over the preimage of an affine open the image of `c_f` is
the image of the `f`-map by
`range_moduleComparison_app_eq_range_map_restrictOpenMap`. -/
theorem isLocallySurjective_moduleFMap_of_isLocallySurjective_moduleComparison
    (hc : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (ringRestriction A)).map (moduleComparison M g)))
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hsurj : Function.Surjective g.hom.targetHom.hom.base) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (ringRestriction B)).map (moduleFMap M g)) := by
  have := hg
  have := Opens.full_map_of_surjective hsurj
  refine ⟨fun {W'} s x hx ↦ ?_⟩
  obtain ⟨x₀, hx₀⟩ := hsurj x
  have hcov := hc.imageSieve_mem
    (U := (Opens.map g.hom.targetHom.hom.base).obj W') s
  rw [Opens.mem_grothendieckTopology] at hcov
  obtain ⟨Z, i, hZ, hx₀Z⟩ := hcov x₀ (by rwa [Opens.mem_map, hx₀])
  obtain ⟨V₁, hV₁open, hV₁⟩ :=
    (g.hom.targetHom.hom.isClosedEmbedding).isInducing.isOpen_iff.mp Z.2
  have hxV₁ : x ∈ (⟨V₁, hV₁open⟩ : B.obj.thickening.target.scheme.Opens) := by
    rw [← hx₀]
    exact hV₁.ge hx₀Z
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens B.obj.thickening.target.scheme))
      (show x ∈ (⟨V₁, hV₁open⟩ : B.obj.thickening.target.scheme.Opens) ⊓ W' from ⟨hxV₁, hx⟩)
  have hpre : (Opens.map g.hom.targetHom.hom.base).obj V ≤ Z := fun z hz ↦
    hV₁.le (show g.hom.targetHom.hom.base z ∈ V₁ from (hVle hz).1)
  refine ⟨V, homOfLE fun z hz ↦ (hVle hz).2, ?_, hxV⟩
  obtain ⟨t, ht⟩ := Sieve.downward_closed _ hZ (homOfLE hpre)
  obtain ⟨n, hn⟩ :=
    (range_moduleComparison_app_eq_range_map_restrictOpenMap M g hg hsurj hVaff).le
      (Set.mem_range_self t)
  exact ⟨n, hn.trans ht⟩

/-- **Hypothesis (2) of [Stacks, Tag 07JN] implies the local surjectivity of the `f`-map**, in the
form in which the hypothesis is stated: if `F` has surjective closed immersion comparison maps then
the `f`-map `F_{T'} ⟶ f_* F_T` of a morphism whose map on ambient schemes is a closed immersion and
is surjective is locally surjective on `T'`.

This is the implication (a) ⟹ (b) that the source's proof uses and that this library did not have.
Only the comparison map of the one morphism `g` is used, which is
`isLocallySurjective_moduleFMap_of_isLocallySurjective_moduleComparison`. -/
theorem isLocallySurjective_moduleFMap (hM : IsSurjectiveComparison M)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hsurj : Function.Surjective g.hom.targetHom.hom.base) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (ringRestriction B)).map (moduleFMap M g)) :=
  isLocallySurjective_moduleFMap_of_isLocallySurjective_moduleComparison M g (hM g hg) hg hsurj

/-- **(a) ⟹ (b) in the subcategory `𝒞` of [Stacks, Tag 07JK], with no extra hypothesis.**  For a
morphism of `Cris(X/S)` between objects over the whole of `X` whose map on ambient schemes is a
closed immersion, hypothesis (2) of [Stacks, Tag 07JN] implies that the `f`-map
`F_{T'} ⟶ f_* F_T` is locally surjective on `T'`.

The surjectivity on points that `isLocallySurjective_moduleFMap` asks for is supplied by
`surjective_targetHom_base_of_isIso_toX`, so this is the form in which the implication the source
calls an equivalence is available where the proof of [Stacks, Tag 07JN] needs it: the objects of
its category `𝒞` are exactly those with `IsIso A.obj.toX`. -/
theorem isLocallySurjective_moduleFMap_of_isIso_toX (hM : IsSurjectiveComparison M)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (ringRestriction B)).map (moduleFMap M g)) :=
  isLocallySurjective_moduleFMap M g hM hg (surjective_targetHom_base_of_isIso_toX g hA hB)

end Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

end

end
