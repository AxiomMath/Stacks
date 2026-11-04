module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SheafComparison

/-!
# Surjectivity of the comparison map of `Ω_{X/S}` along a closed immersion

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `Ω_{X/S}` be the presheaf of
crystalline differentials on the big crystalline category `CRIS(X/S)`.  For a morphism
`f : (U, T, δ) ⟶ (U', T', δ')` whose map `T ⟶ T'` on ambient schemes is a closed immersion, the
comparison morphism `c_f : f^*(Ω_{X/S})_{T'} ⟶ (Ω_{X/S})_T` of presheaves of `𝒪_T`-modules is
surjective: every section of `(Ω_{X/S})_T` is, locally on `T`, in the image of `c_f`.

The reason is the one of the source.  Over an open `W'` of `T'` the sections of `(Ω_{X/S})_{T'}`
are the divided power differentials of `Γ(W', 𝒪_{T'})` relative to the base, modulo the
differentials of the sections pulled back from the base, and those differentials generate; the
comparison carries the differential of a section to the differential of its image.  So over
`f⁻¹W'` the image of `c_f` contains a generating set as soon as `Γ(W', 𝒪_{T'}) ⟶ Γ(f⁻¹W', 𝒪_T)`
is surjective, which it is when `W'` is affine, a closed immersion being affine and surjective on
sections over an affine.  Finally a closed immersion is a topological embedding, so every open of
`T` is the preimage of an open of `T'`, and the preimages of the affine opens inside that one
cover it.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crysDifferentialsRestrictionModule` — the sections of
  the restriction of `Ω_{X/S}` to the ambient scheme of an object, as a module over the
  restriction of the structure presheaf of `CRIS(X/S)`.

## Main results

* `Crystalline.dpConstDifferentials_span` — the universal differentials generate the module of
  divided power differentials killing a set of constants.
* `Crystalline.GlobalCrystallineSituation.Thickening.range_moduleComparison_app` — over the
  preimage of an open of the ambient scheme of the target, the image of the comparison morphism
  of a presheaf of `𝒪_{X/S}`-modules contains the image of the transition map of that presheaf
  along the restricted morphism.
* `Crystalline.GlobalCrystallineSituation.surjective_appTop_restrictOpenMap` — the restriction of
  a morphism of `CRIS(X/S)` whose map on ambient schemes is a closed immersion is surjective on
  global sections over an affine open.
* `Crystalline.GlobalCrystallineSituation.surjective_moduleComparison_app` — over the preimage of
  an open on which the morphism is surjective on sections, the comparison morphism of `Ω_{X/S}`
  is surjective.
* `Crystalline.GlobalCrystallineSituation.isLocallySurjective_moduleComparison` — **Stacks, Tag
  07KM (2)**: for a morphism of `CRIS(X/S)` which is a closed immersion on ambient schemes the
  comparison morphism `c_f : f^*(Ω_{X/S})_{T'} ⟶ (Ω_{X/S})_T` of `Ω_{X/S}` is surjective.

## Implementation notes

`Ω_{X/S}` is a presheaf of modules on `CRIS(X/S)`, not a sheaf, and its restriction to the
ambient scheme of an object is a presheaf of `𝒪_T`-modules, not a sheaf
(`Crystalline.GlobalCrystallineSituation.crysDifferentials`, and the implementation notes of the
module defining it).  Surjectivity of a map of sheaves is a local condition, so for this presheaf
model the faithful rendering of the surjectivity of `c_f` is local surjectivity for the topology
of the opens of `T` — equivalently, surjectivity of the induced map of associated sheaves.  It is
not objectwise surjectivity, which is false: over an open of `T` which is not the preimage of an
affine open of `T'` the map on sections need not be surjective already.

The scalars are spelled two ways and have to be managed by hand, as in the modules this one
builds on.  The sections of the restriction of `Ω_{X/S}` over an open `W` are the sections of
`Ω_{X/S}` over the restricted object, a module over `Γ(W, 𝒪_W)`, while the restriction of the
structure presheaf spells the same ring as the sections of a presheaf of rings on `T`; the
instance identifying the two is supplied by name, and the span of the universal differentials is
taken at the second spelling so that the comparison morphism's image is a submodule for the same
ring.

## References

* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Crystalline

section Span

variable {A B : CommRingCat.{u}} {J : Ideal B}

/-- **The universal differentials generate the module of divided power differentials killing a set
of constants.**  A map out of that module is determined by its values on the universal
differentials, so the quotient by the submodule they span receives the zero map and is therefore
zero. -/
theorem dpConstDifferentials_span (f : A ⟶ B) (hJ : DividedPowers J) (T : Set B) :
    Submodule.span B (Set.range (dpConstD f hJ T).d) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  set N := Submodule.span B (Set.range (dpConstD f hJ T).d)
  suffices h : N.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero N).mp h
  have hz : (ModuleCat.ofHom N.mkQ :
      dpConstDifferentials f hJ T ⟶ ModuleCat.of B (↥(dpConstDifferentials f hJ T) ⧸ N)) = 0 := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    exact ((Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨b, rfl⟩)).trans rfl
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hz) x).trans rfl

end Span

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

open Thickening

/-- The sections of the restriction of `Ω_{X/S}` to the ambient scheme of an object, as a module
over the restriction of the structure presheaf of `CRIS(X/S)`; the two rings are the same, but
the restriction of the structure presheaf spells the scalars as the sections of a presheaf of
rings, so the instance is supplied by name. -/
instance crysDifferentialsRestrictionModule (A : Thickening S)
    (V : A.thickening.target.scheme.Opens) :
    Module Γ((A.restrictOpen V).thickening.target.scheme, ⊤)
      ↥((moduleRestriction (crysDifferentials S) A).obj (op V)) :=
  inferInstanceAs (Module Γ((A.restrictOpen V).thickening.target.scheme, ⊤)
    ↥(crysDifferentialsObj S (A.restrictOpen V)))

namespace Thickening

variable {A B : Thickening S} (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)

/-- **Over the preimage of an open of the ambient scheme of the target, the image of the
comparison morphism of a presheaf of `𝒪_{X/S}`-modules contains the image of the transition map
of that presheaf along the restriction of the morphism over that open.**  The `f`-map is the
transpose of the comparison morphism, so over the open it factors through the comparison morphism
over the preimage. -/
theorem range_moduleComparison_app (W : B.thickening.target.scheme.Opens) :
    Set.range ((M.map (restrictOpenMap g W).op).hom) ⊆
      Set.range ((moduleComparison M g).app (op (g.targetHom.hom ⁻¹ᵁ W))).hom := by
  have h := moduleFMap_eq_moduleComparison M g
  rw [Adjunction.homEquiv_unit] at h
  rintro _ ⟨y, rfl⟩
  have happ := congrArg (fun φ ↦ (φ.app (op W)).hom y) h
  change (M.map (restrictOpenMap g W).op).hom y = _ at happ
  exact ⟨_, happ.symm⟩

end Thickening

section Surjective

variable {A B : Thickening S} (g : A ⟶ B)

/-- **The restriction of a morphism of `CRIS(X/S)` whose map on ambient schemes is a closed
immersion is surjective on global sections over an affine open.**  On ambient schemes that
restriction is the restriction of the closed immersion over the open, and a closed immersion into
an affine scheme is surjective on global sections. -/
theorem surjective_appTop_restrictOpenMap [IsClosedImmersion g.targetHom.hom]
    (W : B.thickening.target.scheme.Opens) (hW : IsAffineOpen W) :
    Function.Surjective (restrictOpenMap g W).targetHom.hom.appTop.hom := by
  have : IsAffine W.toScheme := hW
  rw [restrictOpenMap_targetHom]
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (g.targetHom.hom ∣_ W)).2

/-- **Over the preimage of an open on which the morphism is surjective on global sections, the
comparison morphism of `Ω_{X/S}` is surjective on sections.**  The universal differentials
generate the sections of `Ω_{X/S}` over the restricted object, the comparison morphism carries the
universal differential of a section of the target to that of its image, and every section is such
an image. -/
theorem surjective_moduleComparison_app (W : B.thickening.target.scheme.Opens)
    (hsurj : Function.Surjective (restrictOpenMap g W).targetHom.hom.appTop.hom) :
    Function.Surjective
      ((moduleComparison (crysDifferentials S) g).app
        (op (g.targetHom.hom ⁻¹ᵁ W))).hom := by
  intro y
  have hspan := dpConstDifferentials_span
    (crysBaseAppLE S (A.restrictOpen (g.targetHom.hom ⁻¹ᵁ W)))
    (crysDividedPowers S (A.restrictOpen (g.targetHom.hom ⁻¹ᵁ W)))
    (crysBaseSections S (A.restrictOpen (g.targetHom.hom ⁻¹ᵁ W)))
  refine Submodule.span_induction
    (p := fun v _ ↦ v ∈ Set.range ((moduleComparison (crysDifferentials S) g).app
      (op (g.targetHom.hom ⁻¹ᵁ W))).hom) ?_ ⟨0, map_zero _⟩ ?_ ?_
    (Submodule.eq_top_iff'.mp hspan y)
  · rintro _ ⟨b, rfl⟩
    obtain ⟨b', rfl⟩ := hsurj b
    exact Thickening.range_moduleComparison_app S (crysDifferentials S) g W
      ⟨(crysDifferentialsD S (B.restrictOpen W)).d b',
        crysDifferentialsMap_d S (restrictOpenMap g W) b'⟩
  · rintro _ _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  · rintro r _ _ ⟨a, rfl⟩
    exact ⟨(show ↥((ringRestriction A).obj (op (g.targetHom.hom ⁻¹ᵁ W))) from r) • a,
      ((moduleComparison (crysDifferentials S) g).app
        (op (g.targetHom.hom ⁻¹ᵁ W))).hom.map_smul _ a⟩

/-- **Stacks Project, Tag 07KM (2).**  For a morphism `f : (U, T, δ) ⟶ (U', T', δ')` of
`CRIS(X/S)` whose map `T ⟶ T'` on ambient schemes is a closed immersion, the comparison morphism
`c_f : f^*(Ω_{X/S})_{T'} ⟶ (Ω_{X/S})_T` is surjective: every section of `(Ω_{X/S})_T` is, on the
members of an open covering, in the image of `c_f`.  A closed immersion is a topological
embedding, so every open of `T` is the preimage of an open of `T'`, and the preimages of the
affine opens contained in that one cover it; over each of those the comparison morphism is
already surjective on sections. -/
@[stacks 07KM "(2), the comparison map along a closed immersion is surjective"]
theorem isLocallySurjective_moduleComparison [IsClosedImmersion g.targetHom.hom] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (ringRestriction A)).map
        (moduleComparison (crysDifferentials S) g)) := by
  constructor
  intro V s x hx
  obtain ⟨W₀, hW₀open, hW₀⟩ := g.targetHom.hom.isClosedEmbedding.isInducing.isOpen_iff.mp V.2
  have hxW₀ : g.targetHom.hom.base x ∈ (⟨W₀, hW₀open⟩ :
      B.thickening.target.scheme.Opens) := hW₀.ge hx
  obtain ⟨W, hWaff, hxW, hWle⟩ :=
    (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens B.thickening.target.scheme)) hxW₀
  exact ⟨g.targetHom.hom ⁻¹ᵁ W, homOfLE fun z hz ↦ hW₀.le (hWle hz),
    surjective_moduleComparison_app S g W (surjective_appTop_restrictOpenMap S g W hWaff) _, hxW⟩

end Surjective

end GlobalCrystallineSituation

end Crystalline

end
