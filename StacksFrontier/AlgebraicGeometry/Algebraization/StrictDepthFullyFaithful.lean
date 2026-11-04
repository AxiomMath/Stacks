module

public import StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthRecoverSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHoms
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientSystemNearVanishingTilde

/-!
# Completion is fully faithful into a module with the strict depth inequalities

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `A` be `I`-adically complete with a dualizing
complex and `cd(A, I) ≤ d` for some `d ≥ 1`, and let `ℱ` be a coherent `𝒪_U`-module whose
completion along `I𝒪_U` satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3].
If moreover `depth(ℱ_x) ≥ 2` at every `x ∈ U` whose closure meets `Y` only inside `Z`, then

`Hom_U(𝒢, ℱ) ⟶ Hom_{Coh(U, I𝒪_U)}(𝒢^∧, ℱ^∧)`

is bijective for every coherent `𝒪_U`-module `𝒢`. This is [Stacks, Tag 0EJ7].

## Main results

* `Stacks.Algebraization.completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities` —
  **Stacks Tag 0EJ7**.
* `Stacks.Algebraization.completionFunctor_map_bijective_of_isIso_globalToFormalSections` — its
  content over [Stacks, Tag 0EJ6]: the theorem on formal functions in degree zero *for `ℱ`
  itself* already makes completion bijective on every hom set into `ℱ`.

## Implementation notes

### The shape of the proof

The source argues through the internal hom: it transports the strict inequalities and the
depth-two condition from `ℱ` to `ℋ = SheafHom(𝒢, ℱ)` by [Stacks, Tag 0EBC] or
[Stacks, Tag 0AV5] — "details omitted" — applies [Stacks, Tag 0EJ6] to `ℋ`, and identifies
`lim H⁰(U, ℋ/Iⁿℋ)` with `Hom_{Coh(U, I𝒪_U)}(𝒢^∧, ℱ^∧)` by [Stacks, Tag 0882].

That transport is not needed. [Stacks, Tag 0EJ6] for `ℱ` alone suffices, because

* `Hom_U(𝒢, -) ≅ Hom_A(Γ(U, 𝒢), Γ(U, -))` for quasi-coherent `𝒢`: this is the composite of
  Mathlib's `AlgebraicGeometry.tilde.adjunction` with
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` along `U ⟶ X`, whose right adjoint
  `Stacks.Algebraization.affineBaseSections` is `Γ(U, -)` read over `A` and whose counit is
  invertible at `𝒢`;
* [Stacks, Tag 0EJ6] says exactly that `Γ(U, -)` carries the tower of quotients
  `n ↦ ℱ/Iⁿℱ`, with its projections from `ℱ`, to a limit cone, so the right adjoint inverts
  `ℱ ⟶ lim_n ℱ/Iⁿℱ`; and
* a morphism `𝒢^∧ ⟶ ℱ^∧` of coherent adic systems is a morphism `𝒢 ⟶ lim_n ℱ/Iⁿℱ` of modules,
  by `Stacks.Algebraization.completionHomLimitEquiv`, compatibly with completion of morphisms.

The last of these is unconditional in this library, so the source's [Stacks, Tag 0882]
comparison for `ℋ` is not needed, and no hypothesis on `𝒢` beyond coherence is used — coherence
only to know `𝒢` quasi-coherent, and to have a completion of `𝒢` at all.

### The limit of the tower, and its shift

`Stacks.Algebraization.completionFunctor` indexes the completion by `n ↦ ℱ/I^(n+1)ℱ` while
`Stacks.Algebraization.adicQuotientCone` is indexed by the exponent itself, so the canonical
map `Stacks.Algebraization.completionToLimit` into the limit of the completion is the canonical
map into the limit of the tower followed by the shift
`Stacks.Algebraization.NeighbourhoodHoms.adicCompletionLimitIso`; that is
`Stacks.Algebraization.completionToLimit_eq_adicQuotientLift`.

### Hypotheses

Conditions (1), (2) and (3) of the source are the hypotheses verbatim, as they are in
[Stacks, Tag 0EJ6]; nothing else is assumed.

### Term-mode computations

In the two presentations `X.Modules` and `SheafOfModules X.ringCatSheaf` of one category the
rewrite motives of this subtree are ill-typed at `implicit` transparency, as in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/NeighbourhoodHoms.lean`, so the identities are chained with
`Eq.trans`/`congrArg` rather than rewritten.

## References

* [Stacks Project, Tag 0EJ7](https://stacks.math.columbia.edu/tag/0EJ7)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EJ6](https://stacks.math.columbia.edu/tag/0EJ6), the formal functions.
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880), the completion functor.
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882), the comparison the
  source uses instead of the adjunction above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.Algebraization.NeighbourhoodHoms

/-! ### The map into the limit of the completion, through the unshifted tower -/

section Shift

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The map into the limit of the completion is the map into the limit of the tower of
ideal-power quotients**, read through the shift of the tower. Both sides are normalized by the
projections onto the terms of the completion. -/
public theorem completionToLimit_eq_adicQuotientLift :
    limit.lift (adicQuotientSystem J F.obj) (adicQuotientCone J F.obj) ≫
        (adicCompletionLimitIso J F).hom =
      completionToLimit X J F := by
  refine limit.hom_ext fun n => ?_
  have h1 : (adicCompletionLimitIso J F).hom ≫
      limit.π ((completionFunctor X J).obj F).obj n =
      limit.π (adicQuotientSystem J F.obj) (op (n.unop + 1)) ≫ (towerIso J F n.unop).inv :=
    limit.lift_π (adicLimitCone J F) n
  have h2 : limit.lift (adicQuotientSystem J F.obj) (adicQuotientCone J F.obj) ≫
      limit.π (adicQuotientSystem J F.obj) (op (n.unop + 1)) =
      cokernel.π (C := X.Modules) (idealPowerMultiple J (n.unop + 1) F.obj).ι :=
    limit.lift_π (adicQuotientCone J F.obj) (op (n.unop + 1))
  rw [Category.assoc, h1, ← Category.assoc, h2, ← completionProjection_comp_towerIso]
  refine Eq.trans ?_ (completionToLimit_projection X J F n).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => completionProjection X J F n.unop ≫ k)
      (towerIso J F n.unop).hom_inv_id).trans (Category.comp_id _))

/-- **A functor that takes the tower of ideal-power quotients to a limit cone inverts the map
into the limit of the completion.** The map into the limit of the completion factors as the map
into the limit of the tower followed by the shift, and the shift is an isomorphism; the first
factor becomes the comparison of two limit cones. -/
public theorem isIso_map_completionToLimit_of_isLimit {C : Type*} [Category C]
    (T : X.Modules ⥤ C) [PreservesLimit (adicQuotientSystem J F.obj) T]
    (h : IsLimit (T.mapCone (adicQuotientCone J F.obj))) :
    IsIso (T.map (completionToLimit X J F)) := by
  have hlim : IsLimit (T.mapCone (limit.cone (adicQuotientSystem J F.obj))) :=
    isLimitOfPreserves T (limit.isLimit _)
  have heq : hlim.lift (T.mapCone (adicQuotientCone J F.obj)) =
      T.map (limit.lift (adicQuotientSystem J F.obj) (adicQuotientCone J F.obj)) :=
    hlim.hom_ext fun n => (hlim.fac _ n).trans
      ((T.map_comp _ _).symm.trans
        (congrArg T.map (limit.lift_π (adicQuotientCone J F.obj) n))).symm
  have hlift : IsIso (T.map
      (limit.lift (adicQuotientSystem J F.obj) (adicQuotientCone J F.obj))) :=
    heq ▸ (IsLimit.conePointUniqueUpToIso h hlim).isIso_hom
  have hshift : IsIso (T.map (adicCompletionLimitIso J F).hom) :=
    (T.mapIso (adicCompletionLimitIso J F)).isIso_hom
  have key : T.map (limit.lift (adicQuotientSystem J F.obj) (adicQuotientCone J F.obj)) ≫
      T.map (adicCompletionLimitIso J F).hom = T.map (completionToLimit X J F) :=
    (T.map_comp _ _).symm.trans (congrArg T.map (completionToLimit_eq_adicQuotientLift J F))
  exact key ▸ IsIso.comp_isIso' hlift hshift

end Shift

/-! ### Sections on the complement, over the base ring -/

section BaseSections

variable (A : Type u) [CommRing A] (a : Ideal A)

/-- The sections of a module on `U = Spec(A) ∖ V(𝔞)`, as an `A`-module: the pushforward along
`U ⟶ Spec(A)` followed by global sections. It is the right adjoint of the composite of
`AlgebraicGeometry.tilde.adjunction` with
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. -/
public abbrev affineBaseSections :
    (complementZeroLocus A a : Scheme).Modules ⥤ ModuleCat.{u} A :=
  Scheme.Modules.pushforward (complementZeroLocus A a).ι ⋙ moduleSpecΓFunctor

/-- The adjunction whose right adjoint is `Stacks.Algebraization.affineBaseSections`: a module
over the base ring becomes a module on `Spec(A)` and is restricted to `U`. -/
public abbrev affineBaseSectionsAdjunction :=
  (tilde.adjunction (R := .of A)).comp
    (Scheme.Modules.restrictAdjunction (complementZeroLocus A a).ι)

/-- **A right adjoint is bijective on the morphisms out of an object where its counit is
invertible.** -/
public theorem map_bijective_of_isIso_counit {C : Type*} {D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (M N : D) [IsIso (adj.counit.app M)] :
    Function.Bijective (fun f : M ⟶ N => R.map f) := by
  let e : (M ⟶ N) ≃ (R.obj M ⟶ R.obj N) :=
    (Iso.homCongr (asIso (adj.counit.app M)).symm (Iso.refl N)).trans
      (adj.homEquiv (R.obj M) N)
  have he (f : M ⟶ N) : e f = R.map f := by
    simp [e, adj.homEquiv_unit, ← Category.assoc, adj.right_triangle_components]
  have hb := e.bijective
  rwa [show (⇑e) = (fun f : M ⟶ N => R.map f) from funext he] at hb

/-- Sections over `U`, read over the base ring, preserve all limits: they are a right adjoint. -/
public instance preservesLimit_affineBaseSections {D : Type*} [Category D]
    (K : D ⥤ (complementZeroLocus A a : Scheme).Modules) :
    PreservesLimit K (affineBaseSections A a) := by
  have := (affineBaseSectionsAdjunction A a).rightAdjoint_preservesLimits
  infer_instance

variable [IsNoetherianRing A]

/-- **The counit of `Stacks.Algebraization.affineBaseSectionsAdjunction` is invertible at a
quasi-coherent module.** Over a Noetherian ring the open immersion `U ⟶ Spec(A)` is quasi-compact
and quasi-separated, so the pushforward of a quasi-coherent module is quasi-coherent and the two
counits in the composite are invertible. -/
public theorem isIso_affineBaseSectionsAdjunction_counit_app
    (G : (complementZeroLocus A a : Scheme).Modules) [G.IsQuasicoherent] :
    IsIso ((affineBaseSectionsAdjunction A a).counit.app G) := by
  have hqc : ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj G).IsQuasicoherent :=
    inferInstance
  have htilde : IsIso ((tilde.adjunction (R := .of A)).counit.app
      ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj G)) :=
    (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ _).mp hqc
  rw [affineBaseSectionsAdjunction, Adjunction.comp_counit_app]
  infer_instance

/-- **Sections over `U`, read over the base ring, are fully faithful out of a quasi-coherent
module.** Only the source has to be quasi-coherent. -/
public theorem affineBaseSections_map_bijective
    (G M : (complementZeroLocus A a : Scheme).Modules) [G.IsQuasicoherent] :
    Function.Bijective (fun f : G ⟶ M => (affineBaseSections A a).map f) :=
  have := isIso_affineBaseSectionsAdjunction_counit_app A a G
  map_bijective_of_isIso_counit (affineBaseSectionsAdjunction A a) G M

/-- **Composing with a morphism that sections over `U` invert is bijective on the morphisms out
of a quasi-coherent module.** -/
public theorem bijective_comp_of_isIso_affineBaseSections_map
    {M N : (complementZeroLocus A a : Scheme).Modules}
    (G : (complementZeroLocus A a : Scheme).Modules) [G.IsQuasicoherent] (f : M ⟶ N)
    (hf : IsIso ((affineBaseSections A a).map f)) :
    Function.Bijective (fun h : G ⟶ M => h ≫ f) := by
  have := hf
  have hM := affineBaseSections_map_bijective A a G M
  have hN := affineBaseSections_map_bijective A a G N
  have hmap (p : G ⟶ M) : (affineBaseSections A a).map (p ≫ f) =
      (affineBaseSections A a).map p ≫ (affineBaseSections A a).map f :=
    Functor.map_comp _ _ _
  refine ⟨fun p q hpq => hM.1 ?_, fun k => ?_⟩
  · exact (cancel_mono ((affineBaseSections A a).map f)).1
      ((hmap p).symm.trans ((congrArg _ hpq).trans (hmap q)))
  · obtain ⟨p, hp⟩ := hM.2 ((affineBaseSections A a).map k ≫ inv ((affineBaseSections A a).map f))
    exact ⟨p, hN.1 (by
    simp only [hmap, hp, Category.assoc, IsIso.inv_hom_id, Category.comp_id])⟩

end BaseSections

/-! ### The criterion: full faithfulness into one module -/

/-- **The theorem on formal functions in degree zero for `ℱ` makes completion bijective on every
hom set into `ℱ`.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, write `U = Spec(A) ∖ V(𝔞)`,
and let `ℱ` be a coherent `𝒪_U`-module for which

  `H⁰(U, ℱ) ⟶ lim H⁰(U, ℱ / Iⁿ ℱ)`

is an isomorphism. Then completion along `I𝒪_U` is bijective on the morphisms `𝒢 ⟶ ℱ` for every
coherent `𝒪_U`-module `𝒢`.

Sections over `U`, read over `A`, therefore carry the tower of quotients of `ℱ` to a limit cone,
so they invert `ℱ ⟶ lim_n ℱ/Iⁿℱ`; being a right adjoint whose counit is invertible at the
quasi-coherent `𝒢`, they are fully faithful out of `𝒢`, and composition with that arrow is
bijective on `𝒢 ⟶ ℱ`. Finally `Stacks.Algebraization.completionHomLimitEquiv` reads a morphism
`𝒢 ⟶ lim_n ℱ/Iⁿℱ` as a morphism `𝒢^∧ ⟶ ℱ^∧`, compatibly with completion of morphisms by
`Stacks.Algebraization.completionHomLimitEquiv_comp_completionToLimit`. -/
public theorem completionFunctor_map_bijective_of_isIso_globalToFormalSections
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf)
    (hFF : IsIso (FormalSectionsII.globalToFormalSections A I a F.obj))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf) :
    Function.Bijective ((completionFunctor (complementZeroLocus A a : Scheme)
        (idealSheafNearVanishing A I a)).map :
      (G ⟶ F) →
        ((completionFunctor (complementZeroLocus A a : Scheme)
            (idealSheafNearVanishing A I a)).obj G ⟶
          (completionFunctor (complementZeroLocus A a : Scheme)
            (idealSheafNearVanishing A I a)).obj F)) := by
  have hqc : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  -- Sections over `U` take the tower of ideal-power quotients of `ℱ` to a limit cone.
  have hAb : IsLimit ((sectionsAb (complementZeroLocus A a : Scheme)).mapCone
      (adicQuotientCone (idealSheafNearVanishing A I a) F.obj)) :=
    IsLimit.ofIsoLimit (limit.isLimit (formalSections A I a F.obj))
      (Cone.ext (@asIso _ _ _ _ _ hFF)
        (fun n => (FormalSectionsII.globalToFormalSections_proj A I a F.obj n.unop).symm)).symm
  have hlim : IsLimit ((affineBaseSections A a).mapCone
      (adicQuotientCone (idealSheafNearVanishing A I a) F.obj)) :=
    isLimitOfReflects (forget₂ (ModuleCat.{u} A) Ab.{u}) hAb
  -- Hence they invert the canonical map into the limit of the completion.
  have hiso : IsIso ((affineBaseSections A a).map
      (completionToLimit (complementZeroLocus A a : Scheme)
        (idealSheafNearVanishing A I a) F)) :=
    isIso_map_completionToLimit_of_isLimit _ F _ hlim
  -- So composing with that map is bijective on the morphisms out of `𝒢`.
  have hcomp : Function.Bijective (fun h : G.obj ⟶ F.obj =>
      h ≫ completionToLimit (complementZeroLocus A a : Scheme)
        (idealSheafNearVanishing A I a) F) :=
    bijective_comp_of_isIso_affineBaseSections_map A a G.obj _ hiso
  have hhom : Function.Bijective (fun g : G ⟶ F => g.hom) :=
    ⟨fun _ _ e => ObjectProperty.hom_ext _ e, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  have hbij := (completionHomLimitEquiv (I := idealSheafNearVanishing A I a) G
    ((completionFunctor (complementZeroLocus A a : Scheme)
      (idealSheafNearVanishing A I a)).obj F)).bijective.comp (hcomp.comp hhom)
  have hmap : (⇑(completionHomLimitEquiv (I := idealSheafNearVanishing A I a) G
          ((completionFunctor (complementZeroLocus A a : Scheme)
            (idealSheafNearVanishing A I a)).obj F)) ∘
        (fun h : G.obj ⟶ F.obj => h ≫ completionToLimit (complementZeroLocus A a : Scheme)
          (idealSheafNearVanishing A I a) F) ∘ fun g : G ⟶ F => g.hom) =
      ((completionFunctor (complementZeroLocus A a : Scheme)
          (idealSheafNearVanishing A I a)).map :
        (G ⟶ F) → _) :=
    funext fun g => completionHomLimitEquiv_comp_completionToLimit _ G F g
  exact hmap ▸ hbij

/-! ### Stacks 0EJ7 -/

/-- **Stacks Project, Tag 0EJ7.** Let `A` be a Noetherian ring with ideals `I ⊆ 𝔞`, write
`X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)`, `U = X ∖ Z`, and let `ℱ` be a coherent `𝒪_U`-module and
`d ≥ 1`. Assume

1. `A` is `I`-adically complete, has a dualizing complex, and `cd(A, I) ≤ d`,
2. the completion `ℱ^∧` of `ℱ` along `I𝒪_U` satisfies the strict `(1, 1 + d)`-inequalities of
   [Stacks, Tag 0EJ3], and
3. `depth(ℱ_x) ≥ 2` for every `x ∈ U` with `\overline{\{x\}} ∩ Y ⊆ Z`.

Then

  `Hom_U(𝒢, ℱ) ⟶ Hom_{Coh(U, I𝒪_U)}(𝒢^∧, ℱ^∧)`

is bijective for every coherent `𝒪_U`-module `𝒢`. The map is the action on morphisms of the
completion functor `Stacks.Algebraization.completionFunctor` of [Stacks, Tag 0880].

The hypotheses are those of [Stacks, Tag 0EJ6] —
`Stacks.Algebraization.isIso_globalToFormalSections_of_satisfiesStrictDepthInequalities` — and
that lemma is what is applied: it gives the theorem on formal functions in degree zero for `ℱ`,
which already forces the conclusion for every coherent `𝒢` by
`Stacks.Algebraization.completionFunctor_map_bijective_of_isIso_globalToFormalSections`. The
source instead applies [Stacks, Tag 0EJ6] to `SheafHom(𝒢, ℱ)`, after a transport of conditions
(2) and (3) to that module whose details it omits; no such transport is needed here. -/
@[stacks 0EJ7 "Hom_U(G,F) = Hom_{Coh(U,IO_U)}(G^∧,F^∧) for every coherent G, under the strict \
(1,1+d)-inequalities and depth two off the formal locus; 0EJ6 applied to F itself"]
public theorem completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : cohomologicalDimension S.A S.I S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (hdepth : FormalSectionsII.DepthTwoOffFormalLocus S.A S.I S.a F.obj)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf) :
    Function.Bijective ((completionFunctor S.U.toScheme (idealOnOpen S)).map :
      (G ⟶ F) →
        ((completionFunctor S.U.toScheme (idealOnOpen S)).obj G ⟶
          (completionFunctor S.U.toScheme (idealOnOpen S)).obj F)) := by
  rw [idealOnOpen_eq_baseIdealSheaf S]
  exact completionFunctor_map_bijective_of_isIso_globalToFormalSections S.A S.I S.a F
    (isIso_globalToFormalSections_of_satisfiesStrictDepthInequalities S F d hd K hK hcd
      hstrict hdepth)
    G

end Stacks.Algebraization

end
