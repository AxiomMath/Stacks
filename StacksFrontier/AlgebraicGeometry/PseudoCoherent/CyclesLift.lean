module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SingleApproximation

/-!
# Lifting a local epimorphism onto a cohomology sheaf to the cycles

Let `X` be a ringed space, let `𝒦` be a complex of `𝒪_X`-modules and suppose `H^p(𝒦)` is an
`𝒪_X`-module of finite type. Then, locally on `X`, there is a direct summand `𝒜` of a finite free
module and a map `𝒜 ⟶ Z^p(𝒦)` whose composite with `Z^p(𝒦) ⟶ H^p(𝒦)` is an epimorphism.

This is the step of the converse half of Stacks 09VA which turns the finite generation of
`H^p(ℰ^•)` into the map `𝒪_Z^{⊕n}[-p] ⟶ ℰ^•` of the source proof. It is exactly the hypothesis of
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_local_epi_homologyπ`.

Two shrinkings happen, and they land on different spaces, which is the whole difficulty. Finite
type gives an epimorphism `𝒪_{X|U₀}^{⊕n} ⟶ H^p(𝒦)|_{U₀}` on an open `U₀` of `X`; lifting it
through the epimorphism `Z^p(𝒦|_{U₀}) ⟶ H^p(𝒦|_{U₀})` is Stacks 08C6 over an open subset
(`AlgebraicGeometry.RingedSpace.exists_local_lift_over_of_isDirectSummandOfFiniteFree`), whose
conclusion lives over an open `V` of the *subspace* `X|_{U₀}` and in the slice idiom. The open `U₁`
of `X` corresponding to `V` and the reindexing
`AlgebraicGeometry.RingedSpace.restrictOverHom` bring it back, and
`AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso` identifies the doubly restricted complex
with `𝒦|_{U₁}`.

## Main results

* `CategoryTheory.ShortComplex.toCycles_comp_mapCyclesIso_hom`: the comparison
  `(F S).cycles ≅ F (S.cycles)` for a functor preserving left homology is compatible with
  `toCycles`.
* `CategoryTheory.ShortComplex.epi_comp_homologyπ_map` and
  `CategoryTheory.epi_comp_homologyπ_mapHomologicalComplex`: for an exact functor `F`, a map into
  `Z^p(F 𝒦)` is epimorphic onto `H^p(F 𝒦)` as soon as the corresponding map into `F(Z^p 𝒦)` is
  epimorphic onto `F(H^p 𝒦)`. This is the `homologyπ` square for an exact functor, in the only
  form needed.
* `AlgebraicGeometry.RingedSpace.exists_local_epi_comp_homologyπ_of_isFiniteType_homology`: the
  local lift itself.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_isFiniteType_homology`: a complex
  with no cohomology above `p` whose `p`-th cohomology sheaf is of finite type is
  `p`-pseudo-coherent.

## Implementation notes

Mathlib has `CategoryTheory.ShortComplex.mapHomologyIso`, but no compatibility between it and
`homologyπ`, and its two defining equations
(`CategoryTheory.ShortComplex.LeftHomologyData.mapHomologyIso_eq` and its `cycles` companion) are
proved under `backward.isDefEq.respectTransparency false`, so rewriting by them produces a goal
that is not type-correct at `implicit` transparency. The square is therefore obtained here from
the universal property instead: `H^p(F 𝒦)` and `F(H^p 𝒦)` are both cokernels of
`Z^{p-1}(𝒦) ⟶ Z^p(𝒦)` transported along the cycles comparison — the second because `F` preserves
finite colimits — and the comparison of the two cokernels is an isomorphism *whose defining
equation is the square*. No second `H^p(F 𝒦) ≅ F(H^p 𝒦)` is introduced: the isomorphism stays
inside the proof.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 20.46.3 (Tag 08C6)](https://stacks.math.columbia.edu/tag/08C6)
* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u} [Category.{v} D] [Abelian D]

/-- **The comparison `(F S).cycles ≅ F (S.cycles)` is compatible with `toCycles`.** Both sides
become `F S.f` after composing with the monomorphism `(F S).iCycles`. -/
public theorem toCycles_comp_mapCyclesIso_hom (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S] :
    (S.map F).toCycles ≫ (S.mapCyclesIso F).hom = F.map S.toCycles := by
  rw [← Iso.eq_comp_inv, ← cancel_mono ((S.map F).iCycles), ShortComplex.toCycles_i,
    Category.assoc, ← ShortComplex.mapCyclesIso_hom_iCycles, Iso.inv_hom_id_assoc, ← F.map_comp,
    ShortComplex.toCycles_i, ShortComplex.map_f]

/-- **The `homologyπ` square of an exact functor, in the form a lifting argument needs.** Let `F`
be an exact functor and `S` a short complex. A map `c` into the cycles of `F S` is epimorphic onto
the homology of `F S` as soon as the corresponding map into `F (S.cycles)` is epimorphic onto
`F (S.homology)`.

The homology of `F S` is the cokernel of `(F S).toCycles`, and `F (S.homology)` is the cokernel of
`F (S.toCycles)` because `F` preserves finite colimits; the cycles comparison identifies the two
sources, so the induced map `H(F S) ⟶ F(H S)` is an isomorphism and its defining equation
`(F S).homologyπ ≫ _ = (S.mapCyclesIso F).hom ≫ F (S.homologyπ)` is the square. -/
public theorem epi_comp_homologyπ_map (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {A : D} (c : A ⟶ (S.map F).cycles)
    (h : Epi (c ≫ (S.mapCyclesIso F).hom ≫ F.map S.homologyπ)) :
    Epi (c ≫ (S.map F).homologyπ) := by
  have hw : (S.map F).toCycles ≫ (S.mapCyclesIso F).hom ≫ F.map S.homologyπ = 0 := by
    rw [← Category.assoc, toCycles_comp_mapCyclesIso_hom S F, ← F.map_comp,
      ShortComplex.toCycles_comp_homologyπ, F.map_zero]
  have hcB := CokernelCofork.mapIsColimit _ S.homologyIsCokernel F
  have hχ : F.map S.toCycles ≫ (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ = 0 := by
    rw [← toCycles_comp_mapCyclesIso_hom S F, Category.assoc, Iso.hom_inv_id_assoc,
      ShortComplex.toCycles_comp_homologyπ]
  obtain ⟨ψ', hψ'⟩ := CokernelCofork.IsColimit.desc' hcB
    ((S.mapCyclesIso F).inv ≫ (S.map F).homologyπ) hχ
  simp only [CokernelCofork.map_π, Cofork.π_ofπ] at hψ'
  set ψ := (S.map F).descHomology ((S.mapCyclesIso F).hom ≫ F.map S.homologyπ) hw with hψ
  have hsq : (S.map F).homologyπ ≫ ψ = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ :=
    ShortComplex.π_descHomology _ _ _
  have h1 : ψ ≫ ψ' = 𝟙 _ := by
    refine Cofork.IsColimit.hom_ext (S.map F).homologyIsCokernel ?_
    simp only [Cofork.π_ofπ]
    rw [← Category.assoc, hsq, Category.assoc, hψ', Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  have h2 : ψ' ≫ ψ = 𝟙 _ := by
    refine Cofork.IsColimit.hom_ext hcB ?_
    simp only [CokernelCofork.map_π, Cofork.π_ofπ]
    rw [← Category.assoc, hψ', Category.assoc, hsq, Iso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm
  have : IsIso ψ := ⟨ψ', h1, h2⟩
  refine (epi_comp_iff_of_isIso _ ψ).1 ?_
  rw [Category.assoc, hsq]
  exact h

end CategoryTheory.ShortComplex

namespace CategoryTheory

/-- **Being an epimorphism transports along an equality of morphisms.** Used here rather than
`rw`: the morphisms compared below are composites in which the cycles of a complex appear both as
`HomologicalComplex.cycles` and as the cycles of the degree-`p` short complex, two spellings that
are definitionally but not syntactically equal, so a rewrite cannot abstract them. -/
public theorem epi_of_eq {C : Type u} [Category.{v} C] {A B : C} {f g : A ⟶ B} (hfg : f = g)
    (hg : Epi g) : Epi f := by cases hfg; exact hg

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u} [Category.{v} D] [Abelian D]

/-- `CategoryTheory.ShortComplex.epi_comp_homologyπ_map` for the degreewise image of a cochain
complex under an exact functor. -/
public theorem epi_comp_homologyπ_mapHomologicalComplex (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : CochainComplex C ℤ) (p : ℤ)
    {A : D} (c : A ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).cycles p)
    (h : Epi (c ≫ ((M.sc p).mapCyclesIso F).hom ≫ F.map (M.homologyπ p))) :
    Epi (c ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).homologyπ p) :=
  ShortComplex.epi_comp_homologyπ_map (M.sc p) F c h

/-- **An epimorphism onto `F(H^p 𝒦)` through `F(Z^p 𝒦)` becomes, along any identification of the
degreewise image of `𝒦` with a complex `ℒ`, an epimorphism onto `H^p(ℒ)` through `Z^p(ℒ)`.**

This is the form in which the converse half of Stacks 09VA consumes
`CategoryTheory.epi_comp_homologyπ_mapHomologicalComplex`: the exact functor is restriction to a
smaller open subspace, and the identification is
`AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso`. It is stated separately, with every
complex behind a variable, because matching a written-out instance of its conclusion against the
restriction functors it is applied to is expensive. -/
public theorem exists_epi_comp_homologyπ_of_iso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : CochainComplex C ℤ)
    (L : CochainComplex D ℤ)
    (θ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅ L) (p : ℤ) {A : D}
    (c : A ⟶ F.obj (M.cycles p)) (h : Epi (c ≫ F.map (M.homologyπ p))) :
    ∃ c' : A ⟶ L.cycles p, Epi (c' ≫ L.homologyπ p) := by
  have heq := (Category.assoc c ((M.sc p).mapCyclesIso F).inv
      (((M.sc p).mapCyclesIso F).hom ≫ F.map (M.homologyπ p))).trans
    (congrArg (fun g => c ≫ g)
      (Iso.inv_hom_id_assoc ((M.sc p).mapCyclesIso F) (F.map (M.homologyπ p))))
  have hA := epi_comp_homologyπ_mapHomologicalComplex F M p
    (c ≫ ((M.sc p).mapCyclesIso F).inv) (epi_of_eq heq h)
  refine ⟨(c ≫ ((M.sc p).mapCyclesIso F).inv) ≫ HomologicalComplex.cyclesMap θ.hom p,
    epi_of_eq ?_
      (@epi_comp _ _ _ _ _ _ hA (HomologicalComplex.homologyMap θ.hom p) inferInstance)⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => (c ≫ ((M.sc p).mapCyclesIso F).inv) ≫ g)
      (HomologicalComplex.homologyπ_naturality θ.hom p).symm).trans
        (Category.assoc _ _ _).symm)

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- **A local epimorphism onto `H^p(𝒦)` lifts to the cycles.** Let `𝒦` be a complex of
`𝒪_X`-modules whose `p`-th cohomology sheaf is of finite type. Then every point of `X` has an open
neighbourhood `U` carrying a direct summand `𝒜` of a finite free module and a map
`𝒜 ⟶ Z^p(𝒦|_U)` whose composite with `Z^p(𝒦|_U) ⟶ H^p(𝒦|_U)` is an epimorphism.

Finite type gives an epimorphism `𝒪_{X|U₀}^{⊕n} ⟶ H^p(𝒦)|_{U₀}` on some open `U₀`, which
`AlgebraicGeometry.RingedSpace.restrictComplexHomologyIso` reads as an epimorphism onto
`H^p(𝒦|_{U₀})`. Stacks 08C6 over an open subset lifts it through the epimorphism
`Z^p(𝒦|_{U₀}) ⟶ H^p(𝒦|_{U₀})` over an open `V` of the subspace `X|_{U₀}`;
`AlgebraicGeometry.RingedSpace.restrictOverHom` carries the lift to the open `U₁` of `X`
corresponding to `V`, where `CategoryTheory.epi_comp_homologyπ_mapHomologicalComplex` and
`AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso` put it in the asked-for form. -/
public theorem exists_local_epi_comp_homologyπ_of_isFiniteType_homology
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (p : ℤ)
    (hft : SheafOfModules.IsFiniteType (R := structureSheafOfRings X) (K.homology p))
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ A : OXMod.{u, u} (X.restrict U.isOpenEmbedding), IsDirectSummandOfFiniteFree A ∧
        ∃ c : A ⟶ (restrictComplex K U).cycles p,
          Epi (c ≫ (restrictComplex K U).homologyπ p) := by
  obtain ⟨U₀, hxU₀, n, q, hq⟩ := exists_epi_finiteFree_of_isFiniteType (K.homology p) hft x
  set M := restrictComplex K U₀ with hM
  set γ : finiteFree (X.restrict U₀.isOpenEmbedding) n ⟶ M.homology p :=
    q ≫ (restrictComplexHomologyIso K U₀ p).inv with hγ
  have hγepi : Epi γ := by rw [hγ]; exact epi_comp _ _
  have hπ : Epi (M.homologyπ p) := inferInstanceAs (Epi ((M.sc p).homologyπ))
  obtain ⟨V, hVtop, hxV, l, hl⟩ := exists_local_lift_over_of_isDirectSummandOfFiniteFree
    (E := finiteFree (X.restrict U₀.isOpenEmbedding) n) (M.homologyπ p) ⟨n, ⟨Retract.refl _⟩⟩ ⊤
    ((SheafOfModules.overFunctor
      (structureSheafOfRings (X.restrict U₀.isOpenEmbedding)) ⊤).map γ)
    (Set.mem_univ (⟨x, hxU₀⟩ : (X.restrict U₀.isOpenEmbedding).carrier))
  rw [SheafOfModules.overRestrict_map] at hl
  -- the open of `X` corresponding to `V`, and its two containments
  have hU₁U₀ : (U₀.overEquivalence.inverse.obj V).left ≤ U₀ :=
    leOfHom (U₀.overEquivalence.inverse.obj V).hom
  have hxU₁ : x ∈ (U₀.overEquivalence.inverse.obj V).left := ⟨⟨x, hxU₀⟩, hxV, rfl⟩
  have hU₁V : ∀ y : U₀, y.1 ∈ (U₀.overEquivalence.inverse.obj V).left → y ∈ V := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := hy
    obtain rfl : w = y := Subtype.ext hyw
    exact hw
  set G := restrictModulesOfLE X hU₁U₀ with hG
  -- the reindexed lift, and the epimorphy of its composite with `G (H^p 𝒦|_{U₀})`
  set c₀ := restrictOverHom hU₁U₀ V hU₁V l with hc₀
  have hc₀epi : Epi (c₀ ≫ G.map (M.homologyπ p)) := by
    rw [hc₀, ← restrictOverHom_map hU₁U₀ V hU₁V (M.homologyπ p), ← restrictOverHom_comp, hl,
      restrictOverHom_map]
    have hpe : G.PreservesEpimorphisms := inferInstance
    exact @CategoryTheory.Functor.PreservesEpimorphisms.preserves _ _ _ _ _ hpe _ _ γ hγepi
  -- put it in the asked-for form
  exact ⟨_, hxU₁, G.obj (finiteFree (X.restrict U₀.isOpenEmbedding) n),
    isDirectSummandOfFiniteFree_restrictModulesOfLE hU₁U₀ ⟨n, ⟨Retract.refl _⟩⟩,
    CategoryTheory.exists_epi_comp_homologyπ_of_iso G M _
      (restrictComplexOfLEIso X hU₁U₀ K) p c₀ hc₀epi⟩

/-- **A complex with no cohomology above `p` whose `p`-th cohomology sheaf is of finite type is
`p`-pseudo-coherent.** This is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_local_epi_homologyπ` fed with
`AlgebraicGeometry.RingedSpace.exists_local_epi_comp_homologyπ_of_isFiniteType_homology`, and it is
the base case `p = m` of the induction of the converse half of Stacks 09VA. -/
public theorem isPseudoCoherentComplexFrom_of_isFiniteType_homology
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (p : ℤ)
    (hvanish : ∀ j : ℤ, p < j → IsZero (K.homology j))
    (hft : SheafOfModules.IsFiniteType (R := structureSheafOfRings X) (K.homology p)) :
    IsPseudoCoherentComplexFrom K p :=
  isPseudoCoherentComplexFrom_of_local_epi_homologyπ K p hvanish
    (exists_local_epi_comp_homologyπ_of_isFiniteType_homology K p hft)

end AlgebraicGeometry.RingedSpace

end
