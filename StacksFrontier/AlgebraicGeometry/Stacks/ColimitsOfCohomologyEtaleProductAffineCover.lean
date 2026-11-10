module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyProductAffineCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Condition (2)(c) of Stacks 0GMS for the étale site of an algebraic stack

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, and give its
total category the *étale* topology of **Stacks 06TP**. Condition (2)(c) of **Stacks 0GMS** —
equivalently condition (3) of **Stacks 0GN4** — asks, for two objects `x`, `x'` of that site
lying over affine schemes, for a finite family `V_i` of such objects with morphisms
`p_i : V_i ⟶ x` and `q_i : V_i ⟶ x'` for which `∐_i h_{V_i}^# ⟶ h_x^# ⨯ h_{x'}^#` is a surjection
of *étale* sheaves of sets. This file proves that condition, with one member, for a stack which is
quasi-separated over a quasi-separated base scheme.

**The geometry is the same geometry the fppf case uses, and no new geometric input is needed.**
The source produces the family by covering the 2-fibre product `U ×_{x, 𝒳, x'} U'` of the slices
`x` and `x'` represent by an affine scheme: **Stacks 075S** part (3) makes that 2-fibre product
quasi-compact, and **Stacks 04YC** attaches to a quasi-compact algebraic stack an affine object
`U₀` together with a *surjective smooth* 1-morphism from the category `U₀` represents. The only
step that reads the chosen topology is the last one, where the sections of that presentation are
read off a covering of the base: for the fppf topology that is **Stacks 06QA**, which asks the
1-morphism to be surjective, flat and locally of finite presentation, and for the étale topology
it is **Stacks 06XH** part (2), `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which
asks it to be surjective and *smooth* — exactly what Stacks 04YC supplies. So the étale case asks
nothing of the presentation that the fppf case does not, and in particular no affine *étale*
presentation of a quasi-compact algebraic stack is required.

Accordingly everything here is proved once, at an arbitrary topology `τ` on the underlying
category of schemes of `B`, with the fibre-lifting property of a surjective smooth 1-morphism as a
hypothesis, exactly as condition (1) is in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyAtlasCovers.lean`; the étale statement
is its value at `AlgebraicGeometry.etaleTopology`, with Stacks 06XH part (2) discharging that
hypothesis.

## Main results

* `AlgebraicGeometry.Stack`
  `.isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating`: condition
  (2)(c) at an arbitrary topology of Stacks 06TP, from one quadruple of Stacks 0040 dominating
  every quadruple locally.
* `AlgebraicGeometry.Stack`
  `.isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating_base`: the same
  with the covering taken in the big fppf category over `S`, which is the shape the fibre-lifting
  tags produce.
* `AlgebraicGeometry.Stack.exists_quadruple_dominating_associatedTopology`: the dominating
  quadruple itself, for a quasi-compact 2-fibre product of two 2-Yoneda 1-morphisms, at any
  topology in which a surjective smooth 1-morphism admits fibre lifts.
* `AlgebraicGeometry.Stack`
  `.exists_fin_affineObjects_isLocallySurjective_prodLift_associatedTopology`: condition (2)(c)
  itself at such a topology.
* `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_etale`:
  **condition (2)(c) for the étale site**, in the shape
  `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale` consumes as its
  hypothesis `h_product`.
* `AlgebraicGeometry.Stack`
  `.isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiSeparatedOver`: the second
  assertion of Stacks 0GQV for a quasi-compact algebraic stack quasi-separated over a
  quasi-separated base, with condition (4) of Stacks 0GN4 still assumed.

## Implementation notes

The three steps of the fppf argument are reproduced over an arbitrary `τ`, each of them verbatim
apart from the topology:

* the dictionary between pairs of morphisms of the site and the quadruples of **Stacks 0040** is
  absolute — `AlgebraicGeometry.Stack.exists_quadruple_of_hom_pair`,
  `AlgebraicGeometry.Stack.quadMap_comp_quadFst` and `.quadMap_comp_quadSnd` mention no topology
  at all — so passing from a locally dominating quadruple to local surjectivity needs only that
  a Grothendieck topology is stable under pullback;
* the passage from a covering sieve of the base to a covering family upstairs is
  `CategoryTheory.Functor.inheritedTopology` and nothing else: every morphism of a category
  fibred in groupoids is strongly cartesian over its image, and the images of the lifts generate
  the given sieve downstairs, so the lifts generate a covering sieve of the inherited topology
  `AlgebraicGeometry.Stack.associatedTopology` at `τ` for the same reason as at the fppf
  topology;
* the dominating quadruple is `f(1_{U₀})` for `f` the affine smooth presentation of
  **Stacks 04YC**, and the only use of the topology is the fibre-lifting hypothesis applied to
  `f`.

Quasi-compactness of the 2-fibre product, and quasi-separatedness over `S` of it, are taken from
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyProductAffineCover.lean`
(`AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism`),
as are the two bookkeeping lemmas `AlgebraicGeometry.Stack.obj_quadObj` and
`AlgebraicGeometry.Stack.isHomLift_quadMap`: none of the three mentions a topology, so the étale
case reuses them unchanged. The fppf statements of that file are the values of the statements here
at `AlgebraicGeometry.BigFppfSite.topology`, with **Stacks 06QA** discharging the fibre-lifting
hypothesis, and could be re-derived from them.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] essentiallySmall_join hasSheafify_ab_join enoughInjectives_sheaf_join
  globalSections_additive_join

universe v₀ u₀

/-- Sheaves of sets on a site have colimits of the size of the join of the two universes of the
site. The instance is needed to form the finite coproducts of sheafified representables the
conditions of Stacks 0GN4 speak of, and is restated in its constructed form, as in the files
proving Stacks 0GN3 and Stacks 0GN4 and in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomology.lean`, because the search that finds
it is not cheap. It is anonymous because those files export a declaration of the same name whose
`instance` attribute is local to them. -/
local instance {C : Type u₀} [Category.{v₀} C] (J : GrothendieckTopology C) :
    HasColimitsOfSize.{max u₀ v₀, max u₀ v₀} (Sheaf J (Type max u₀ v₀)) :=
  Sheaf.instHasColimitsOfSize

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Dictionary

variable (𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (τ : GrothendieckTopology B.Schemes)

variable {x x' : 𝒞.val.obj}

-- As in `StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyProductDictionary.lean`:
-- `Functor.Fiber` is a plain `def` and `Bicategory.InducedBicategory` is semireducible, so
-- without these `rw` declines to abstract over the subterms of the goals below.
attribute [local implicit_reducible] Functor.Fiber Bicategory.InducedBicategory

/-- **Condition (2)(c) of Stacks 0GMS at an arbitrary topology of Stacks 06TP, from one quadruple
which dominates every quadruple locally.** Let `x`, `x'` be objects of the site of `𝒞` at a
topology `τ` and let `Q` be an object of the 2-fibre product `U ×_{x, 𝒞, x'} U'` of the slices
they represent. Suppose every object `P` of that 2-fibre product carries a covering sieve of the
object of the site it classifies over whose members `P` is dominated by an object admitting a
morphism to `Q`. Then `∐ h_V^# ⟶ h_x^# ⨯ h_{x'}^#` is a surjection of sheaves of sets, for the
one-member family `V = ` the object `Q` classifies with its two classified morphisms.

This is
`AlgebraicGeometry.Stack.isLocallySurjective_prodLift_fppfTopology_of_exists_quadruple_dominating`
with the fppf topology replaced by the topology inherited from `τ`. Nothing of the fppf topology
was used: the dictionary between quadruples and pairs of morphisms of the site is absolute
(`AlgebraicGeometry.Stack.exists_quadruple_of_hom_pair`,
`AlgebraicGeometry.Stack.quadMap_comp_quadFst` and `.quadMap_comp_quadSnd`), and the covering
sieve the hypothesis attaches to `P` is transported to one of `y` by stability of a Grothendieck
topology under pullback. -/
theorem isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating
    (Q : twoFibreProductObjects B S hS 𝒞 x x')
    (h : ∀ P : twoFibreProductObjects B S hS 𝒞 x x',
      ∃ T ∈ associatedTopology B S hS 𝒞.val.p τ (quadObj B S hS 𝒞 P),
        ∀ ⦃z : 𝒞.val.obj⦄ (g : z ⟶ quadObj B S hS 𝒞 P), T.arrows g →
          ∃ (P' : twoFibreProductObjects B S hS 𝒞 x x') (ψ : P' ⟶ P) (_ : P' ⟶ Q)
            (c : z ⟶ quadObj B S hS 𝒞 P'), c ≫ quadMap B S hS 𝒞 ψ = g) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc fun _ : Fin 1 =>
      prod.lift
        ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒞.val.p τ)).map
          (quadFst B S hS 𝒞 Q))
        ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒞.val.p τ)).map
          (quadSnd B S hS 𝒞 Q))) := by
  refine Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering
    (fun _ : Fin 1 => quadObj B S hS 𝒞 Q) (fun _ => quadFst B S hS 𝒞 Q)
    (fun _ => quadSnd B S hS 𝒞 Q) fun y α β => ?_
  obtain ⟨P, e, -, hα, hβ⟩ := exists_quadruple_of_hom_pair B S hS 𝒞 y α β
  obtain ⟨T, hT, hlift⟩ := h P
  refine ⟨Sieve.pullback e.hom T,
    (associatedTopology B S hS 𝒞.val.p τ).pullback_stable e.hom hT, fun z g hg => ?_⟩
  obtain ⟨P', ψ, χ, c, hc⟩ := hlift (g ≫ e.hom) hg
  refine ⟨0, c ≫ quadMap B S hS 𝒞 χ, ?_, ?_⟩
  · rw [Category.assoc, quadMap_comp_quadFst, ← hα, ← Category.assoc, ← hc, Category.assoc,
      quadMap_comp_quadFst]
  · rw [Category.assoc, quadMap_comp_quadSnd, ← hβ, ← Category.assoc, ← hc, Category.assoc,
      quadMap_comp_quadSnd]

/-- **Condition (2)(c) of Stacks 0GMS at an arbitrary topology of Stacks 06TP, with the covering
taken downstairs.** The hypothesis of
`AlgebraicGeometry.Stack`
`.isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating` with the
covering requirement moved to the big fppf category over `S`, localized at the chosen topology
`τ`: for every object `P` of the 2-fibre product it is enough to have a covering sieve `R` of the
*scheme* the object `P` classifies lies over, together with, over each member `k` of `R`, an
object `P'` admitting a morphism to `Q` and a morphism `P' ⟶ P` whose induced morphism of the
site lies over `k`.

This is the shape **Stacks 06QA** produces at the fppf topology and **Stacks 06XH** part (2) at
the étale topology, so it is the form in which an affine smooth presentation of the 2-fibre
product discharges condition (2)(c) in either.

The family of induced morphisms of the site is a covering family of the object `P` classifies:
every morphism of a category fibred in groupoids is strongly cartesian over its image, and the
images of the members generate `R`, each one agreeing with its member after the comparison
isomorphism of `CategoryTheory.Functor.IsHomLift.domain_eq`. The topology of Stacks 06TP is the
topology inherited from the localization of `τ` at `S`, so that covering family generates a
covering sieve of the site with no transport. -/
theorem isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating_base
    (Q : twoFibreProductObjects B S hS 𝒞 x x')
    (h : ∀ P : twoFibreProductObjects B S hS 𝒞 x x',
      ∃ R ∈ τ.over (B.obj hS) (𝒞.val.p.obj (quadObj B S hS 𝒞 P)),
        ∀ ⦃T : BigFppfOver B S hS⦄ ⦃k : T ⟶ 𝒞.val.p.obj (quadObj B S hS 𝒞 P)⦄, R.arrows k →
          ∃ (P' : twoFibreProductObjects B S hS 𝒞 x x') (ψ : P' ⟶ P) (_ : P' ⟶ Q),
            𝒞.val.p.IsHomLift k (quadMap B S hS 𝒞 ψ)) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc fun _ : Fin 1 =>
      prod.lift
        ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒞.val.p τ)).map
          (quadFst B S hS 𝒞 Q))
        ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒞.val.p τ)).map
          (quadSnd B S hS 𝒞 Q))) := by
  classical
  refine isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating
    B S hS 𝒞 τ Q fun P => ?_
  obtain ⟨R, hR, hlift⟩ := h P
  have hch : ∀ i : Σ T : BigFppfOver B S hS,
      {k : T ⟶ 𝒞.val.p.obj (quadObj B S hS 𝒞 P) // R.arrows k},
      ∃ (P' : twoFibreProductObjects B S hS 𝒞 x x') (ψ : P' ⟶ P) (_ : P' ⟶ Q),
        𝒞.val.p.IsHomLift i.2.1 (quadMap B S hS 𝒞 ψ) := fun i => hlift i.2.2
  choose P' ψ χ hψ using hch
  refine ⟨Sieve.ofArrows (fun i => quadObj B S hS 𝒞 (P' i))
    (fun i => quadMap B S hS 𝒞 (ψ i)), ?_, ?_⟩
  · rw [associatedTopology, Functor.inheritedTopology_eq]
    refine Precoverage.generate_mem_toGrothendieck
      ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
        𝒞.isFiberedInGroupoids q, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
    refine (τ.over (B.obj hS)).superset_covering ?_ hR
    intro T k hk
    let i : Σ T' : BigFppfOver B S hS,
        {k' : T' ⟶ 𝒞.val.p.obj (quadObj B S hS 𝒞 P) // R.arrows k'} := ⟨T, k, hk⟩
    have hinst := hψ i
    have hdom : 𝒞.val.p.obj (quadObj B S hS 𝒞 (P' i)) = T :=
      IsHomLift.domain_eq 𝒞.val.p k (quadMap B S hS 𝒞 (ψ i))
    have hfac : 𝒞.val.p.map (quadMap B S hS 𝒞 (ψ i)) = eqToHom hdom ≫ k := by
      simpa using IsHomLift.fac' 𝒞.val.p k (quadMap B S hS 𝒞 (ψ i))
    refine ⟨𝒞.val.p.obj (quadObj B S hS 𝒞 (P' i)), eqToHom hdom.symm,
      𝒞.val.p.map (quadMap B S hS 𝒞 (ψ i)), Presieve.ofArrows.mk i, ?_⟩
    rw [hfac, eqToHom_trans_assoc]
    simp
  · intro z g hg
    obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ g).1 hg
    exact ⟨P' i, ψ i, χ i, c, hc.symm⟩

end Dictionary

section AffineQuadruple

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) (τ : GrothendieckTopology B.Schemes)
variable {y y' : 𝒳.val.val.obj}

/-- **A quasi-compact 2-fibre product of two 2-Yoneda 1-morphisms has a quadruple over an affine
scheme which dominates every quadruple after a covering taken downstairs, in any topology in
which a surjective smooth 1-morphism admits fibre lifts.**

This is
`AlgebraicGeometry.Stack.exists_quadruple_dominating` with the fibre-lifting property of a
surjective smooth 1-morphism made a hypothesis instead of being discharged by **Stacks 06QA**;
the fppf statement is its value at `AlgebraicGeometry.BigFppfSite.topology` and the étale one its
value at `AlgebraicGeometry.etaleTopology`, where **Stacks 06XH** part (2) discharges it.

**Stacks 04YC** parts (1) and (2) turn quasi-compactness into an affine object `U₀` and a
surjective, relatively smooth 1-morphism `f` from the slice `(Sch/S)/U₀` onto the 2-fibre product;
the quadruple is `Q = f(1_{U₀})`, which lies over `U₀` because `f` is a based functor. Relative
smoothness is upgraded to smoothness in the sense of **Stacks 075U** by
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty`, and the
hypothesis then covers the base object of any quadruple `P` by objects over each of which `P`
receives a morphism from `f(a)` for an object `a` of the slice; `f(a)` is the dominating quadruple
over that member of the covering, and its morphism to `Q` is the image under `f` of the structure
morphism `a ⟶ 1_{U₀}`.

Note that no flatness or local finite presentation of `f` is asked for here: those are what the
fppf fibre-lifting tag needs of it, not what the construction of `Q` needs. -/
theorem exists_quadruple_dominating_associatedTopology
    (hqc : IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
        (objectMorphismAlgebraicStacks B S hS 𝒳 y')).val
      (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
        (objectMorphismAlgebraicStacks B S hS 𝒳 y')).property)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (a : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj a ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∃ Q : twoFibreProductObjects B S hS 𝒳.val y y',
      IsAffineObject B S hS 𝒳.val.val.p (quadObj B S hS 𝒳.val Q) ∧
        ∀ P : twoFibreProductObjects B S hS 𝒳.val y y',
          ∃ R ∈ τ.over (B.obj hS) (𝒳.val.val.p.obj (quadObj B S hS 𝒳.val P)),
            ∀ ⦃T : BigFppfOver B S hS⦄
              ⦃k : T ⟶ 𝒳.val.val.p.obj (quadObj B S hS 𝒳.val P)⦄, R.arrows k →
              ∃ (P' : twoFibreProductObjects B S hS 𝒳.val y y') (ψ : P' ⟶ P) (_ : P' ⟶ Q),
                𝒳.val.val.p.IsHomLift k (quadMap B S hS 𝒳.val ψ) := by
  classical
  set 𝒬 := twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
    (objectMorphismAlgebraicStacks B S hS 𝒳 y')
  obtain ⟨U₀, hU₀, f, hsurj, hfrep, hrel⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒬).1 hqc
  have hsm : AlgebraicStacks.IsSmooth B S hS f :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) 𝒬.property f.hom hfrep hrel
  set F := CatFiberedInGroupoids.homFunctor f.hom
  have hw : F ⋙ 𝒬.val.val.p = (schemeFibredCategory B S hS U₀).val.p := f.hom.hom.w
  -- The dominating quadruple is the image of the terminal object of the slice over `U₀`.
  refine ⟨F.obj (Over.mk (𝟙 U₀)), ?_, ?_⟩
  · have hproj : 𝒳.val.val.p.obj (quadObj B S hS 𝒳.val (F.obj (Over.mk (𝟙 U₀)))) = U₀ :=
      (obj_quadObj B S hS 𝒳.val (F.obj (Over.mk (𝟙 U₀)))).trans
        (Functor.congr_obj hw (Over.mk (𝟙 U₀)))
    change IsAffine ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj (quadObj B S hS 𝒳.val (F.obj (Over.mk (𝟙 U₀))))))
    rw [hproj]
    exact hU₀
  · intro P
    obtain ⟨R, hR, hlift⟩ := h_lift _ 𝒬 f hsurj hsm
      (𝒳.val.val.p.obj (quadObj B S hS 𝒳.val P))
      (Functor.Fiber.mk (a := P) (obj_quadObj B S hS 𝒳.val P).symm)
    refine ⟨R, hR, fun T k hk => ?_⟩
    obtain ⟨a, φ, hφ⟩ := hlift hk
    exact ⟨F.obj a, φ, F.map (Over.homMk a.hom (Category.comp_id a.hom)),
      isHomLift_quadMap B S hS 𝒳.val φ k hφ⟩

/-- **Condition (2)(c) of Stacks 0GMS at an arbitrary topology of Stacks 06TP in which a
surjective smooth 1-morphism admits fibre lifts**, for an algebraic stack quasi-separated over a
quasi-separated base scheme: for two objects `x`, `x'` of the site lying over affine schemes there
is a finite family of such objects, with a morphism to `x` and a morphism to `x'` from each, whose
sheafified representables jointly cover `h_x^# ⨯ h_{x'}^#`.

The family has one member, as in the source. It is the object the quadruple of
`AlgebraicGeometry.Stack.exists_quadruple_dominating_associatedTopology` classifies, with the two
morphisms that quadruple classifies, and the covering assertion is
`AlgebraicGeometry.Stack`
`.isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating_base`.
Quasi-compactness of the 2-fibre product, which is what produces the quadruple, is
`AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism`, and is
where quasi-separatedness enters, through **Stacks 075S** part (3). -/
theorem exists_fin_affineObjects_isLocallySurjective_prodLift_associatedTopology
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (a : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj a ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∀ U ∈ affineObjects B S hS 𝒳.val, ∀ U' ∈ affineObjects B S hS 𝒳.val,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
            Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
              prod.lift
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p τ)).map (p i))
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p τ)).map (q i))) := by
  intro U hU U' hU'
  obtain ⟨Q, hQaff, hQ⟩ := exists_quadruple_dominating_associatedTopology B S hS 𝒳 τ
    (isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism B S hS 𝒳 hqsS h𝒳 hU hU')
    h_lift
  exact ⟨1, fun _ => quadObj B S hS 𝒳.val Q, fun _ => hQaff,
    fun _ => quadFst B S hS 𝒳.val Q, fun _ => quadSnd B S hS 𝒳.val Q,
    isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating_base
      B S hS 𝒳.val τ Q hQ⟩

/-- **Condition (2)(c) of Stacks 0GMS for the étale site of an algebraic stack quasi-separated
over a quasi-separated base scheme**, in the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale` consumes as its
hypothesis `h_product`: for two objects `x`, `x'` of the étale site lying over affine schemes
there is a finite family of such objects, with a morphism to `x` and a morphism to `x'` from each,
whose sheafified representables jointly cover `h_x^# ⨯ h_{x'}^#`.

This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_prodLift_associatedTopology` at the big étale
topology, its fibre-lifting hypothesis discharged by **Stacks 06XH** part (2),
`AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which reads the fibre lifts of a
surjective smooth 1-morphism off an *étale* covering of the base. The affine smooth presentation
of **Stacks 04YC** is smooth and surjective, which is exactly what that tag asks for, so the
étale case needs nothing of the presentation beyond what the fppf case needs — in particular no
affine étale presentation of a quasi-compact algebraic stack. The family has one member, as in the
source. -/
@[stacks 0GMS "condition (2)(c) for the étale site of an algebraic stack quasi-separated over a \
quasi-separated base scheme, with the collection B of Stacks 0GQV: the objects of the site lying \
over affine schemes; the family produced has one member, as in the source"]
theorem exists_fin_affineObjects_isLocallySurjective_prodLift_etale
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳) :
    ∀ U ∈ affineObjects B S hS 𝒳.val, ∀ U' ∈ affineObjects B S hS 𝒳.val,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
            Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
              prod.lift
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (p i))
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (q i))) :=
  exists_fin_affineObjects_isLocallySurjective_prodLift_associatedTopology B S hS 𝒳
    (etaleTopology B) hqsS h𝒳
    fun _ _ f hsurj hsm => exists_etaleCovering_fibre_lift B S hS f hsurj hsm

/-- **The second assertion of Stacks 0GQV, in the étale topology, for a quasi-compact algebraic
stack which is quasi-separated over a quasi-separated base scheme, from condition (4) of
Stacks 0GN4 alone.**

This is `AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompactStack`
with its condition (3) discharged by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_etale`. Condition
(4), the corresponding assertion for the equalizer of two parallel morphisms, is still assumed:
the 2-fibre product the source covers by an affine scheme in that case is the one of a single
1-morphism against the diagonal, not of two 2-Yoneda 1-morphisms, so the quadruple of this file
does not discharge it, in this topology any more than in the fppf one. So this is not yet the full
second assertion of Stacks 0GQV. -/
@[stacks 0GQV "the second assertion, in the étale topology, for a quasi-compact algebraic stack \
quasi-separated over a quasi-separated base; conditions (1), (2) and (3) of 0GN4 are now proved \
for the étale site, condition (4) is still assumed"]
theorem isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiSeparatedOver
    (hqsS : QuasiSeparatedSpace S)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (h_equalizer : ∀ {U U' : 𝒳.val.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳.val → U' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map a)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map b)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompactStack.{u, w} B S hS 𝒳 hqc
    (exists_fin_affineObjects_isLocallySurjective_prodLift_etale B S hS 𝒳 hqsS h𝒳)
    h_equalizer p F

end AffineQuadruple

end AlgebraicGeometry.Stack

end
