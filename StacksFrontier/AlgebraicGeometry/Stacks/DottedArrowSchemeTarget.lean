module

public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.SchemeTwoCells
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuativeSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionDottedGroupoid

/-!
# Dotted arrows of valuative squares into a represented stack

Let `f : 𝒳 ⟶ 𝒯` be a 1-morphism of algebraic stacks over `S` whose target is the algebraic stack
of an object `V` of the big fppf site, for instance the structure morphism `𝒳 ⟶ S`. Two
1-morphisms into `𝒯` have at most one 2-morphism between them, so the second compatibility
condition of a morphism of dotted arrows (Stacks 0H18) is automatic. Consequently the category of
dotted arrows of a valuative square `q` for `f` is controlled by restriction of 2-morphisms along
the left edge `j : Spec K ⟶ Spec R` of the square:

* it is a setoid as soon as a 2-endomorphism of a 1-morphism `Spec R ⟶ 𝒳` which restricts to the
  identity along `j` is the identity;
* any two of its objects are isomorphic as soon as every 2-morphism between the restrictions along
  `j` of two 1-morphisms `Spec R ⟶ 𝒳`, the first of which restricts to the generic point of the
  square, is the restriction of a 2-morphism.

By the 2-Yoneda lemma both conditions are conditions on the fibres of `𝒳` over `Spec R` and
`Spec K`; `AlgebraicGeometry.Stack.ValuativeSquare.denseTestUniqueness_of_fibre` states the
hypothesis of Stacks 0E95 in that form.

## Main results

* `AlgebraicGeometry.Stack.ValuativeSquare.isSetoidCategory_dottedArrow_of_schemeTarget`: the
  category of dotted arrows into a represented stack is a setoid under the first condition.
* `AlgebraicGeometry.Stack.ValuativeSquare.nonempty_iso_dottedArrow_of_schemeTarget`: any two
  dotted arrows into a represented stack are isomorphic under the second condition.
* `AlgebraicGeometry.Stack.ValuativeSquare.denseTestUniqueness_of_fibre`: the hypothesis of
  Stacks 0E95 for a 1-morphism into a represented stack, in terms of the fibres of `𝒳`.

## References

* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace ValuativeSquare

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {V : BigFppfOver B S hS}
  {f : 𝒳 ⟶ schemeStack.{u, w} B S hS V}

/-- **The category of dotted arrows into a represented stack is a setoid** when a 2-endomorphism
of a 1-morphism `Spec R ⟶ 𝒳` restricting to the generic point `x` of the square, and restricting
to the identity along the left edge `j` of the square, is the identity. -/
theorem isSetoidCategory_dottedArrow_of_schemeTarget (q : ValuativeSquare B S hS f)
    (hinj : ∀ (a : schemeFibredCategory B S hS (siteObject B S hS q.ring_mem q.base) ⟶ 𝒳.1),
      (q.j ≫ a ⟶ q.x) → ∀ θ : a ⟶ a, q.j ◁ θ = 𝟙 (q.j ≫ a) → θ = 𝟙 a) :
    IsSetoidCategory (CategoryTheory.DottedArrow q.x q.j f.hom q.y q.γ) := by
  refine ⟨fun _ => inferInstance, fun a θ => ?_⟩
  apply CategoryTheory.DottedArrow.Hom.ext
  show θ.θ = 𝟙 a.a
  have hαiso : IsIso a.α := (CatFiberedInGroupoids.homGroupoid _ _).all_isIso a.α
  refine hinj a.a a.α θ.θ ?_
  apply (cancel_mono a.α).1
  simpa using θ.cond_α.symm

/-- **Any two dotted arrows into a represented stack are isomorphic** when every 2-morphism
between the restrictions along the left edge `j` of two 1-morphisms `Spec R ⟶ 𝒳`, the first of
which restricts to the generic point `x` of the square, is the restriction of a 2-morphism. -/
theorem nonempty_iso_dottedArrow_of_schemeTarget (q : ValuativeSquare B S hS f)
    (hext : ∀ (a a' : schemeFibredCategory B S hS (siteObject B S hS q.ring_mem q.base) ⟶ 𝒳.1),
      (q.j ≫ a ⟶ q.x) → ∀ e : q.j ≫ a ⟶ q.j ≫ a', ∃ θ : a ⟶ a', q.j ◁ θ = e)
    (d d' : CategoryTheory.DottedArrow q.x q.j f.hom q.y q.γ) : Nonempty (d ≅ d') := by
  have hαiso : IsIso d'.α := (CatFiberedInGroupoids.homGroupoid _ _).all_isIso d'.α
  obtain ⟨θ, hθ⟩ := hext d.a d'.a d.α (d.α ≫ inv d'.α)
  let t : d ⟶ d' :=
    { θ := θ
      cond_α := by rw [hθ]; simp
      cond_β := (subsingleton_hom₂_schemeFibredCategory B S hS _ _).elim _ _ }
  exact ⟨asIso t⟩

/-! ### Restriction along a map of represented stacks, read in the fibres -/

section Restriction

variable {𝒳' : AlgebraicStacks.{u, w} B S hS} {UK U : BigFppfOver B S hS} (g : UK ⟶ U)
  (j : schemeFibredCategory B S hS UK ⟶ schemeFibredCategory B S hS U)

/-- The image under a 1-morphism `a : U ⟶ 𝒳` of the canonical arrow `(Over.map g).obj 1 ⟶ 1` of
the slice lies over `g`. -/
private theorem isHomLift_map_mkIdTerminal_map
    (a : schemeFibredCategory B S hS U ⟶ 𝒳'.1) :
    𝒳'.val.val.p.IsHomLift g
      (a.hom.map (Over.mkIdTerminal.from ((Over.map g).obj (Over.mk (𝟙 UK))))) := by
  have hc := Functor.TwoYoneda.isHomLift_map_slice 𝒳'.val.val.p (G := a.hom)
    (Over.mkIdTerminal.from ((Over.map g).obj (Over.mk (𝟙 UK))))
  simpa using hc

/-- **Restriction of 2-endomorphisms along `j = Over.map g`, read in the fibres.** If every
endomorphism `t` over `𝟙` of an object `ξ` of `𝒳` over `U` with `c ≫ t = c`, for an arrow
`c : η ⟶ ξ` over `g` with `η` mapping to the value `x(1)` of a given 1-morphism `x : UK ⟶ 𝒳` by an
arrow over `𝟙`, is the identity, then a 2-endomorphism of a 1-morphism `U ⟶ 𝒳` restricting to `x`,
and restricting to the identity along `j`, is the identity. -/
theorem eq_id_of_whiskerLeft_eq_id_of_fibre (hj : j.hom.toFunctor = Over.map g)
    (x : schemeFibredCategory B S hS UK ⟶ 𝒳'.1)
    (hF : ∀ {ξ η : 𝒳'.val.val.obj} (c : η ⟶ ξ) (r : η ⟶ x.hom.toFunctor.obj (Over.mk (𝟙 UK))),
      𝒳'.val.val.p.IsHomLift g c → 𝒳'.val.val.p.IsHomLift (𝟙 UK) r →
      ∀ t : ξ ⟶ ξ, 𝒳'.val.val.p.IsHomLift (𝟙 U) t → c ≫ t = c → t = 𝟙 ξ)
    (a : schemeFibredCategory B S hS U ⟶ 𝒳'.1) (α : j ≫ a ⟶ x)
    (θ : a ⟶ a) (hθ : j ◁ θ = 𝟙 (j ≫ a)) : θ = 𝟙 a := by
  obtain ⟨⟨F, w⟩⟩ := j
  change F = Over.map g at hj
  subst hj
  apply (CatFiberedInGroupoids.homEquivBasedNatTrans a a).injective
  refine Functor.TwoYoneda.hom_ext_of_app_unit 𝒳'.val.val.p 𝒳'.val.isFiberedInGroupoids _ _ ?_
  let o := Over.mk (𝟙 UK)
  have h₁ : θ.hom.toNatTrans.app ((Over.map g).obj o) = 𝟙 _ :=
    congrArg (fun η => η.hom.toNatTrans.app o) hθ
  have hnat := θ.hom.toNatTrans.naturality (Over.mkIdTerminal.from ((Over.map g).obj o))
  rw [h₁, Category.id_comp] at hnat
  exact hF _ (α.hom.toNatTrans.app o) (isHomLift_map_mkIdTerminal_map B S hS g a)
    (CatFiberedInGroupoids.isHomLift_app α o) _
    (CatFiberedInGroupoids.isHomLift_app θ (Over.mk (𝟙 _))) hnat

/-- **Extension of 2-morphisms along `j = Over.map g`, read in the fibres.** If for all objects
`ξ`, `ξ'` of `𝒳` over `U`, arrows `c : η ⟶ ξ` and `c' : η' ⟶ ξ'` over `g` and every arrow
`s : η ⟶ η'` over `𝟙`, with `η` mapping to the value `x(1)` of a given 1-morphism `x : UK ⟶ 𝒳` by
an arrow over `𝟙`, there is an arrow `t : ξ ⟶ ξ'` over `𝟙` with `c ≫ t = s ≫ c'`, then every
2-morphism between the restrictions along `j` of two 1-morphisms `U ⟶ 𝒳`, the first of which
restricts to `x`, is the restriction of a 2-morphism. -/
theorem exists_whiskerLeft_eq_of_fibre (hj : j.hom.toFunctor = Over.map g)
    (x : schemeFibredCategory B S hS UK ⟶ 𝒳'.1)
    (hF : ∀ {ξ ξ' η η' : 𝒳'.val.val.obj} (c : η ⟶ ξ) (c' : η' ⟶ ξ') (s : η ⟶ η')
      (r : η ⟶ x.hom.toFunctor.obj (Over.mk (𝟙 UK))),
      𝒳'.val.val.p.IsHomLift g c → 𝒳'.val.val.p.IsHomLift g c' →
      𝒳'.val.val.p.IsHomLift (𝟙 UK) s → 𝒳'.val.val.p.IsHomLift (𝟙 UK) r →
        ∃ t : ξ ⟶ ξ', 𝒳'.val.val.p.IsHomLift (𝟙 U) t ∧ c ≫ t = s ≫ c')
    (a a' : schemeFibredCategory B S hS U ⟶ 𝒳'.1) (α : j ≫ a ⟶ x)
    (e : j ≫ a ⟶ j ≫ a') : ∃ θ : a ⟶ a', j ◁ θ = e := by
  obtain ⟨⟨F, w⟩⟩ := j
  change F = Over.map g at hj
  subst hj
  let o := Over.mk (𝟙 UK)
  have hr : 𝒳'.val.val.p.IsHomLift (𝟙 UK) (α.hom.toNatTrans.app o) :=
    CatFiberedInGroupoids.isHomLift_app α o
  have hs : 𝒳'.val.val.p.IsHomLift (𝟙 UK) (e.hom.toNatTrans.app o) :=
    CatFiberedInGroupoids.isHomLift_app e o
  obtain ⟨t, ht, htc⟩ := hF _ _ (e.hom.toNatTrans.app o) (α.hom.toNatTrans.app o)
    (isHomLift_map_mkIdTerminal_map B S hS g a) (isHomLift_map_mkIdTerminal_map B S hS g a') hs hr
  let θ : a ⟶ a' := (CatFiberedInGroupoids.homEquivBasedNatTrans a a').symm
    (Functor.TwoYoneda.homOfUnitHom 𝒳'.val.val.p 𝒳'.val.isFiberedInGroupoids t ht)
  refine ⟨θ, ?_⟩
  apply (CatFiberedInGroupoids.homEquivBasedNatTrans _ _).injective
  refine Functor.TwoYoneda.hom_ext_of_app_unit 𝒳'.val.val.p 𝒳'.val.isFiberedInGroupoids _ _ ?_
  show Functor.TwoYoneda.unitHomApp 𝒳'.val.val.p 𝒳'.val.isFiberedInGroupoids t ht
    ((Over.map g).obj o) = e.hom.toNatTrans.app o
  have hcart := Functor.TwoYoneda.isStronglyCartesian_map_from_mkIdTerminal 𝒳'.val.val.p
    𝒳'.val.isFiberedInGroupoids _ a'.hom ((Over.map g).obj o)
  have h₁ := Functor.TwoYoneda.isHomLift_unitHomApp 𝒳'.val.val.p 𝒳'.val.isFiberedInGroupoids
    t ht ((Over.map g).obj o)
  have hs' : 𝒳'.val.val.p.IsHomLift (𝟙 ((Over.map g).obj o).left) (e.hom.toNatTrans.app o) := hs
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ 𝒳'.val.val.p _ _ _ _ ((Over.map g).obj o).hom
    (a'.hom.map (Over.mkIdTerminal.from ((Over.map g).obj o))) hcart _ _
    (𝟙 ((Over.map g).obj o).left) _ _ h₁ hs'
    ((Functor.TwoYoneda.unitHomApp_fac 𝒳'.val.val.p 𝒳'.val.isFiberedInGroupoids t ht
      ((Over.map g).obj o)).trans htc)

end Restriction

/-- **The hypothesis of Stacks 0E95 for a 1-morphism into a represented stack, read in the
fibres.** Let `h : 𝒰 ⟶ 𝒳` and `f : 𝒳 ⟶ 𝒯`, the target `𝒯` being represented by an object of the big
fppf site. Suppose that for every valuative square `q` for `f` over a discrete valuation ring, with
canonical map `g : Spec K ⟶ Spec R`, whose generic point `x` factors through `h`,

* an endomorphism `t` over `𝟙` of an object `ξ` of `𝒳` over `Spec R` with `c ≫ t = c`, for an
  arrow `c : η ⟶ ξ` over `g` and an arrow `η ⟶ x(1)` over `𝟙`, is the identity, and
* for all objects `ξ`, `ξ'` of `𝒳` over `Spec R`, arrows `c : η ⟶ ξ` and `c' : η' ⟶ ξ'` over
  `g`, an arrow `η ⟶ x(1)` over `𝟙` and an arrow `s : η ⟶ η'` over `𝟙`, there is an arrow
  `t : ξ ⟶ ξ'` over `𝟙` with `c ≫ t = s ≫ c'`.

Then the hypothesis of Stacks 0E95 holds for `h` and `f`. -/
theorem denseTestUniqueness_of_fibre {𝒰 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳)
    (hinj : ∀ q : ValuativeSquare B S hS f, IsDiscreteValuationRing q.R →
      (∃ u : schemeFibredCategory B S hS
          (siteObject B S hS q.field_mem
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ 𝒰.1,
        q.x = u ≫ h.hom) →
      ∀ {ξ η : 𝒳.val.val.obj} (c : η ⟶ ξ)
        (r : η ⟶ q.x.hom.toFunctor.obj (Over.mk (𝟙 (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))))),
        𝒳.val.val.p.IsHomLift q.genericMap c →
        𝒳.val.val.p.IsHomLift (𝟙 (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))) r →
      ∀ t : ξ ⟶ ξ, 𝒳.val.val.p.IsHomLift (𝟙 (siteObject B S hS q.ring_mem q.base)) t →
        c ≫ t = c → t = 𝟙 ξ)
    (hext : ∀ q : ValuativeSquare B S hS f, IsDiscreteValuationRing q.R →
      (∃ u : schemeFibredCategory B S hS
          (siteObject B S hS q.field_mem
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ 𝒰.1,
        q.x = u ≫ h.hom) →
      ∀ {ξ ξ' η η' : 𝒳.val.val.obj} (c : η ⟶ ξ) (c' : η' ⟶ ξ') (s : η ⟶ η')
        (r : η ⟶ q.x.hom.toFunctor.obj (Over.mk (𝟙 (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))))),
        𝒳.val.val.p.IsHomLift q.genericMap c → 𝒳.val.val.p.IsHomLift q.genericMap c' →
        𝒳.val.val.p.IsHomLift (𝟙 (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))) s →
        𝒳.val.val.p.IsHomLift (𝟙 (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))) r →
          ∃ t : ξ ⟶ ξ', 𝒳.val.val.p.IsHomLift (𝟙 (siteObject B S hS q.ring_mem q.base)) t ∧
            c ≫ t = s ≫ c') :
    ValuativeCriterion.DenseTestUniqueness B S hS h f := by
  intro q hq hu
  refine ⟨isSetoidCategory_dottedArrow_of_schemeTarget B S hS q fun a α θ hθ =>
      eq_id_of_whiskerLeft_eq_id_of_fibre B S hS q.genericMap q.j q.j_canonical q.x
        (fun c r hc hr t ht htc => hinj q hq hu c r hc hr t ht htc) a α θ hθ,
    nonempty_iso_dottedArrow_of_schemeTarget B S hS q fun a a' α e =>
      exists_whiskerLeft_eq_of_fibre B S hS q.genericMap q.j q.j_canonical q.x
        (fun c c' s r hc hc' hs hr => hext q hq hu c c' s r hc hc' hs hr) a a' α e⟩

end ValuativeSquare

end AlgebraicGeometry.Stack

end
