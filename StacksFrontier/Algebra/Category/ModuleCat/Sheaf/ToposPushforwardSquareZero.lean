module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction

/-!
# A square zero ideal stays square zero under a transported ring structure

Let `J` and `K` be Grothendieck topologies, let `Φ : Sh(K, Type) ⥤ Sh(J, Type)` preserve finite
products and let `O` be a sheaf of rings on `K`.  The inverse image `Φ O` of Stacks 00YV carries
the ring structure transported along `Φ` — `Stacks.Sheaves.ToposPullback.pullbackRingSheaf`,
whose multiplication on sections over an object `U` is
`CategoryTheory.Sheaf.ringMulObj O (Φ ⋙ Sheaf.sectionsFunctor J U)`. This file shows:

**if `κ : N ⟶ O` is a map of sheaves of sets whose values multiply to zero in `O`, then the
values of `Φ κ` multiply to zero in `Φ O`.**

## Main results

* `CategoryTheory.Sheaf.ringMulObj_map_eq_zero`: the generic statement, for a
  finite-product-preserving functor to types.
* `CategoryTheory.Sheaf.ringObj_map_map_eq_zero`: the companion statement that a family killed by
  a map of sheaves of rings stays killed after the transport.
* `Stacks.Sheaves.ToposPushforward.mul_eq_zero_of_mem_range_pushforward_map`: two sections of the
  direct image `f_*A` of a sheaf of commutative rings `A` along a morphism of topoi `f` which come
  from `f_*κ` multiply to zero.
* `Stacks.Sheaves.ToposPushforward.pushforward_map_apply_eq_zero_of_mem_range`: a family killed by
  a map of sheaves of commutative rings stays killed in a direct image.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t w v u v' u'

namespace CategoryTheory.Sheaf

open _root_.CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] (R : Sheaf J RingCat.{w})
  (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- A morphism to the ring sheaf which factors through the terminal object by the zero map is
sent to the transported zero. -/
private theorem map_eq_ringZeroObj_of_eq {X : Sheaf J (Type w)} {g : X ⟶ ringSheaf R}
    (hg : g = terminal.from X ≫ ringZeroHom R) (x : P.obj X) : P.map g x = ringZeroObj R P := by
  have h := congrArg (fun m => P.map m x) hg
  simp only [P.map_comp_apply, map_terminalFrom_apply] at h
  exact h

/-- **A product of two transported sections pulled back from a square zero family vanishes.**
If the values of `κ : N ⟶ 𝒪` multiply to zero on every object of the site, then the values of
`P κ` multiply to zero in the ring structure transported to `P 𝒪` along a
finite-product-preserving functor `P` to types. -/
theorem ringMulObj_map_eq_zero {N : Sheaf J (Type w)} (κ : N ⟶ ringSheaf R)
    (hκ : ∀ (U : Cᵒᵖ) (s s' : (sectionsFunctor J U).obj N),
      (sectionsFunctor J U).map κ s * (sectionsFunctor J U).map κ s' = 0)
    (x y : P.obj N) :
    ringMulObj R P (P.map κ x) (P.map κ y) = ringZeroObj R P := by
  have hmor : prod.lift (prod.fst ≫ κ) (prod.snd ≫ κ) ≫ ringMulHom R =
      terminal.from (N ⨯ N) ≫ ringZeroHom R := by
    refine hom_ext_sections fun U s => ?_
    simp [hκ]
  simpa [ringMulObj, map_lift_apply] using map_eq_ringZeroObj_of_eq R P hmor (prodObjMk x y)

/-- **A family killed by a map of sheaves of rings stays killed after transport.**  If the values
of `κ : N ⟶ 𝒪` are killed by `q : 𝒪 ⟶ 𝒪'`, then the values of `P κ` are killed by `P q` in the
transported ring structures. -/
theorem ringObj_map_map_eq_zero {R' : Sheaf J RingCat.{w}} {N : Sheaf J (Type w)}
    (κ : N ⟶ ringSheaf R) (q : ringSheaf R ⟶ ringSheaf R')
    (hκ : ∀ (U : Cᵒᵖ) (s : (sectionsFunctor J U).obj N),
      (sectionsFunctor J U).map q ((sectionsFunctor J U).map κ s) = 0)
    (u : P.obj N) :
    P.map q (P.map κ u) = ringZeroObj R' P := by
  have hmor : κ ≫ q = terminal.from N ≫ ringZeroHom R' := by
    refine hom_ext_sections fun U s => ?_
    simp [hκ]
  simpa using map_eq_ringZeroObj_of_eq R' P hmor u

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory.Sheaf Stacks.Sheaves.ToposPullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **A product of two sections of a direct image which come from a square zero family
vanishes.**  Let `f` be a morphism of topoi, let `A` be a sheaf of commutative rings on the
source and let `κ : N ⟶ A` be a map of sheaves of sets whose values multiply to zero.  Then any
two sections of `f_*A` in the image of `f_*κ` multiply to zero. -/
theorem mul_eq_zero_of_mem_range_pushforward_map
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
    (A : Sheaf J CommRingCat.{w}) {N : Sheaf J (Type w)}
    (κ : N ⟶ CategoryTheory.Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf A))
    (hκ : ∀ (U : Cᵒᵖ) (s s' : (sectionsFunctor J U).obj N),
      (sectionsFunctor J U).map κ s * (sectionsFunctor J U).map κ s' = 0)
    (V : Dᵒᵖ) (x y : ((pushforwardCommRingFunctor f).obj A).obj.obj V)
    (hx : ∃ s : (f.pushforward.obj N).obj.obj V, (f.pushforward.map κ).hom.app V s = x)
    (hy : ∃ s : (f.pushforward.obj N).obj.obj V, (f.pushforward.map κ).hom.app V s = y) :
    x * y = 0 := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨s', hs'⟩ := hy
  subst hs
  subst hs'
  exact ringMulObj_map_eq_zero (Stacks.SheafOfModules.Tensor.ringSheaf A)
    (f.pushforward ⋙ sectionsFunctor K V) κ hκ s s'

/-- **A family killed by a map of sheaves of commutative rings stays killed in a direct image.**
If the values of `κ : N ⟶ A` are killed by `q : A ⟶ A'`, then the values of `f_*κ` are killed by
`f_*q`. -/
theorem pushforward_map_apply_eq_zero_of_mem_range
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
    {A A' : Sheaf J CommRingCat.{w}} (q : A ⟶ A') {N : Sheaf J (Type w)}
    (κ : N ⟶ CategoryTheory.Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf A))
    (hκ : ∀ (U : Cᵒᵖ) (s : (sectionsFunctor J U).obj N),
      (q.hom.app U).hom ((sectionsFunctor J U).map κ s) = 0)
    (V : Dᵒᵖ) (u : (f.pushforward.obj N).obj.obj V) :
    (((pushforwardCommRingFunctor f).map q).hom.app V).hom
        ((f.pushforward.map κ).hom.app V u) = 0 := by
  have hq := forgetCommRingSheaf_map_pullbackCommRingSheafMap K f.pushforward q
  have hfun : ∀ z, (((pushforwardCommRingFunctor f).map q).hom.app V).hom z =
      (f.pushforward ⋙ sectionsFunctor K V).map
        ((sheafCompose J (forget RingCat.{w})).map ((Stacks.forgetCommRingSheaf J).map q)) z :=
    fun z => congrArg (fun m => (m.hom.app V).hom z) hq
  exact (hfun _).trans (ringObj_map_map_eq_zero (Stacks.SheafOfModules.Tensor.ringSheaf A)
    (f.pushforward ⋙ sectionsFunctor K V) κ
    ((sheafCompose J (forget RingCat.{w})).map ((Stacks.forgetCommRingSheaf J).map q)) hκ u)

end Stacks.Sheaves.ToposPushforward

end
