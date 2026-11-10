module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomRingHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction

/-!
# Maps out of the inverse image of a representable sheaf, as a ring

Let `f` be a morphism of topoi from `Sh(C, J)` to `Sh(D, K)`, let `R` be a sheaf of rings on
`(C, J)` and let `V` be an object of `D`, the site of the target, which we assume subcanonical so
that `V` represents a sheaf `h_V` there.  Composing the adjunction `f⁻¹ ⊣ f_*` with the Yoneda
lemma identifies

`Hom(f⁻¹h_V, R) ≅ Hom(h_V, f_*R) ≅ (f_*R)(V)`,

a bijection of sets.  This file upgrades it to an isomorphism of **rings**: the left-hand side
carries the pointwise ring structure of `CategoryTheory.Sheaf.homRing`, the generalized elements
of `R` of shape `f⁻¹h_V`, and the right-hand side is the ring of sections over `V` of the
direct-image sheaf of rings.

The upgrade is not formal.  The direct image of a sheaf of rings carries a *transported* ring
structure — `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` applied to `f_*`, which preserves
finite products because it is a right adjoint — and the content is that the bijection above
respects it.  It does, because the bijection factors as two maps already known to be ring
homomorphisms: applying `f_*` to a generalized element, which is
`Stacks.Sheaves.ToposPullback.inverseImageRingEltRingHom` for the functor `f_*`, and then
evaluating on the section `𝟙_V`, which is `CategoryTheory.Sheaf.sectionsEvalRingHom`.

The reason to want a *ring* isomorphism is that a system of polynomial equations can then be
transported across it.  This is what the proof of [Stacks Project, Tag 04I6] does in its closing
move: the comparison `f⁻¹h_V → h_{X ×_Y V}` is produced by feeding the coordinate functions
`x₁, …, x_n` of an étale presentation of `V` through the structure map of `f`, and the equations
`Pⱼ(x₁, …, x_n) = 0` continue to hold on the other side for the sole reason that a ring
homomorphism carries a relation to its image.

## Main definitions

* `MorphismOfTopoi.inverseImageYonedaRingHom` — the composite of the adjunction and Yoneda, as a
  ring homomorphism.
* `MorphismOfTopoi.inverseImageYonedaRingEquiv` — the same, as a ring isomorphism.

## Main results

* `MorphismOfTopoi.inverseImageYonedaRingHom_bijective` — the ring homomorphism is bijective,
  being the composite of two bijections.
* `MorphismOfTopoi.inverseImageYonedaRingEquiv_naturality` and
  `MorphismOfTopoi.inverseImageYonedaRingEquiv_symm_naturality` — the identification is **natural
  in `V`**: precomposition with `f⁻¹h_k` on the left corresponds to restriction along `k` on the
  right.  This is what makes the comparison of step (3) of [Stacks Project, Tag 04I6] a natural
  transformation in the chart rather than a family of unrelated maps.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe w v u u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{w} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [K.Subcanonical]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (R : Sheaf J RingCat.{w}) (V : D)

/-- **Maps out of `f⁻¹h_V` into a sheaf of rings `R` form a ring isomorphic to the sections of
`f_*R` over `V`** — the ring homomorphism.  It is the adjunction `f⁻¹ ⊣ f_*` followed by the
Yoneda lemma, written as the composite of the two maps whose ring-homomorphism property is
already known: applying `f_*` to a generalized element, and evaluating the result on `𝟙_V`. -/
def inverseImageYonedaRingHom :
    (f.inverseImage.obj (K.yoneda.obj V) ⟶ ringSheaf R) →+*
      (sectionsFunctor K (op V)).obj (ringSheaf (pullbackRingSheaf K f.pushforward R)) :=
  (sectionsEvalRingHom (op V) (𝟙 V)).comp
    (inverseImageRingEltRingHom K f.pushforward (f.adj.unit.app (K.yoneda.obj V)))

/-- The ring homomorphism of `MorphismOfTopoi.inverseImageYonedaRingHom` is, as a function, the
composite of the adjunction bijection and the Yoneda bijection. -/
theorem inverseImageYonedaRingHom_apply
    (a : f.inverseImage.obj (K.yoneda.obj V) ⟶ ringSheaf R) :
    inverseImageYonedaRingHom f R V a =
      K.yonedaEquiv (f.adj.homEquiv (K.yoneda.obj V) (ringSheaf R) a) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The ring homomorphism of `MorphismOfTopoi.inverseImageYonedaRingHom` is bijective: it is the
adjunction bijection followed by the Yoneda bijection. -/
theorem inverseImageYonedaRingHom_bijective :
    Function.Bijective (inverseImageYonedaRingHom f R V) := by
  have h : (inverseImageYonedaRingHom f R V : _ → _) =
      K.yonedaEquiv ∘ f.adj.homEquiv (K.yoneda.obj V) (ringSheaf R) :=
    funext (inverseImageYonedaRingHom_apply f R V)
  rw [h]
  exact K.yonedaEquiv.bijective.comp
    (f.adj.homEquiv (K.yoneda.obj V) (ringSheaf R)).bijective

/-- **Maps out of `f⁻¹h_V` into a sheaf of rings `R` form a ring isomorphic to the sections of
`f_*R` over `V`.**  The underlying bijection is the adjunction `f⁻¹ ⊣ f_*` followed by the Yoneda
lemma; the ring structure on the left is the pointwise one on generalized elements of `R` of
shape `f⁻¹h_V`, and the one on the right is the transported ring structure of the direct image. -/
def inverseImageYonedaRingEquiv :
    (f.inverseImage.obj (K.yoneda.obj V) ⟶ ringSheaf R) ≃+*
      (sectionsFunctor K (op V)).obj (ringSheaf (pullbackRingSheaf K f.pushforward R)) :=
  RingEquiv.ofBijective _ (inverseImageYonedaRingHom_bijective f R V)

/-- The ring isomorphism `MorphismOfTopoi.inverseImageYonedaRingEquiv` agrees, as a function, with
the ring homomorphism `MorphismOfTopoi.inverseImageYonedaRingHom`. -/
@[simp]
theorem inverseImageYonedaRingEquiv_apply
    (a : f.inverseImage.obj (K.yoneda.obj V) ⟶ ringSheaf R) :
    inverseImageYonedaRingEquiv f R V a = inverseImageYonedaRingHom f R V a :=
  rfl

/-- **The identification of `Hom(f⁻¹h_V, R)` with `(f_*R)(V)` is natural in `V`.**  Precomposing a
generalized element of `R` of shape `f⁻¹h_{V'}` with `f⁻¹h_k`, for `k : V ⟶ V'`, corresponds to
restricting the corresponding section of `f_*R` from `V'` to `V`.

Both halves of the identification are natural: the adjunction bijection in its left variable
(`CategoryTheory.Adjunction.homEquiv_naturality_left`) and the Yoneda bijection
(`CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality`). -/
theorem inverseImageYonedaRingEquiv_naturality (V' : D) (k : V ⟶ V')
    (a : f.inverseImage.obj (K.yoneda.obj V') ⟶ ringSheaf R) :
    inverseImageYonedaRingEquiv f R V (f.inverseImage.map (K.yoneda.map k) ≫ a) =
      (ringSheaf (pullbackRingSheaf K f.pushforward R)).obj.map k.op
        (inverseImageYonedaRingEquiv f R V' a) := by
  rw [inverseImageYonedaRingEquiv_apply, inverseImageYonedaRingEquiv_apply,
    inverseImageYonedaRingHom_apply, inverseImageYonedaRingHom_apply,
    Adjunction.homEquiv_naturality_left]
  exact (K.yonedaEquiv_naturality _ k).symm

/-- **The inverse identification is natural in `V`**, the form in which the comparison of step (3)
of the proof of [Stacks Project, Tag 04I6] uses it: a section of `f_*R` over `V'`, restricted to
`V` and read as a map out of `f⁻¹h_V`, is the map out of `f⁻¹h_{V'}` precomposed with
`f⁻¹h_k`. -/
theorem inverseImageYonedaRingEquiv_symm_naturality (V' : D) (k : V ⟶ V')
    (z : (sectionsFunctor K (op V')).obj
      (ringSheaf (pullbackRingSheaf K f.pushforward R))) :
    (inverseImageYonedaRingEquiv f R V).symm
        ((ringSheaf (pullbackRingSheaf K f.pushforward R)).obj.map k.op z) =
      f.inverseImage.map (K.yoneda.map k) ≫ (inverseImageYonedaRingEquiv f R V').symm z :=
  (inverseImageYonedaRingEquiv f R V).symm_apply_eq.2
    (((inverseImageYonedaRingEquiv_naturality f R V V' k
        ((inverseImageYonedaRingEquiv f R V').symm z)).trans
      (congrArg (fun w => (ringSheaf (pullbackRingSheaf K f.pushforward R)).obj.map k.op w)
        ((inverseImageYonedaRingEquiv f R V').apply_symm_apply z))).symm)

end MorphismOfTopoi

end
