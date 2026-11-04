module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBaseFunctor

/-!
# The global sections of the internal hom are the morphisms, `A`-linearly

`Stacks.Algebraization.internalHomSectionsTopMapAddEquiv` — the degenerate case `U = ⊤` of
[Stacks, Tag 0882] — identifies the morphisms `G ⟶ ℳ` of sheaves of modules on a scheme with the
global sections of `𝓗om(G, ℳ)`, as an isomorphism of *abelian groups*. For a scheme over a base
ring `A` both sides are `A`-modules, and this file upgrades the identification to an isomorphism
of `A`-modules.

An isomorphism of abelian groups between two `A`-modules says nothing about their dimensions over
`A`; the `A`-linear form below is what lets a count of global sections of an internal hom be read
as a count of morphisms, which is how the duality of dimensions of
[Stacks, Tag 0BS6] clause (3) is reached at a vector bundle other than `𝒪_X`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `Stacks.Algebraization.internalHomSectionsTopMapAddEquiv_smul`: the comparison carries the
  action of a scalar on a morphism to the action of its image on a section.
* `internalHomSectionsTopLinearEquivGlobalSections`:
  **`(G ⟶ ℳ) ≃ₗ[A] Γ(X, 𝓗om(G, ℳ))`**.
* `finrank_hom_eq_finrank_globalSectionsOver_sheafHom`: the resulting equality of dimensions.

## The proof

Both module structures are postcomposition with multiplication by the image of the scalar. On the
left, `AlgebraicGeometry.Scheme.linearOfRingHom` makes `a • g` the morphism whose value on
sections over an open `V` is multiplication by the restriction of the image of `a`, which is
`Stacks.SheafOfModules.smul_val_app`. On the right, the `Γ(X, ⊤)`-module structure on the
sections of the internal hom over `⊤` is
`Stacks.SheafOfModules.smulHom`, postcomposition with `Stacks.SheafOfModules.multEndoHom`, whose
value on sections over `V` is again multiplication by that restriction. The comparison itself is
`Functor.map` of `Stacks.Algebraization.topOverForget`, which acts componentwise, so the two sides
agree open by open. The arrow `V ⟶ ⊤` along which the restriction is taken is the unique one in
either description, the opens of a space being a poset.

The two spellings `f.appLE ⊤ ⊤` and `f.appTop` of the structure map intervene: the `A`-linear
structure on the sheaves of modules is taken at `Stacks.LocalCohomology.baseScalars`, which uses
the first — this is the same instance as
`AlgebraicGeometry.Scheme.Modules.linearOverBase`, whose body it is — and
`AlgebraicGeometry.globalSectionsOver` restricts scalars along the second. They are
equal by `AlgebraicGeometry.Scheme.Hom.appLE_eq_app`, and that equality is rewritten in
`map_smul'`.

## References

* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Algebraization

/-- **The comparison of [Stacks, Tag 0882] at `U = ⊤` commutes with the action of the base
ring.** A scalar acts on a morphism of sheaves of modules by multiplication by the restriction of
its image in `Γ(X, 𝒪_X)`, and on a section of the internal hom over `⊤` by postcomposition with
multiplication by that same restriction. -/
public theorem internalHomSectionsTopMapAddEquiv_smul (X : Scheme.{u}) (A : Type u) [CommRing A]
    (φ : A →+* Γ(X, ⊤)) (G M : X.Modules) (a : A) (g : G ⟶ M) :
    letI : Linear A X.Modules := AlgebraicGeometry.Scheme.linearOfRingHom X A φ
    internalHomSectionsTopMapAddEquiv G M (a • g) =
      (show X.ringCatSheaf.obj.obj (op ⊤) from φ a) •
        internalHomSectionsTopMapAddEquiv G M g :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext <| LinearMap.ext fun x =>
    Stacks.SheafOfModules.smul_val_app X.ringCatSheaf A ⊤ Limits.isTerminalTop φ
      a g (op V.unop.left) x

end Stacks.Algebraization

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`Hom_{𝒪_X}(G, ℳ) ≃ₗ[A] Γ(X, 𝓗om(G, ℳ))`** on a scheme over `A`: the comparison of
[Stacks, Tag 0882] at `U = ⊤`, read `A`-linearly. -/
public def internalHomSectionsTopLinearEquivGlobalSections (G M : X.Modules) :
    letI : Linear A X.Modules :=
      Scheme.linearOfRingHom X A (Stacks.LocalCohomology.baseScalars A f)
    (G ⟶ M) ≃ₗ[A] (globalSectionsOver f).obj
      ((Stacks.Algebraization.sheafHomFunctor X G).obj M) :=
  letI : Linear A X.Modules :=
      Scheme.linearOfRingHom X A (Stacks.LocalCohomology.baseScalars A f)
  { __ := Stacks.Algebraization.internalHomSectionsTopMapAddEquiv G M
    map_smul' := fun a g =>
      (Stacks.Algebraization.internalHomSectionsTopMapAddEquiv_smul X A
        (Stacks.LocalCohomology.baseScalars A f) G M a g).trans <|
        congrArg (fun c : Γ(X, ⊤) =>
          (show X.ringCatSheaf.obj.obj (op ⊤) from c) •
            Stacks.Algebraization.internalHomSectionsTopMapAddEquiv G M g)
          (congrArg (fun m : Γ(Spec (.of A), ⊤) ⟶ Γ(X, ⊤) =>
            ((Scheme.ΓSpecIso (.of A)).inv ≫ m).hom a) (Scheme.Hom.appLE_eq_app f (U := ⊤))) }

/-- **`dim_A Hom_{𝒪_X}(G, ℳ) = dim_A Γ(X, 𝓗om(G, ℳ))`.** -/
public theorem finrank_hom_eq_finrank_globalSectionsOver_sheafHom (G M : X.Modules) :
    letI : Linear A X.Modules :=
      Scheme.linearOfRingHom X A (Stacks.LocalCohomology.baseScalars A f)
    Module.finrank A (G ⟶ M) =
      Module.finrank A ((globalSectionsOver f).obj
        ((Stacks.Algebraization.sheafHomFunctor X G).obj M)) :=
  let : Linear A X.Modules :=
      Scheme.linearOfRingHom X A (Stacks.LocalCohomology.baseScalars A f)
  (internalHomSectionsTopLinearEquivGlobalSections f G M).finrank_eq

end AlgebraicGeometry

end
