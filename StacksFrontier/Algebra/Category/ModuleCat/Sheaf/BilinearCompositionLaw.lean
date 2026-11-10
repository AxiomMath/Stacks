module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas
public import StacksFrontier.CategoryTheory.Sites.Topos.InverseImageComp

/-!
# The composition law of the bilinear-pairing bijection of Tag 03D3

The third step of the chain of bijections of Tag 03EL is
`Stacks.SheafOfModules.inverseImageBilinearEquiv`, the transport of bilinear pairings along a
morphism of topoi `f`:

`Bilin_{f⁻¹O}(f⁻¹F × f⁻¹G, N) = Bilin_O(F × G, f_*N)`.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality` and
`…BilinearSourceNaturality` record its naturality in the sheaf of values and in the two source
modules, and `…BilinearValueFormulas` writes its two directions out as morphism-level formulas —
all for one fixed `f`. This file supplies the law in the *morphism* variable: how the transport
along a composite `ψ ∘ φ` of morphisms of topoi is built out of the transport along `φ` and the
transport along `ψ`.

The law is stated on the underlying pairing rather than on the bilinear subtype, which loses
nothing: `Stacks.SheafOfModules.inverseImageBilinearEquiv` is
`Stacks.SheafOfModules.inverseImagePairingEquiv` on underlying pairings, by
`Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe`, and the bilinearity of the image is
carried along rather than computed. Nor is the statement about an iterated *pairing bijection*:
it is about the two halves the bijection is assembled from, the product comparison of `f⁻¹` and
the transposition across `f⁻¹ ⊣ f_*`, each of which is unwound one stage at a time. The
implementation notes say why that is the honest form.

## Main results

* `Stacks.SheafOfModules.inverseImagePairingEquiv_comp`: **the composition law.** The pairing into
  the direct image produced by the bijection of Tag 03D3 for a composite `ψ ∘ φ` is obtained by
  composing with the product comparison of `φ⁻¹` and transposing across `φ⁻¹ ⊣ φ_*`, then
  composing with the product comparison of `ψ⁻¹` and transposing across `ψ⁻¹ ⊣ ψ_*`.
* `Stacks.SheafOfModules.inverseImageBilinearEquiv_comp`: the same law for the bilinear-pairing
  bijection itself, read on the underlying pairing.

## Implementation notes

*Why the law is not an equation between composed bijections.* Composing the bijection for `φ`
with the bijection for `ψ` would require their types to meet, and they do not meet on the nose.
The bijection for `φ` is taken at the base ring `ψ⁻¹O` and produces a pairing with values in
`φ_*N`, which the bijection for `ψ` would then consume; but the bijection for `ψ` demands a
module over `ψ⁻¹O`, while the bijection for the composite demands a module over `(ψ ∘ φ)⁻¹O`, and
those two sheaves of rings are *not* the same object. They have the same underlying sheaf of sets
— `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso` is the identity on sections — but their
transported ring structures are only provably equal, so the two sides of a composed bijection
would have to be joined by a restriction of scalars along that comparison, and the sources would
have to be joined by `Stacks.Sheaves.ToposPullback.pullbackModuleCompIso`. The resulting statement
would be an equality of bijections between types related by three transports, and nothing in the
chain of Tag 03EL consumes it in that shape.

What the chain does consume is the *value* of the bijection on a given pairing, and that is what
is stated here: both sides are morphisms out of the inverse image of a product, in the single
spelling `(ψ ∘ φ)⁻¹` that the bijection for the composite already uses. No sheaf of rings appears
in the statement at all, only the two topos-level halves of the bijection, so no transport is
needed and the law is an equality of morphisms rather than of bijections.

*The seam.* `Stacks.SheafOfModules.inverseImagePairingEquiv` has the inverse images in its type
spelled geometrically, as `f⁻¹` applied to the underlying sheaf of sets of a module, while the
intermediate modules of a two-stage transport are spelled as inverse images of sheaves of
modules; the two agree only at default transparency, as the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas` record. Keeping the
statement
at the geometric spelling, which is the one the bijection's own type uses, is what keeps that
seam out of it.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section Comp

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{w})] [L.HasSheafCompose (forget RingCat.{w''})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [L.HasSheafCompose (forget AddCommGrpCat.{w''})]
  (φ : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (ψ : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
  (O : Sheaf L RingCat.{w''}) (F G : SheafOfModules.{w''} O)
  (N : SheafOfModules.{w} (inverseImageRingSheaf (ψ.comp φ) O))

/-- **The composition law of the bijection of Tag 03D3 in the morphism variable.** Let
`φ : Sh(C) → Sh(D)` and `ψ : Sh(D) → Sh(E)` be morphisms of topoi, let `O` be a sheaf of rings on
`E` and let `F`, `G` be sheaves of `O`-modules. A pairing `q` of the inverse images of `F` and `G`
along the composite, with values in a sheaf of `(ψ ∘ φ)⁻¹O`-modules `N`, is carried to a pairing
of `F` and `G` with values in `(ψ ∘ φ)_*N` in two stages: compose with the product comparison of
`φ⁻¹` and transpose across `φ⁻¹ ⊣ φ_*`, then compose with the product comparison of `ψ⁻¹` and
transpose across `ψ⁻¹ ⊣ ψ_*`.

This is the composition law that the third step of the chain of Tag 03EL needs. It is
`MorphismOfTopoi.comp_homEquiv_prodComparison` read for the underlying sheaves of sets of `F` and
`G`: by `Stacks.SheafOfModules.inverseImagePairingEquiv_apply` the bijection *is* the product
comparison followed by the transposition, so the composition law of the bijection is the
composition law of those two.

No sheaf-compose instance over the middle site `D` is needed, and none is assumed: the law never
mentions the intermediate sheaf of rings `ψ⁻¹O`, which is exactly what keeps it free of the
transports a composed bijection would require. -/
theorem inverseImagePairingEquiv_comp
    (q : (ψ.comp φ).inverseImage.obj (moduleSheaf O F) ⨯
        (ψ.comp φ).inverseImage.obj (moduleSheaf O G) ⟶
      moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N) :
    inverseImagePairingEquiv (ψ.comp φ) O F G N q =
      ψ.adj.homEquiv (moduleSheaf O F ⨯ moduleSheaf O G)
          (φ.pushforward.obj (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N))
        (prodComparison ψ.inverseImage (moduleSheaf O F) (moduleSheaf O G) ≫
          φ.adj.homEquiv (ψ.inverseImage.obj (moduleSheaf O F) ⨯
              ψ.inverseImage.obj (moduleSheaf O G))
              (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N)
            (prodComparison φ.inverseImage (ψ.inverseImage.obj (moduleSheaf O F))
              (ψ.inverseImage.obj (moduleSheaf O G)) ≫ q)) :=
  MorphismOfTopoi.comp_homEquiv_prodComparison φ ψ (moduleSheaf O F) (moduleSheaf O G) q

/-- **The composition law of the bilinear-pairing bijection of Tag 03D3.** The underlying pairing
of the image of a bilinear pairing `q` under the bijection for a composite `ψ ∘ φ` is the
two-stage transport of `Stacks.SheafOfModules.inverseImagePairingEquiv_comp`.

The bilinearity of the image is not part of the statement: the bijection carries it along rather
than computing it, which is `Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe`. -/
theorem inverseImageBilinearEquiv_comp
    (q : { q : moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O)
          ((inverseImageModules (ψ.comp φ) O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O)
          ((inverseImageModules (ψ.comp φ) O).obj G) ⟶
          moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N //
      IsBilinearPairing (inverseImageRingSheaf (ψ.comp φ) O) q }) :
    (inverseImageBilinearEquiv (ψ.comp φ) O F G N q).1 =
      ψ.adj.homEquiv (moduleSheaf O F ⨯ moduleSheaf O G)
          (φ.pushforward.obj (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N))
        (prodComparison ψ.inverseImage (moduleSheaf O F) (moduleSheaf O G) ≫
          φ.adj.homEquiv (ψ.inverseImage.obj (moduleSheaf O F) ⨯
              ψ.inverseImage.obj (moduleSheaf O G))
              (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N)
            (prodComparison φ.inverseImage (ψ.inverseImage.obj (moduleSheaf O F))
              (ψ.inverseImage.obj (moduleSheaf O G)) ≫ q.1)) :=
  inverseImagePairingEquiv_comp φ ψ O F G N q.1

end Comp

end Stacks.SheafOfModules

end
