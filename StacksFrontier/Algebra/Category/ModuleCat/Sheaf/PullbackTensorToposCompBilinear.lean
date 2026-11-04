module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTensorUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposComp

/-!
# The chain of Tag 03EL regrouped, and its composition law

Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi and let `χ : (Sh(C), O_C) ⟶ (Sh(E), O_E)` play the role of their composite, joined
to it by a comparison `τ` of the geometric direct images as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso`. The comparison of
Tag 03EL for `χ` ought to be the comparison for `ψ` pulled back along `φ`, followed by the
comparison for `φ`. The comparison is defined by the chain of six bijections
`Stacks.SheafOfModules.pullbackTensorStep1` … `Stacks.SheafOfModules.pullbackTensorStep6`, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposComp` proves that identity for
the first two steps, those over the fixed site `E`. Beyond them the two chains were not
comparable: the remaining four steps of `χ`'s chain are over `χ⁻¹O_E` on `C`, whereas the
composite route meets a chain over `ψ⁻¹O_E` on `D` and one over `φ⁻¹O_D` on `C`, so there is no
step-by-step correspondence to prove — the composite route traverses nine steps where `χ`'s
chain traverses four.

This file removes that obstruction by **regrouping the chain**. Steps 3 to 6 compose, after the
universal property of the tensor product over the structure sheaf of the source is undone, to a
single bijection

`Bilin_{O_E}(F × G, χ_*N) ≃ Bilin_{O_C}(χ^*F × χ^*G, N)`,

`Stacks.SheafOfModules.pullbackTensorBilinEquiv`, the base change of bilinear pairings along
`χ`. With that one bijection in place of four steps the chain has four links — the adjunction of
Tag 03D7, the universal property of the tensor product over `O_E`, the base change of pairings,
and the universal property of the tensor product over `O_C` — and the two routes **do**
correspond, because on the composite route two of the links cancel in pairs:

* the inner transposition of `φ`'s adjunction cancels against the outer one, since the composite
  route transposes a morphism out of `φ^*ψ^*(F ⊗ G)` across `φ` only to transpose it back; and
* `ψ`'s last link, the universal property of the tensor product over `O_D` at
  `(ψ^*F, ψ^*G)`, is the *inverse* of `φ`'s second link, which is the universal property of the
  tensor product over `O_D` at the very same pair. That is
  `Stacks.SheafOfModules.pullbackTensorStep2_eq_stepTarget_symm`, and it holds on the nose.

What is left after both cancellations is one link of each route against the other, and that is
the content of `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_iff`: the composition law for
the chain of Tag 03EL holds **if and only if** the base change of bilinear pairings is
compatible with composition. So the composition law is no longer a coherence problem spread over
steps of two incomparable lengths; it is one equation between two bijections on bilinear
pairings. That equation is `Stacks.SheafOfModules.pullbackTensorBilinEquiv_comp`, and it is
proved here, from the unit formula described below; with it the composition law for Tag 03EL,
`Stacks.SheafOfModules.pullbackTensorHomEquiv_comp`, follows.

## Main definitions

* `Stacks.SheafOfModules.pullbackTensorStepTarget`: the universal property of the tensor product
  sheaf over the structure sheaf of the *source*, at the two pullbacks. This is the fourth link
  of the regrouped chain, and it is the link whose two readings cancel on the composite route.
* `Stacks.SheafOfModules.pullbackTensorBilinEquiv`: **the base change of bilinear pairings
  along a morphism of ringed topoi**, `Bilin_{O_D}(F × G, f_*N) ≃ Bilin_{O_C}(f^*F × f^*G, N)`,
  the third link of the regrouped chain. It is steps 3 to 6 of Tag 03EL's chain with the
  universal property of the tensor product over `O_C` undone.
* `Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv`: the extension-of-scalars half of that
  base change, `Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|) ≃ Bilin_{O_C}(f^*F × f^*G, N)`, which is steps 4
  to 6 alone.
* `Stacks.SheafOfModules.pullbackTensorCompTranspose` and
  `Stacks.SheafOfModules.pullbackTensorCompPairing`: the transpose across `φ` of a morphism out
  of `φ^*ψ^*(F ⊗ G)`, and the bilinear pairing over `O_E` that both routes start from.

## Main results

* `Stacks.SheafOfModules.pullbackTensorHomEquiv_eq_regrouped` and
  `Stacks.SheafOfModules.pullbackTensorHomEquiv_apply`: **the chain of Tag 03EL is the regrouped
  four-link chain.** Nothing is changed about the comparison of Tag 03EL; the two groupings are
  the same bijection.
* `Stacks.SheafOfModules.pullbackTensorStep2_eq_stepTarget_symm`: **the cancellation.** Step 2 of
  `φ`'s chain at `(ψ^*F, ψ^*G)` is the inverse of the fourth link of `ψ`'s chain at `(F, G)`.
* `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_left`: **the composite's own route.** The
  chain of `χ`, applied to a morphism precomposed with the comparison of pullbacks, is the last
  two links of `χ`'s chain applied to the shared pairing, transported along the comparison of
  direct images.
* `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_right`: **the composite route.** The chain
  of `φ` applied to the transpose of the chain of `ψ` is the last link of `φ`'s chain applied to
  the base change of pairings along `ψ` and then along `φ`, of the same shared pairing. This is
  where both cancellations happen.
* `Stacks.SheafOfModules.pullbackTensorStepTarget_precomp`: the fourth link is natural in its
  two source modules, at the two spellings the two routes use.
* `Stacks.SheafOfModules.pullbackAdjPushforwardModules_unit_comp_pullbackModulesCompIso` and
  `Stacks.SheafOfModules.moduleSheafFunctor_map_unit_comp_pullbackModulesCompIso`: **the unit of
  Tag 03D7 is compatible with composition**, with the comparison of direct images on the target
  rather than read into the adjunction, on sheaves of modules and on underlying sheaves of sets.
* `Stacks.SheafOfModules.prodMap_natIso_inv_prodComparison_map`: for a comparison
  `θ : K ⋙ L ≅ M` of a composite of functors with a third, the image of a morphism out of a
  binary product, read on the product of the images, is transported along `θ` by transporting the
  two factors. This is the step that trades the component of `θ` at each source object for the one
  at the object of values.
* `Stacks.SheafOfModules.prodMap_natIso_inv_prodComparison_map_comp`: the same trade with the two
  routes' factors supplied and the precomposition in the two source variables pushed across the
  product comparison. This is the whole of the bookkeeping the composition law needs.
* `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_iff`: **the composition law for the chain of
  Tag 03EL is equivalent to the composition law for the base change of bilinear pairings.**
* `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_prodMap_comp` and
  `Stacks.SheafOfModules.pullbackTensorBilinEquiv_comp`: **the composition law for the base change
  of bilinear pairings**, for the inverse bijection and for the bijection itself.
* `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp`: **the composition law for the chain of
  Tag 03EL.** The comparison of Tag 03EL for `χ` is the comparison for `ψ` pulled back along `φ`
  followed by the comparison for `φ`.
* `Stacks.SheafOfModules.pullbackTensorBilinEquiv_eq` and
  `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply`: the base change of pairings is the
  transport along the inverse image followed by the extension of scalars, and its inverse is the
  extension of scalars undone followed by the bijection of Tag 03D3. The second is the outer
  layer of the unit formula that would settle the composition law, since
  `Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe_eq_unit_comp` already writes that
  bijection as the unit of `f⁻¹ ⊣ f_*` followed by the direct image of the pairing.
* `Stacks.SheafOfModules.pullbackTensorStep5_symm_step6_symm_stepTarget`: **steps 5 and 6 of the
  chain, traversed backwards, are the unit of Tag 03CZ followed by the base change of a tensor
  product.** This removes both steps at once and leaves an expression built only from that unit
  and `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`, which is what
  `Stacks.Sheaves.RingedToposModules.sheafificationUnit_comp_extendScalarsTensorIso_hom_val`
  computes on a pure tensor. The inverse of step 6 costs nothing: it is
  `CategoryTheory.Iso.homFromEquiv` run backwards, i.e. composition with the hom, which the
  hom-equivalence of Tag 03CZ absorbs.
* `Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv_symm_apply_coe`: **the inner layer of the
  unit formula.** The inverse of the extension-of-scalars half carries a pairing `q` over `O_C`
  to `q` precomposed in each variable with the unit `f⁻¹F ⟶ (f^*F)|` of Tag 03CZ.
* `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply_coe_eq_unit_comp`: **the unit formula
  for the base change of bilinear pairings**, the two layers assembled. Every factor of the
  resulting composite is a morphism with a value formula of its own.
* `Stacks.SheafOfModules.moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app`: the unit
  of Tag 03D7, on underlying sheaves of sets, is the unit of Tag 03D3 followed by the direct image
  of the unit of Tag 03CZ. This identifies the two units the formula above produces with the
  single unit whose compatibility with composition is already known.
* `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit`: **the unit
  formula in the form Stacks states it**, `q ↦ (η_F × η_G) ≫ f_*q`, with `η` the one unit of
  Tag 03D7.

## Implementation notes

Every object appearing in a composition is written out: no factor of a composite and no implicit
argument of an `CategoryTheory.Adjunction.homEquiv` is left as `_`. Two spellings of one sheaf of
modules — `(tensorSheafBifunctor E.J ⋙ pullbackModules ψ).obj (F, G)` and
`(pullbackModules ψ).obj ((tensorSheafBifunctor E.J).obj (F, G))`, say — are definitionally equal
only at default transparency, so a goal that mixes them is not type-correct at the transparency
`rw` does its motive check at, and the rewrite fails with no useful message. Naming the object
keeps the two routes on one spelling throughout.

`Stacks.SheafOfModules.pullbackTensorStepTarget_precomp` is proved in term mode from
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_precomp`, but the two differ by more than a
transparency: the tensor product of two morphisms read on the uncurried bifunctor,
`(Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor C.O)).map (s, u)`, is the
functorial image of `s` whiskered with the target of `u` *followed by* the image of `u`, whereas
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_precomp` produces the single sheafified
morphism `(PresheafOfModules.sheafification (𝟙 _)).map (s.val ⊗ₘ u.val)`. The two are equal only
propositionally, by `Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`, whose proof is the
functoriality of sheafification; that identity is composed onto the library lemma here.

**What remains for the composition law.** The equation
`Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_iff` reduces it to is the compatibility of
`Stacks.SheafOfModules.pullbackTensorBilinEquiv` with composition. The route to it taken here is
the **unit formula** for its inverse — that it carries a pairing `q` to `(η_F × η_G) ≫ f_*q`,
with `η` the unit of the adjunction of Tag 03D7 on modules — from which the composition law
follows from the compatibility of that unit with composition alone, with no exchange law between
the inverse image and the extension of scalars needed. That formula splits along
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply`, and its **outer layer is already
proved**: `Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe_eq_unit_comp` is exactly
`f.adj.unit ≫ f_*(prodComparison ≫ q)`.

The inner layer is `Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv_symm_apply_coe`:
`((pullbackTensorExtendBilinEquiv f F G N).symm q).1` is `prod.map ε_F ε_G ≫ q.1`, with `ε` the
unit of the extension-restriction adjunction of Tag 03CZ. Both sides are pairings, so the
identity is checked on a pair of local sections, where the two value formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearValueFormulas` — which read a pairing off a
morphism out of a tensor product sheaf on the sheafification-unit image of a pure tensor — reduce
it to the pure-tensor identity for the base change of a tensor product,
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_unit_tmul`.

That inner layer is stated for the two pullbacks at the ring spelling
`commRingSheaf X.J (inverseImageStructureCommRing f) _`, not at the
`Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf` spelling that steps 4 to 6 are declared
with. The two are the same sheaf of rings, but a goal mixing them is not type-correct at the
transparency `rw` does its motive check at, so the statement is written at the spelling the
universal property of the tensor product over `f⁻¹O_D` produces its pairings in, and every step
of the proof is a term.

What the composition law still needs beyond the unit formula is one rewriting and one coherence.
The rewriting is done:
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit` puts it in the
shape `q ↦ (η_F × η_G) ≫ f_*q`, by
`Stacks.SheafOfModules.homEquiv_prodComparison_prodMap_comp` — which turns the transpose of a
product comparison followed by a product of two morphisms into the product of the two transposes —
together with
`Stacks.SheafOfModules.moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app`, which
identifies each transpose with a unit of Tag 03D7. The coherence left is the compatibility of
that one unit with composition, and that is
`Stacks.SheafOfModules.pullbackAdjPushforwardModules_unit_comp_pullbackModulesCompIso`.

With the unit formula and that coherence both in hand, each side of the composition law is
`prod.map u v` followed by a direct image of the pairing, and the two `u`'s differ by exactly one
component of the comparison of direct images. The bookkeeping that moves that component across the
product comparisons is `Stacks.SheafOfModules.prodMap_natIso_inv_prodComparison_map`, which is
built from the two Mathlib facts about `CategoryTheory.Limits.prodComparison` that it needs — that
the comparison of a composite functor is the composite of the two comparisons, and that the
comparison is natural in the functor.

`Stacks.SheafOfModules.prodMap_natIso_inv_prodComparison_map_comp` assembles those three inputs
into a single identity between the two routes, with the two routes' factors supplied and the
component of the comparison of direct images written outermost. Both shapes are deliberate: that
is exactly the shape each side of the law reaches once the unit formula has been applied to it, so
the law follows from the identity by a term and needs no rewriting at all. A term is what it has
to be. The product comparisons carry `CategoryTheory.Limits.HasBinaryProduct` and
`CategoryTheory.IsIso` arguments that are fixed in the statement of the unit formula on one side
and synthesized afresh at a rewrite site on the other, so the two sides can print identically and
still not be matched by `rw`, which compares them up to reducibility; a term is checked up to
definitional equality and does not care.

That gives `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_prodMap_comp`, the composition law
for the inverse of the base change of pairings;
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_comp` reads it forwards, and feeding that to
`Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_iff` gives
`Stacks.SheafOfModules.pullbackTensorHomEquiv_comp`, the composition law for the chain of
Tag 03EL itself.

Downstream of the composition law for the base change of pairings lies the composition law for
the canonical map of Tag 0GMX; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

/-! ## The direct image of a pairing, transported along a comparison of composites -/

section ProdComparisonTransport

/-- The inverse of the comparison isomorphism of a product-preserving functor is the inverse of
the product comparison, the two being the same morphism under
`CategoryTheory.Limits.PreservesLimitPair.iso_hom`. This is the bridge between the spelling the
value formulas of this file use and the spelling Mathlib's naturality lemmas for the product
comparison are stated in. -/
theorem preservesLimitPair_iso_inv {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (H : C ⥤ D) (A B : C) [HasBinaryProduct A B] [HasBinaryProduct (H.obj A) (H.obj B)]
    [PreservesLimit (pair A B) H] :
    (PreservesLimitPair.iso H A B).inv = inv (prodComparison H A B) :=
  (IsIso.inv_eq_of_hom_inv_id (PreservesLimitPair.iso H A B).hom_inv_id).symm

/-- **The image of a morphism out of a binary product, read on the product of the images,
transported along a comparison of a composite functor with a third one.** Let `K`, `L` and `M`
be functors with `θ : K ⋙ L ≅ M`, let `n : A ⨯ B ⟶ T`, and suppose the three relevant product
comparisons are isomorphisms. Reading `n` through `M` on the product of the `M`-images and then
transporting the two factors along `θ` is reading it through `K` and then through `L`, and
transporting the value along `θ`.

This is the only fact beyond the compatibility of the unit of Tag 03D7 with composition that the
composition law for the base change of bilinear pairings needs; it is where the component of the
comparison of direct images attached to each of the two source modules is traded for the one
attached to the sheaf of values. It is
`CategoryTheory.Limits.prodComparison_natural_of_natTrans` — the naturality of the product
comparison in the functor — together with
`CategoryTheory.Limits.prodComparison_comp` — the product comparison of a composite — and the
naturality of `θ` at `n`. -/
theorem prodMap_natIso_inv_prodComparison_map {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {E : Type u''} [Category.{v''} E] [HasBinaryProducts C]
    [HasBinaryProducts D] [HasBinaryProducts E] {K : C ⥤ D} {L : D ⥤ E} {M : C ⥤ E}
    (θ : K ⋙ L ≅ M) {A B T : C}
    [IsIso (prodComparison K A B)] [IsIso (prodComparison M A B)]
    [IsIso (prodComparison L (K.obj A) (K.obj B))] (n : A ⨯ B ⟶ T) :
    prod.map (θ.hom.app A) (θ.hom.app B) ≫ inv (prodComparison M A B) ≫ M.map n =
      inv (prodComparison L (K.obj A) (K.obj B)) ≫
        L.map (inv (prodComparison K A B) ≫ K.map n) ≫ θ.hom.app T := by
  have hcomp : prodComparison (K ⋙ L) A B =
      L.map (prodComparison K A B) ≫ prodComparison L (K.obj A) (K.obj B) :=
    prodComparison_comp K L
  have hKL : IsIso (prodComparison (K ⋙ L) A B) := by rw [hcomp]; infer_instance
  have hinvcomp : inv (prodComparison (K ⋙ L) A B) =
      inv (prodComparison L (K.obj A) (K.obj B)) ≫ L.map (inv (prodComparison K A B)) := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [hcomp, Category.assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp, IsIso.hom_inv_id]
    exact L.map_id _
  have hnat : θ.hom.app (A ⨯ B) ≫ prodComparison M A B =
      prodComparison (K ⋙ L) A B ≫ prod.map (θ.hom.app A) (θ.hom.app B) :=
    prodComparison_natural_of_natTrans θ.hom
  have hmove : prod.map (θ.hom.app A) (θ.hom.app B) ≫ inv (prodComparison M A B) =
      inv (prodComparison (K ⋙ L) A B) ≫ θ.hom.app (A ⨯ B) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hnat.symm
  rw [← Category.assoc, hmove, Category.assoc, ← θ.hom.naturality n, hinvcomp]
  simp only [Category.assoc, Functor.comp_map, Functor.map_comp]

/-- **The two routes compared, with their factors supplied.** Let `K`, `L` and `M` be functors
with `θ : K ⋙ L ≅ M`, let `n : A ⨯ B ⟶ T`, and let `uF : A' ⟶ A` and `uG : B' ⟶ B` be morphisms
to be applied in the two source variables before `n`. Suppose the two morphisms `cF`, `cG` with
which the `M`-route enters the product of the `M`-images factor, after the `M`-images of `uF` and
`uG`, as the morphisms `aF`, `aG` with which the `L`-route enters, followed by the `L`-images of
the morphisms `bF`, `bG` with which the `K`-route enters and by the component of `θ`. Then the
two routes agree: reading `prod.map uF uG ≫ n` through `M` is reading `n` through `K`, then
through `L`, and transporting the value along `θ`.

This is `Stacks.SheafOfModules.prodMap_natIso_inv_prodComparison_map` with the precomposition
`prod.map uF uG` pushed across the product comparison of `M` by
`CategoryTheory.Limits.prodComparison_inv_natural` and the factorisations `hF`, `hG` used to
split the two entering morphisms, the resulting products of composites being merged and
unmerged by `CategoryTheory.Limits.prod.map_map`.

The component of `θ` is written outermost on the right-hand side because that is the shape the
composition law for the base change of bilinear pairings reaches: there the composite of the two
base changes is a pairing in its own right, and the comparison of direct images is applied to it
afterwards. -/
theorem prodMap_natIso_inv_prodComparison_map_comp {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {E : Type u''} [Category.{v''} E] [HasBinaryProducts C]
    [HasBinaryProducts D] [HasBinaryProducts E] {K : C ⥤ D} {L : D ⥤ E} {M : C ⥤ E}
    (θ : K ⋙ L ≅ M) {A B T A' B' : C} {A₁ B₁ : D} {F' G' : E}
    [IsIso (prodComparison K A B)] [IsIso (prodComparison M A B)]
    [IsIso (prodComparison M A' B')] [IsIso (prodComparison L (K.obj A) (K.obj B))]
    [IsIso (prodComparison L A₁ B₁)]
    (uF : A' ⟶ A) (uG : B' ⟶ B) (aF : F' ⟶ L.obj A₁) (aG : G' ⟶ L.obj B₁)
    (bF : A₁ ⟶ K.obj A) (bG : B₁ ⟶ K.obj B) (cF : F' ⟶ M.obj A') (cG : G' ⟶ M.obj B')
    (hF : cF ≫ M.map uF = aF ≫ L.map bF ≫ θ.hom.app A)
    (hG : cG ≫ M.map uG = aG ≫ L.map bG ≫ θ.hom.app B)
    (n : A ⨯ B ⟶ T) :
    prod.map cF cG ≫ inv (prodComparison M A' B') ≫ M.map (prod.map uF uG ≫ n) =
      (prod.map aF aG ≫ inv (prodComparison L A₁ B₁) ≫
        L.map (prod.map bF bG ≫ inv (prodComparison K A B) ≫ K.map n)) ≫ θ.hom.app T := by
  rw [Category.assoc (prod.map aF aG), Category.assoc (inv (prodComparison L A₁ B₁)),
    M.map_comp, prodComparison_inv_natural_assoc M uF uG,
    ← Category.assoc (prod.map cF cG), prod.map_map, hF, hG,
    L.map_comp (prod.map bF bG) (inv (prodComparison K A B) ≫ K.map n),
    Category.assoc (L.map (prod.map bF bG)),
    prodComparison_inv_natural_assoc L bF bG,
    ← prodMap_natIso_inv_prodComparison_map θ n,
    ← Category.assoc (prod.map aF aG), prod.map_map,
    ← Category.assoc (prod.map (aF ≫ L.map bF) (aG ≫ L.map bG)), prod.map_map,
    Category.assoc aF (L.map bF) (θ.hom.app A), Category.assoc aG (L.map bG) (θ.hom.app B)]

end ProdComparisonTransport

/-! ## The chain of Tag 03EL regrouped into four links -/

section Regroup

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The fourth link of the regrouped chain of Tag 03EL**:
`Bilin_{O_C}(f^*F × f^*G, N) = Hom_{O_C}(f^*F ⊗_{O_C} f^*G, N)`, the universal property of the
tensor product sheaf of Tag 05NA over the structure sheaf of the *source*, at the two pullbacks.

This is the link whose two readings cancel on a composite route: it is the same construction as
`Stacks.SheafOfModules.pullbackTensorStep2` for a further morphism out of the source, which is
`Stacks.SheafOfModules.pullbackTensorStep2_eq_stepTarget_symm`. -/
def pullbackTensorStepTarget :
    { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj F) ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q } ≃
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :=
  bilinearEquivTensorSheafHom (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
    (F := (f.pullbackModules).obj F) (G := (f.pullbackModules).obj G) (N := N)

/-- **The base change of bilinear pairings along a morphism of ringed topoi**,
`Bilin_{O_D}(F × G, f_*N) ≃ Bilin_{O_C}(f^*F × f^*G, N)`: the third link of the regrouped chain
of Tag 03EL, and the only one of the four whose compatibility with composition is not available.

It is steps 3 to 6 of the chain of Tag 03EL — the transport of pairings along the inverse image,
the universal property of the tensor product over `f⁻¹O_D`, the extension-restriction adjunction
of Tag 03CZ and the base change of a tensor product — with the universal property of the tensor
product over `O_C` undone by `Stacks.SheafOfModules.pullbackTensorStepTarget`. Those four steps
are exactly the ones a composite route does not meet, and reading them as this one bijection
between pairings is what makes the two routes correspond. -/
def pullbackTensorBilinEquiv :
    { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ((pushforwardModules f).obj N) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q } ≃
      { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj F) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q } :=
  ((pullbackTensorStep3 f F G N).trans ((pullbackTensorStep4 f F G N).trans
    ((pullbackTensorStep5 f F G N).trans (pullbackTensorStep6 f F G N)))).trans
      (pullbackTensorStepTarget f F G N).symm

/-- **The chain of bijections of Tag 03EL is the regrouped four-link chain**: the adjunction of
Tag 03D7, the universal property of the tensor product over `O_D`, the base change of bilinear
pairings, and the universal property of the tensor product over `O_C`. The last four steps of
the original chain are the third link followed by the fourth, so nothing about the comparison of
Tag 03EL is changed by the regrouping. -/
theorem pullbackTensorHomEquiv_eq_regrouped :
    pullbackTensorHomEquiv f F G N =
      (pullbackTensorStep1 f F G N).trans ((pullbackTensorStep2 f F G N).trans
        ((pullbackTensorBilinEquiv f F G N).trans (pullbackTensorStepTarget f F G N))) := by
  rw [pullbackTensorBilinEquiv, Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]
  rfl

/-- The chain of bijections of Tag 03EL, applied to a morphism, read through the four links of
the regrouping. -/
theorem pullbackTensorHomEquiv_apply
    (h : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        f.pullbackModules).obj (F, G) ⟶ N) :
    pullbackTensorHomEquiv f F G N h =
      pullbackTensorStepTarget f F G N (pullbackTensorBilinEquiv f F G N
        (pullbackTensorStep2 f F G N (pullbackTensorStep1 f F G N h))) := by
  rw [pullbackTensorHomEquiv_eq_regrouped]; rfl

/-- **The extension-of-scalars half of the base change of bilinear pairings**: steps 4 to 6 of
the chain of Tag 03EL with the universal property of the tensor product over `O_C` undone, so
`Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|) ≃ Bilin_{O_C}(f^*F × f^*G, N)`.

Its type is *derived* from the three steps rather than written out: the sheaf of rings `f⁻¹O_D`
has two spellings —
`inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)`, which the steps
are declared with, and the `commRingSheaf` of `inverseImageStructureCommRing f`, which
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom` produces — and a re-typed signature makes
the elaborator cross between them inside a `Subtype` of a `Hom`, which exceeds the heartbeat
budget outright. -/
def pullbackTensorExtendBilinEquiv :=
  ((pullbackTensorStep4 f F G N).trans ((pullbackTensorStep5 f F G N).trans
    (pullbackTensorStep6 f F G N))).trans (pullbackTensorStepTarget f F G N).symm

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The base change of bilinear pairings is the transport along the inverse image followed by
the extension of scalars**: step 3 of the chain of Tag 03EL, then
`Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv`. -/
theorem pullbackTensorBilinEquiv_eq :
    pullbackTensorBilinEquiv f F G N =
      (pullbackTensorStep3 f F G N).trans (pullbackTensorExtendBilinEquiv f F G N) := by
  rw [pullbackTensorBilinEquiv, pullbackTensorExtendBilinEquiv]
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The inverse of the base change of bilinear pairings, with its outer layer written out.**
A pairing over `O_C` on the two pullbacks is carried back to a pairing over `O_D` into `f_*N` by
undoing the extension of scalars and then applying the bijection of Tag 03D3.

With this, the outer layer of the expected unit formula for the base change of pairings is
already available: `Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe_eq_unit_comp`
writes the right-hand side here as the unit of `f⁻¹ ⊣ f_*` followed by the direct image of the
pairing precomposed with the product comparison of `f⁻¹`. What is left of that formula is the
inner layer, the value of `Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv`'s inverse. -/
theorem pullbackTensorBilinEquiv_symm_apply
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((f.pullbackModules).obj F) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    (pullbackTensorBilinEquiv f F G N).symm q =
      inverseImageBilinearEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F G
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)
        ((pullbackTensorExtendBilinEquiv f F G N).symm q) := by
  rw [pullbackTensorBilinEquiv_eq]
  rfl

/-- The adjunction of Tag 03CZ that step 5 of the chain of Tag 03EL transposes under: extension
of scalars along `f♯` is left adjoint to restriction of scalars. -/
abbrev pullbackExtendAdj :=
  f.extendRestrictScalarsFSharpAdjunction

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **Steps 5 and 6 of the chain of Tag 03EL, traversed backwards, are the unit of Tag 03CZ
followed by the base change of a tensor product.** Given a bilinear pairing `q` over `O_C` on the
two pullbacks, read it as a morphism out of `f^*F ⊗_{O_C} f^*G` by the fourth link of the
regrouped chain; then undoing step 6 and step 5 gives the composite

`f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G ⟶ (f^*F ⊗_{O_C} f^*G)| ⟶ N|`

whose first factor is the unit of the extension-restriction adjunction at the tensor product over
`f⁻¹O_D`, read through the comparison of Stacks 03EL's step 4.

This is the normalization the value formula for
`Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv` starts from: it removes steps 5 and 6 at
once and leaves an expression built only from the Tag 03CZ unit and
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`, which is exactly what
`Stacks.Sheaves.RingedToposModules.sheafificationUnit_comp_extendScalarsTensorIso_hom_val`
computes on a pure tensor. It needs no step of its own for the inverse of step 6: that inverse is
`CategoryTheory.Iso.homFromEquiv` run backwards, which is composition with the hom, so the
hom-equivalence of Tag 03CZ absorbs it. -/
theorem pullbackTensorStep5_symm_step6_symm_stepTarget
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((f.pullbackModules).obj F) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    (pullbackTensorStep5 f F G N).symm ((pullbackTensorStep6 f F G N).symm
        (pullbackTensorStepTarget f F G N q)) =
      (pullbackExtendAdj f).unit.app (inverseImageTensorSheaf f
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)) ≫
        (SheafOfModules.restrictScalars
            (commRingSheafMap X.J (fSharpCommRing f)
              (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).map
          ((extendScalarsTensorIso (fSharpCommRing f)
              (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).hom ≫
            pullbackTensorStepTarget f F G N q) :=
  (pullbackExtendAdj f).homEquiv_unit _ _ _

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The inner layer of the unit formula for the base change of bilinear pairings**: the inverse
of `Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv` carries a pairing `q` over `O_C` on the
two pullbacks to `q` precomposed, in each variable, with the unit `ε : f⁻¹F ⟶ (f^*F)|` of the
extension-restriction adjunction of Tag 03CZ.

Together with
`Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe_eq_unit_comp`, which is the outer
layer, and the splitting `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply`, this is the
unit formula for the inverse of `Stacks.SheafOfModules.pullbackTensorBilinEquiv`.

Both sides are pairings, so the identity is checked on a pair of local sections by
`Stacks.SheafOfModules.pairing_ext` — instantiated at the sheaf of rings
`commRingSheaf X.J (inverseImageStructureCommRing f) _`, the spelling in which the universal
property of the tensor product over `f⁻¹O_D` produces its pairings. On a pair of sections the
left-hand side is read off by `Stacks.SheafOfModules.pairingApp_bilinearEquivTensorSheafHom_symm`
after `Stacks.SheafOfModules.pullbackTensorStep5_symm_step6_symm_stepTarget` has removed steps 5
and 6; what is left is exactly
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_unit_tmul`, the pure-tensor
identity for step 4, followed by
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_val_app_unit_tmul` for the fourth link. -/
theorem pullbackTensorExtendBilinEquiv_symm_apply_coe
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((f.pullbackModules).obj F) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    ((pullbackTensorExtendBilinEquiv f F G N).symm q).1 =
      prod.map
          ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
          ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))) ≫
        q.1 := by
  refine pairing_ext (commRingSheaf X.J (inverseImageStructureCommRing f)
    (isSheaf_inverseImageStructureCommRing f)) (fun U a b ↦ ?_)
  refine (pairingApp_bilinearEquivTensorSheafHom_symm
      ((pullbackTensorStep5 f F G N).symm ((pullbackTensorStep6 f F G N).symm
        (pullbackTensorStepTarget f F G N q))) U a b).trans ?_
  refine (CategoryTheory.congr_fun
      (congrArg (fun m ↦ PresheafOfModules.Hom.app (SheafOfModules.Hom.val m) U)
        (pullbackTensorStep5_symm_step6_symm_stepTarget f F G N q)) _).trans ?_
  refine (congrArg
      (fun z ↦ (ConcreteCategory.hom ((pullbackTensorStepTarget f F G N q).val.app U)) z)
      (extendScalarsTensorIso_hom_val_app_unit_tmul (fSharpCommRing f)
        (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
        ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) U a b)).trans ?_
  refine (bilinearEquivTensorSheafHom_val_app_unit_tmul (A := X.O.obj)
      (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
      (F := (f.pullbackModules).obj F) (G := (f.pullbackModules).obj G) (N := N) q U
      ((((pullbackExtendAdj f).unit.app
          ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)).val.app U).hom a)
      ((((pullbackExtendAdj f).unit.app
          ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).val.app U).hom
        b)).trans ?_
  refine Eq.symm (((Sheaf.sectionsFunctor X.J U).map_comp_apply
      (prod.map
        ((moduleSheafFunctor
            (commRingSheaf X.J (inverseImageStructureCommRing f)
              (isSheaf_inverseImageStructureCommRing f))).map
          ((pullbackExtendAdj f).unit.app
            ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
        ((moduleSheafFunctor
            (commRingSheaf X.J (inverseImageStructureCommRing f)
              (isSheaf_inverseImageStructureCommRing f))).map
          ((pullbackExtendAdj f).unit.app
            ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))))
      q.1 (Functor.prodObjMk a b)).trans
    (congrArg ((Sheaf.sectionsFunctor X.J U).map q.1) ?_))
  refine (Functor.map_prodMap_apply
    ((moduleSheafFunctor
        (commRingSheaf X.J (inverseImageStructureCommRing f)
          (isSheaf_inverseImageStructureCommRing f))).map
      ((pullbackExtendAdj f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
    ((moduleSheafFunctor
        (commRingSheaf X.J (inverseImageStructureCommRing f)
          (isSheaf_inverseImageStructureCommRing f))).map
      ((pullbackExtendAdj f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))
    (Functor.prodObjMk a b)).trans ?_
  rw [Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The unit formula for the base change of bilinear pairings.** The inverse of
`Stacks.SheafOfModules.pullbackTensorBilinEquiv` carries a pairing `q` over `O_C` on the two
pullbacks to the unit of `f⁻¹ ⊣ f_*` followed by the direct image of `q` precomposed with the
product comparison of `f⁻¹` and, in each variable, with the unit of Tag 03CZ.

This is the two layers of
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply` assembled:
`Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe_eq_unit_comp` supplies the unit of
Tag 03D3 and the product comparison, and
`Stacks.SheafOfModules.pullbackTensorExtendBilinEquiv_symm_apply_coe` supplies the two units of
Tag 03CZ. Every factor of the composite is a morphism with a known value formula, which is what
the composition law for the base change of pairings has to be checked against. -/
theorem pullbackTensorBilinEquiv_symm_apply_coe_eq_unit_comp
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((f.pullbackModules).obj F) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    ((pullbackTensorBilinEquiv f F G N).symm q).1 =
      f.toToposHom.adj.unit.app
          (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
              moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
        f.toToposHom.pushforward.map
          (prodComparison f.toToposHom.inverseImage
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
            (prod.map
                ((moduleSheafFunctor
                    (commRingSheaf X.J (inverseImageStructureCommRing f)
                      (isSheaf_inverseImageStructureCommRing f))).map
                  ((pullbackExtendAdj f).unit.app
                    ((inverseImageModules f.toToposHom
                        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
                ((moduleSheafFunctor
                    (commRingSheaf X.J (inverseImageStructureCommRing f)
                      (isSheaf_inverseImageStructureCommRing f))).map
                  ((pullbackExtendAdj f).unit.app
                    ((inverseImageModules f.toToposHom
                        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G))) ≫
              q.1)) := by
  rw [pullbackTensorBilinEquiv_symm_apply, inverseImageBilinearEquiv_apply_coe_eq_unit_comp,
    pullbackTensorExtendBilinEquiv_symm_apply_coe]
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The unit of the adjunction of Tag 03D7, on underlying sheaves of sets, is the unit of
Tag 03D3 followed by the direct image of the unit of Tag 03CZ.** The adjunction of Tag 03D7 is
the adjunction of Tag 03D3 composed with the extension-restriction adjunction of Tag 03CZ, so its
unit is the composite of the two units; on underlying sheaves of sets the first of them is the
unit of `f⁻¹ ⊣ f_*`, because the hom-set bijection of Tag 03D3 is the transpose of the underlying
morphism of sheaves of sets.

This is what identifies the two factors
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply_coe_eq_unit_comp` produces — the unit
of Tag 03D3 and the unit of Tag 03CZ — with the single unit of Tag 03D7, whose compatibility with
composition is `Stacks.Sheaves.RingedToposModules.unit_pullbackModulesCompIso_hom_app`. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app :
    (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F) =
      f.toToposHom.adj.unit.app (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ≫
        f.toToposHom.pushforward.map
          ((moduleSheafFunctor
              (commRingSheaf X.J (inverseImageStructureCommRing f)
                (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F))) := by
  have h₁ : (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((inverseImageAdjDirectImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).unit.app F) =
      f.toToposHom.adj.unit.app (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) := by
    show (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (toposModulesHomEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F
          ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) (𝟙 _)) = _
    rw [moduleSheafFunctor_map_toposModulesHomEquiv]
    exact f.toToposHom.adj.homEquiv_id _
  refine ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp
      ((inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).unit.app F)
      ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackExtendAdj f).unit.app
          ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))).trans ?_
  refine (congrArg (fun m ↦ m ≫
      (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackExtendAdj f).unit.app
          ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))) h₁).trans ?_
  exact congrArg
    (fun m ↦ f.toToposHom.adj.unit.app
        (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ≫ m)
    (moduleSheafFunctor_map_directImageModules_map f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pullbackExtendAdj f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The unit formula for the base change of bilinear pairings, in the form Stacks states it**:
the inverse of `Stacks.SheafOfModules.pullbackTensorBilinEquiv` carries a pairing `q` over `O_C`
to `(η_F × η_G) ≫ f_*q`, with `η` the unit of the adjunction of Tag 03D7 on modules. The direct
image preserves binary products, so `f_*q` is read on the product of the two direct images
through the inverse of that product comparison.

This is `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply_coe_eq_unit_comp` with the
unit of Tag 03D3 and the two units of Tag 03CZ collected into the one unit of Tag 03D7:
`Stacks.SheafOfModules.homEquiv_prodComparison_prodMap_comp` turns the transpose of a product
comparison followed by a product of two morphisms into the product of the two transposes, and
`Stacks.SheafOfModules.moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app` identifies
each transpose with a unit of Tag 03D7. In this form the composition law is the compatibility of
that one unit with composition. -/
theorem pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((f.pullbackModules).obj F) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    ((pullbackTensorBilinEquiv f F G N).symm q).1 =
      prod.map
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app F))
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app G)) ≫
        ((PreservesLimitPair.iso f.toToposHom.pushforward
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj F))
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                  ((f.pullbackModules).obj G))).inv ≫
          f.toToposHom.pushforward.map q.1) := by
  have hn : prodComparison f.toToposHom.pushforward
          (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj F))
          (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj G)) ≫
        ((PreservesLimitPair.iso f.toToposHom.pushforward
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj F))
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                  ((f.pullbackModules).obj G))).inv ≫
          f.toToposHom.pushforward.map q.1) =
      f.toToposHom.pushforward.map q.1 := by
    rw [← PreservesLimitPair.iso_hom]
    exact Iso.hom_inv_id_assoc _ _
  rw [moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app f F,
    moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app f G]
  exact (pullbackTensorBilinEquiv_symm_apply_coe_eq_unit_comp f F G N q).trans
    (homEquiv_prodComparison_prodMap_comp f.toToposHom.adj
      ((moduleSheafFunctor
          (commRingSheaf X.J (inverseImageStructureCommRing f)
            (isSheaf_inverseImageStructureCommRing f))).map
        ((pullbackExtendAdj f).unit.app
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)))
      ((moduleSheafFunctor
          (commRingSheaf X.J (inverseImageStructureCommRing f)
            (isSheaf_inverseImageStructureCommRing f))).map
        ((pullbackExtendAdj f).unit.app
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)))
      q.1
      ((PreservesLimitPair.iso f.toToposHom.pushforward
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj F))
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                ((f.pullbackModules).obj G))).inv ≫
        f.toToposHom.pushforward.map q.1) hn)

/-- **The chain of Tag 03EL carries its own comparison morphism to the identity.** The comparison
of Tag 03EL is the preimage of the identity under the chain of bijections at the tensor product
of the two pullbacks, `Stacks.SheafOfModules.pullbackTensorIso_hom_app`, so the chain sends it to
that identity.

The sheaf of values is named at the spelling
`(Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).obj (f^*F, f^*G)`, which is
the one the composition law is stated at, rather than the
`((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (f^*F)).obj (f^*G)` of
`Stacks.SheafOfModules.pullbackTensorIso_hom_app`. The two are definitionally equal only at
default transparency, so the single crossing between them is paid here, inside one `exact`, and
every consumer is spared it. -/
lemma pullbackTensorHomEquiv_pullbackTensorIso_hom :
    pullbackTensorHomEquiv f F G
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
        ((pullbackTensorIso f).hom.app (F, G)) =
      𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)) := by
  refine ((pullbackTensorHomEquiv f F G
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
      ((f.pullbackModules).obj F,
        (f.pullbackModules).obj G))).eq_symm_apply).1 ?_
  exact pullbackTensorIso_hom_app f F G

/-- **The chain of Tag 03EL collapses its own comparison morphism.** Applying the chain of
bijections at a sheaf of values `N` to the comparison of Tag 03EL followed by a morphism
`f^*F ⊗_{O_C} f^*G ⟶ N` returns that morphism.

The chain is natural in the sheaf of values, so it carries the composite to the chain of the
comparison composed with the morphism, and the chain of the comparison is the identity by
`Stacks.SheafOfModules.pullbackTensorHomEquiv_pullbackTensorIso_hom`. This is the step by which an
identity between two readings of the chain becomes an identity between morphisms, as in
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`. -/
lemma pullbackTensorHomEquiv_pullbackTensorIso_hom_comp
    (ρ : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
      ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    pullbackTensorHomEquiv f F G N ((pullbackTensorIso f).hom.app (F, G) ≫ ρ) = ρ := by
  refine (pullbackTensorHomEquiv_naturality
    (N := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
      ((f.pullbackModules).obj F, (f.pullbackModules).obj G))
    f F G ((pullbackTensorIso f).hom.app (F, G)) ρ).trans ?_
  exact (congrArg (· ≫ ρ) (pullbackTensorHomEquiv_pullbackTensorIso_hom f F G)).trans
    (Category.id_comp ρ)

end Regroup

/-! ## The two routes along a composite, and the cancellations -/

section ChainComp

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
  (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The transpose across `φ` of a morphism out of `φ^*ψ^*(F ⊗_{O_E} G)`. Both routes along the
composite begin by making this transposition, and the composite route makes it twice — once here
and once, inversely, when the chain of `φ` is applied — which is the first of the two
cancellations. -/
def pullbackTensorCompTranspose
    (ρ : (φ.pullbackModules).obj ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) ⟶ N) :
    (ψ.pullbackModules).obj (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ⟶
      (pushforwardModules φ).obj N :=
  (pullbackAdjPushforwardModules φ).homEquiv
    ((ψ.pullbackModules).obj (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) N ρ

/-- **The bilinear pairing over `O_E` that both routes start from**: transpose a morphism out of
`φ^*ψ^*(F ⊗_{O_E} G)` across `φ` and then across `ψ`, and read the result as a pairing by the
universal property of the tensor product over `O_E`. These are the first two links of both
routes, which `Stacks.SheafOfModules.pullbackTensorStep1_comp` and
`Stacks.SheafOfModules.pullbackTensorStep2_comp` identify with the first two links of `χ`'s
chain. -/
def pullbackTensorCompPairing
    (ρ : (φ.pullbackModules).obj ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) ⟶ N) :
    { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) F ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) G ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
          ((pushforwardModules ψ).obj ((pushforwardModules φ).obj N)) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) q } :=
  pullbackTensorStep2 ψ F G ((pushforwardModules φ).obj N)
    (pullbackTensorStep1 ψ F G ((pushforwardModules φ).obj N)
      (pullbackTensorCompTranspose φ ψ F G N ρ))

/-- The shared pairing is the one `Stacks.SheafOfModules.pullbackTensorStep2_comp` produces:
transposing across `φ` and then across `ψ` is transposing across the composite adjunction. -/
theorem pullbackTensorCompPairing_eq
    (ρ : (φ.pullbackModules).obj ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) ⟶ N) :
    pullbackTensorCompPairing φ ψ F G N ρ =
      pullbackTensorStep2 ψ F G ((pushforwardModules φ).obj N)
        (((pullbackAdjPushforwardModules ψ).comp
          (pullbackAdjPushforwardModules φ)).homEquiv
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
                (F, G)) N ρ) := by
  rw [Adjunction.comp_homEquiv]
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The cancellation that makes the two routes correspond.** Step 2 of the chain of `φ` at the
pair `(ψ^*F, ψ^*G)` is the inverse of the fourth link of the chain of `ψ` at `(F, G)`: both are
the universal property of the tensor product sheaf over `O_D` at that same pair and that same
sheaf of values `φ_*N`. It holds on the nose.

This is why the composite route, which traverses nine links where the chain of `χ` traverses
four, collapses to the length of the chain of `χ`. -/
theorem pullbackTensorStep2_eq_stepTarget_symm :
    pullbackTensorStep2 φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N =
      (pullbackTensorStepTarget ψ F G ((pushforwardModules φ).obj N)).symm := rfl

/-- **The composite route, collapsed.** Applying the chain of `ψ` to the transpose across `φ`,
transposing back and applying the chain of `φ` is the base change of the shared pairing along
`ψ` and then along `φ`, read by the universal property of the tensor product over `O_C`.

Both cancellations happen here: the transposition across `φ` against its inverse, and the fourth
link of `ψ`'s chain against the second link of `φ`'s. Of the nine links the composite route has
after the first two, only two survive, and they are the base changes of pairings along `ψ` and
along `φ`. -/
theorem pullbackTensorHomEquiv_comp_right
    (ρ : (φ.pullbackModules).obj ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) ⟶ N) :
    pullbackTensorHomEquiv φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N
        ((pullbackTensorStep1 φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N).symm
          (pullbackTensorHomEquiv ψ F G ((pushforwardModules φ).obj N)
            (pullbackTensorCompTranspose φ ψ F G N ρ))) =
      pullbackTensorStepTarget φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N
        (pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N
          (pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)
            (pullbackTensorCompPairing φ ψ F G N ρ))) := by
  rw [pullbackTensorHomEquiv_apply φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N,
    Equiv.apply_symm_apply,
    pullbackTensorHomEquiv_apply ψ F G ((pushforwardModules φ).obj N),
    pullbackTensorStep2_eq_stepTarget_symm, Equiv.symm_apply_apply, pullbackTensorCompPairing]

end ChainComp

/-! ## The composition law, reduced to one equation on bilinear pairings -/

section ChainCompLaw

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
  (χ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The unit of Tag 03D7 is compatible with composition.** The unit of `χ^* ⊣ χ_*` followed by
the direct image along `χ` of the comparison of pullbacks is the unit of `ψ^* ⊣ ψ_*` followed by
the direct image along `ψ` of the unit of `φ^* ⊣ φ_*`, followed by the comparison of direct
images.

This is `Stacks.Sheaves.RingedToposModules.unit_pullbackModulesCompIso_hom_app` with the
comparison of direct images carried from the source of the unit to the target: that statement
reads the unit of `χ^* ⊣ χ_*` through `CategoryTheory.Adjunction.ofNatIsoRight`, whose unit is the
unit of `χ^* ⊣ χ_*` followed by the inverse comparison, and the naturality of that inverse carries
it past the comparison of pullbacks, where `CategoryTheory.Iso.inv_hom_id_app` removes it. -/
theorem pullbackAdjPushforwardModules_unit_comp_pullbackModulesCompIso
    (M : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (pullbackAdjPushforwardModules χ).unit.app M ≫
        (pushforwardModules χ).map ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app M) =
      ((pullbackAdjPushforwardModules ψ).comp
            (pullbackAdjPushforwardModules φ)).unit.app M ≫
        (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app
          ((φ.pullbackModules).obj ((ψ.pullbackModules).obj M)) := by
  have hι : (Adjunction.ofNatIsoRight (pullbackAdjPushforwardModules χ)
        (pushforwardModulesCompIso φ ψ χ τ hτ).symm).unit.app M =
      (pullbackAdjPushforwardModules χ).unit.app M ≫
        (pushforwardModulesCompIso φ ψ χ τ hτ).inv.app ((χ.pullbackModules).obj M) := rfl
  rw [← unit_pullbackModulesCompIso_hom_app φ ψ χ τ hτ M, hι]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Category.comp_id]

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The unit of Tag 03D7 is compatible with composition, on underlying sheaves of sets.** This
is `Stacks.SheafOfModules.pullbackAdjPushforwardModules_unit_comp_pullbackModulesCompIso` read
through the forgetful functor to sheaves of sets, where the comparison of direct images becomes
`τ` itself and the unit of the composite adjunction becomes the unit along `ψ` followed by the
direct image along `ψ` of the unit along `φ`. This is the form the composition law for the base
change of bilinear pairings consumes, both sides of that law being built from pairings of
underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_unit_comp_pullbackModulesCompIso
    (M : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          ((pullbackAdjPushforwardModules χ).unit.app M) ≫
        χ.toToposHom.pushforward.map
          ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
            ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app M)) =
      (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          ((pullbackAdjPushforwardModules ψ).unit.app M) ≫
        ψ.toToposHom.pushforward.map
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
              ((pullbackAdjPushforwardModules φ).unit.app ((ψ.pullbackModules).obj M))) ≫
          τ.hom.app (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj M))) := by
  have h := congrArg (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    (pullbackAdjPushforwardModules_unit_comp_pullbackModulesCompIso φ ψ χ τ hτ M)
  simp only [Functor.map_comp, Adjunction.comp_unit_app,
    moduleSheafFunctor_map_pushforwardModules_map, Category.assoc] at h
  exact h

/-- **The route of `χ`'s own chain.** Applying the chain of Tag 03EL for `χ` to a morphism
precomposed with the comparison of pullbacks is applying the last two links of that chain — the
base change of pairings along `χ` and the universal property of the tensor product over `O_C` —
to the shared pairing, transported along the comparison of direct images.

The first two links are discharged by `Stacks.SheafOfModules.pullbackTensorStep1_comp` and
`Stacks.SheafOfModules.pullbackTensorStep2_comp`. -/
theorem pullbackTensorHomEquiv_comp_left
    (ρ : (ψ.pullbackModules ⋙ φ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ⟶ N) :
    pullbackTensorHomEquiv χ F G N
        ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ≫ ρ) =
      pullbackTensorStepTarget χ F G N (pullbackTensorBilinEquiv χ F G N
        ⟨(pullbackTensorCompPairing φ ψ F G N ρ).1 ≫
            (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
              ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N),
          (pullbackTensorCompPairing φ ψ F G N ρ).2.comp
            ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N)⟩) := by
  rw [pullbackTensorHomEquiv_apply χ F G N, pullbackTensorStep1_comp φ ψ χ τ hτ F G N ρ,
    pullbackTensorStep2_comp φ ψ χ τ hτ F G N, pullbackTensorCompPairing_eq]

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The fourth link of the regrouped chain is natural in its two source modules**, at the two
spellings the two routes along a composite use: precomposing a pairing on
`(φ^*ψ^*F, φ^*ψ^*G)` with the comparison of pullbacks in each variable and reading it over
`(χ^*F, χ^*G)` is reading it over `(φ^*ψ^*F, φ^*ψ^*G)` and precomposing with the tensor product
of the two comparisons. -/
theorem pullbackTensorStepTarget_precomp
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F)) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj G)) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    pullbackTensorStepTarget χ F G N
        ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
              ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F))
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
              ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)) ≫ q.1,
          q.2.precomp ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F)
            ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)⟩ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F,
            (pullbackModulesCompIso φ ψ χ τ hτ).hom.app G) :
            (((χ.pullbackModules).obj F, (χ.pullbackModules).obj G) :
              SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
              (φ.pullbackModules).obj ((ψ.pullbackModules).obj G))) ≫
        pullbackTensorStepTarget φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N q :=
  (bilinearEquivTensorSheafHom_precomp (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
      q ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F)
      ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)).trans
    (congrArg (fun morphism ↦ morphism ≫
        pullbackTensorStepTarget φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N q)
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.O
        ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F)
        ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)).symm)

/-- **The composition law for the chain of Tag 03EL is the composition law for the base change of
bilinear pairings.** The identity that the chain of `χ`, applied to a morphism precomposed with
the comparison of pullbacks, is the chain of `ψ` followed by the chain of `φ` — precomposed with
the tensor product of the two comparisons of pullbacks — holds exactly when the base change of
the shared pairing along `χ`, transported along the comparison of direct images, is its base
change along `ψ` and then along `φ`, transported along the comparison of pullbacks in each
variable.

Both sides of the left-hand identity are, by
`Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_left` and
`Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_right`, the fourth link of the regrouped chain
applied to the two pairings compared on the right, so the equivalence is injectivity of that
link. This is the whole of the composition law for Tag 03EL reduced to one equation between
pairings; see the implementation notes for what proving that equation still needs. -/
theorem pullbackTensorHomEquiv_comp_iff
    (ρ : (φ.pullbackModules).obj ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) ⟶ N) :
    pullbackTensorHomEquiv χ F G N
          ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj
                (F, G)) ≫ ρ) =
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
            (((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F,
              (pullbackModulesCompIso φ ψ χ τ hτ).hom.app G) :
              (((χ.pullbackModules).obj F, (χ.pullbackModules).obj G) :
                SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                  SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
              ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
                (φ.pullbackModules).obj ((ψ.pullbackModules).obj G))) ≫
          pullbackTensorHomEquiv φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N
            ((pullbackTensorStep1 φ ((ψ.pullbackModules).obj F)
                ((ψ.pullbackModules).obj G) N).symm
              (pullbackTensorHomEquiv ψ F G ((pushforwardModules φ).obj N)
                (pullbackTensorCompTranspose φ ψ F G N ρ))) ↔
      pullbackTensorBilinEquiv χ F G N
            ⟨(pullbackTensorCompPairing φ ψ F G N ρ).1 ≫
                (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
                  ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N),
              (pullbackTensorCompPairing φ ψ F G N ρ).2.comp
                ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N)⟩ =
        ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
                ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F))
              ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
                ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)) ≫
            (pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F)
              ((ψ.pullbackModules).obj G) N
                (pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)
                  (pullbackTensorCompPairing φ ψ F G N ρ))).1,
          (pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N
              (pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)
                (pullbackTensorCompPairing φ ψ F G N ρ))).2.precomp
            ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F)
            ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)⟩ := by
  rw [pullbackTensorHomEquiv_comp_left φ ψ χ τ hτ F G N ρ,
    pullbackTensorHomEquiv_comp_right φ ψ F G N ρ,
    ← pullbackTensorStepTarget_precomp φ ψ χ τ hτ F G N]
  exact Equiv.apply_eq_iff_eq _

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The composition law for the base change of bilinear pairings, for the inverse bijection.**
Let `q` be a pairing over `O_C` on the pullback along `φ` of the pullback along `ψ` of `F` and of
`G`. Transporting its two variables by the comparison of pullbacks and reading the result back
along `χ` is reading `q` back along `φ` and then along `ψ`, and following the result with the
comparison of direct images.

Both sides are computed by the unit formula
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit`, which turns each
of the three inverse bijections into a product of two units of Tag 03D7 followed by a direct
image of the pairing. What is left is then exactly
`Stacks.SheafOfModules.prodMap_natIso_inv_prodComparison_map_comp` for the comparison `τ` of the
direct images, with
`Stacks.SheafOfModules.moduleSheafFunctor_map_unit_comp_pullbackModulesCompIso` at `F` and at `G`
supplying its two factorisation hypotheses. The inverses of the product comparisons are brought
to the spelling that identity uses by
`Stacks.SheafOfModules.preservesLimitPair_iso_inv`. -/
theorem pullbackTensorBilinEquiv_symm_prodMap_comp
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F)) ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj G)) ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q }) :
    ((pullbackTensorBilinEquiv χ F G N).symm
        ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
              ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F))
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
              ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)) ≫ q.1,
          q.2.precomp ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F)
            ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)⟩).1 =
      ((pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)).symm
          ((pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F)
            ((ψ.pullbackModules).obj G) N).symm q)).1 ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N) := by
  rw [pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit χ F G N,
    pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit ψ F G
      ((pushforwardModules φ).obj N),
    pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit φ ((ψ.pullbackModules).obj F)
      ((ψ.pullbackModules).obj G) N,
    preservesLimitPair_iso_inv, preservesLimitPair_iso_inv, preservesLimitPair_iso_inv]
  exact prodMap_natIso_inv_prodComparison_map_comp τ
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F))
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G))
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((pullbackAdjPushforwardModules ψ).unit.app F))
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((pullbackAdjPushforwardModules ψ).unit.app G))
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((pullbackAdjPushforwardModules φ).unit.app ((ψ.pullbackModules).obj F)))
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((pullbackAdjPushforwardModules φ).unit.app ((ψ.pullbackModules).obj G)))
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((pullbackAdjPushforwardModules χ).unit.app F))
    ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((pullbackAdjPushforwardModules χ).unit.app G))
    (moduleSheafFunctor_map_unit_comp_pullbackModulesCompIso φ ψ χ τ hτ F)
    (moduleSheafFunctor_map_unit_comp_pullbackModulesCompIso φ ψ χ τ hτ G) q.1

/-- **The composition law for the base change of bilinear pairings.** The base change along `χ`
of the pairing both routes share, followed by the comparison of direct images, is its base change
along `ψ` and then along `φ`, with its two variables transported by the comparison of pullbacks.

This is `Stacks.SheafOfModules.pullbackTensorBilinEquiv_symm_prodMap_comp` read forwards, at the
pairing the right-hand side produces: the two inverse bijections there undo the two base changes
applied here, leaving the shared pairing. -/
theorem pullbackTensorBilinEquiv_comp
    (ρ : (φ.pullbackModules).obj ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) ⟶ N) :
    pullbackTensorBilinEquiv χ F G N
          ⟨(pullbackTensorCompPairing φ ψ F G N ρ).1 ≫
              (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
                ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N),
            (pullbackTensorCompPairing φ ψ F G N ρ).2.comp
              ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N)⟩ =
      ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
              ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F))
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
              ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)) ≫
          (pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F)
            ((ψ.pullbackModules).obj G) N
              (pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)
                (pullbackTensorCompPairing φ ψ F G N ρ))).1,
        (pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N
            (pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)
              (pullbackTensorCompPairing φ ψ F G N ρ))).2.precomp
          ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F)
          ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)⟩ := by
  have hundo : (pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)).symm
        ((pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F)
          ((ψ.pullbackModules).obj G) N).symm
          (pullbackTensorBilinEquiv φ ((ψ.pullbackModules).obj F)
            ((ψ.pullbackModules).obj G) N
            (pullbackTensorBilinEquiv ψ F G ((pushforwardModules φ).obj N)
              (pullbackTensorCompPairing φ ψ F G N ρ)))) =
      pullbackTensorCompPairing φ ψ F G N ρ := by
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact (Equiv.eq_symm_apply _).mp
    (Subtype.ext ((pullbackTensorBilinEquiv_symm_prodMap_comp φ ψ χ τ hτ F G N _).trans
      (congrArg (fun s ↦ s.1 ≫ (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N)) hundo)).symm)

/-- **The composition law for the chain of Tag 03EL.** The comparison of Tag 03EL for `χ` is the
comparison for `ψ` pulled back along `φ`, followed by the comparison for `φ`: applying the chain
of `χ` to a morphism out of `χ^*(F ⊗_{O_E} G)` precomposed with the comparison of pullbacks is
applying the chain of `ψ` to its transpose across `φ`, transposing back, applying the chain of
`φ`, and precomposing the result with the tensor product of the two comparisons of pullbacks.

This is `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp_iff` fed with
`Stacks.SheafOfModules.pullbackTensorBilinEquiv_comp`. -/
theorem pullbackTensorHomEquiv_comp
    (ρ : (φ.pullbackModules).obj ((ψ.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) ⟶ N) :
    pullbackTensorHomEquiv χ F G N
        ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ≫ ρ) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F,
            (pullbackModulesCompIso φ ψ χ τ hτ).hom.app G) :
            (((χ.pullbackModules).obj F, (χ.pullbackModules).obj G) :
              SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
              (φ.pullbackModules).obj ((ψ.pullbackModules).obj G))) ≫
        pullbackTensorHomEquiv φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G) N
          ((pullbackTensorStep1 φ ((ψ.pullbackModules).obj F)
              ((ψ.pullbackModules).obj G) N).symm
            (pullbackTensorHomEquiv ψ F G ((pushforwardModules φ).obj N)
              (pullbackTensorCompTranspose φ ψ F G N ρ))) :=
  (pullbackTensorHomEquiv_comp_iff φ ψ χ τ hτ F G N ρ).mpr
    (pullbackTensorBilinEquiv_comp φ ψ χ τ hτ F G N ρ)

/-! ### The composition law at the comparison morphism

The composition law above is an identity between two readings of the *chain of bijections*. The
comparison morphism of Tag 03EL is reached from the chain only by
`Stacks.SheafOfModules.pullbackTensorHomEquiv_symm_eq`, so carrying the law to the comparison is
a further step; it is taken here. This is the form every consumer that handles the comparison as
a morphism needs — among them the canonical map of Stacks 0GMX, which is built from
`(pullbackTensorIso _).inv.app` and is therefore out of reach of the chain-level law. -/

/-- The transpose across `φ` of the composite route's comparison. The composite route's morphism
out of `φ^*ψ^*(F ⊗_{O_E} G)` is `φ^*` of `ψ`'s comparison followed by `φ`'s comparison, and
transposing it across `φ` moves the first factor out of the pullback, leaving `ψ`'s comparison
followed by the transpose of `φ`'s. This is the naturality of the adjunction of Tag 03D7 in its
left variable, and it is the first of the two cancellations made concrete. -/
lemma pullbackTensorCompTranspose_pullbackTensorIso_hom :
    pullbackTensorCompTranspose φ ψ F G
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
            (φ.pullbackModules).obj ((ψ.pullbackModules).obj G)))
        ((φ.pullbackModules).map ((pullbackTensorIso ψ).hom.app (F, G)) ≫
          (pullbackTensorIso φ).hom.app
            ((ψ.pullbackModules).obj F, (ψ.pullbackModules).obj G)) =
      (pullbackTensorIso ψ).hom.app (F, G) ≫
        pullbackTensorStep1 φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G)
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
              (φ.pullbackModules).obj ((ψ.pullbackModules).obj G)))
          ((pullbackTensorIso φ).hom.app
            ((ψ.pullbackModules).obj F, (ψ.pullbackModules).obj G)) :=
  (pullbackAdjPushforwardModules φ).homEquiv_naturality_left _ _

/-- **Both cancellations of the composite route, at the comparison morphism.** Feeding the
composite route's comparison through the three remaining links of the composite route returns the
identity: `ψ`'s comparison cancels against the chain of `ψ`, and `φ`'s comparison against the
chain of `φ`, leaving nothing.

This is what makes the composition law for the comparison morphism follow from the chain-level
law with no residue. -/
lemma pullbackTensorHomEquiv_pullbackTensorIso_hom_cancel :
    pullbackTensorHomEquiv φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G)
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
          ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
            (φ.pullbackModules).obj ((ψ.pullbackModules).obj G)))
        ((pullbackTensorStep1 φ ((ψ.pullbackModules).obj F) ((ψ.pullbackModules).obj G)
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
              ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
                (φ.pullbackModules).obj ((ψ.pullbackModules).obj G)))).symm
          (pullbackTensorHomEquiv ψ F G
            ((pushforwardModules φ).obj
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
                  (φ.pullbackModules).obj ((ψ.pullbackModules).obj G))))
            (pullbackTensorCompTranspose φ ψ F G
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
                ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
                  (φ.pullbackModules).obj ((ψ.pullbackModules).obj G)))
              ((φ.pullbackModules).map ((pullbackTensorIso ψ).hom.app (F, G)) ≫
                (pullbackTensorIso φ).hom.app
                  ((ψ.pullbackModules).obj F, (ψ.pullbackModules).obj G))))) =
      𝟙 (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
          (φ.pullbackModules).obj ((ψ.pullbackModules).obj G))) := by
  rw [pullbackTensorCompTranspose_pullbackTensorIso_hom,
    pullbackTensorHomEquiv_pullbackTensorIso_hom_comp, Equiv.symm_apply_apply]
  exact pullbackTensorHomEquiv_pullbackTensorIso_hom φ ((ψ.pullbackModules).obj F)
    ((ψ.pullbackModules).obj G)

/-- **The composition law for the comparison morphism of Tag 03EL.** The comparison of Tag 03EL
for `χ`, followed by the tensor product of the two comparisons of pullbacks, is the comparison of
pullbacks at `F ⊗_{O_E} G`, followed by `φ^*` of the comparison for `ψ`, followed by the
comparison for `φ`.

This is `Stacks.SheafOfModules.pullbackTensorHomEquiv_comp` carried from the chain of bijections
to the comparison morphism: apply the chain of `χ` to both sides, where
`Stacks.SheafOfModules.pullbackTensorHomEquiv_pullbackTensorIso_hom_comp` collapses the left and
the chain-level law rewrites the right, and
`Stacks.SheafOfModules.pullbackTensorHomEquiv_pullbackTensorIso_hom_cancel` reduces the factor it
leaves behind to the identity. -/
theorem pullbackTensorIso_hom_app_comp :
    (pullbackTensorIso χ).hom.app (F, G) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F,
            (pullbackModulesCompIso φ ψ χ τ hτ).hom.app G) :
            (((χ.pullbackModules).obj F, (χ.pullbackModules).obj G) :
              SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            ((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
              (φ.pullbackModules).obj ((ψ.pullbackModules).obj G))) =
      (pullbackModulesCompIso φ ψ χ τ hτ).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ≫
        (φ.pullbackModules).map ((pullbackTensorIso ψ).hom.app (F, G)) ≫
          (pullbackTensorIso φ).hom.app
            ((ψ.pullbackModules).obj F, (ψ.pullbackModules).obj G) := by
  refine (pullbackTensorHomEquiv χ F G _).injective ?_
  rw [pullbackTensorHomEquiv_pullbackTensorIso_hom_comp, pullbackTensorHomEquiv_comp,
    pullbackTensorHomEquiv_pullbackTensorIso_hom_cancel, Category.comp_id]

/-- **The composition law for the comparison of Tag 03EL, read on the inverse comparison.**
Undoing `φ`'s comparison, then `φ^*` of `ψ`'s, then the comparison of pullbacks at
`F ⊗_{O_E} G`, is the tensor product of the two inverse comparisons of pullbacks followed by
undoing `χ`'s comparison.

This is `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` inverted, and it is the direction
the canonical map of Stacks 0GMX is built from: that map transposes
`(pullbackTensorIso _).inv.app _ ≫ _^*(ev)`, so a statement about it along a composite consumes
the law on the inverse comparison and not on the comparison itself. Both sides being composites
of isomorphisms, the two readings are inverse to one and the same isomorphism. -/
theorem pullbackTensorIso_inv_app_comp :
    (pullbackTensorIso φ).inv.app
          ((ψ.pullbackModules).obj F, (ψ.pullbackModules).obj G) ≫
        (φ.pullbackModules).map ((pullbackTensorIso ψ).inv.app (F, G)) ≫
          (pullbackModulesCompIso φ ψ χ τ hτ).inv.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (((pullbackModulesCompIso φ ψ χ τ hτ).inv.app F,
            (pullbackModulesCompIso φ ψ χ τ hτ).inv.app G) :
            (((φ.pullbackModules).obj ((ψ.pullbackModules).obj F),
              (φ.pullbackModules).obj ((ψ.pullbackModules).obj G)) :
              SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
                SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            ((χ.pullbackModules).obj F, (χ.pullbackModules).obj G)) ≫
        (pullbackTensorIso χ).inv.app (F, G) := by
  have h := congrArg Iso.inv
    (Iso.ext (α := (pullbackTensorIso χ).app (F, G) ≪≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).mapIso
          (Iso.prod ((pullbackModulesCompIso φ ψ χ τ hτ).app F)
            ((pullbackModulesCompIso φ ψ χ τ hτ).app G)))
      (β := (pullbackModulesCompIso φ ψ χ τ hτ).app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ≪≫
        (φ.pullbackModules).mapIso ((pullbackTensorIso ψ).app (F, G)) ≪≫
          (pullbackTensorIso φ).app
            ((ψ.pullbackModules).obj F, (ψ.pullbackModules).obj G))
      (pullbackTensorIso_hom_app_comp φ ψ χ τ hτ F G))
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.prod_inv] at h
  exact (Category.assoc _ _ _).symm.trans h.symm

end ChainCompLaw

end Stacks.SheafOfModules

end
