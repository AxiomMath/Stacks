module

public import StacksFrontier.AlgebraicGeometry.AffineOpensDirectedGlueHom
public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCoherence

/-!
# A compatible family of morphisms for a glueing datum built by peeling

`AlgebraicGeometry.AffineOpensGlue.ofRestrictIso` builds a glueing datum
`AlgebraicGeometry.AffineOpensGlue.ChartComparison` out of a family of isomorphisms
`θ h : mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE h)` along the inclusions of affine
opens, by peeling the pushforwards off; its companion
`AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso` reduces the cocycle condition of the
datum to the cocycle condition for `θ`.

This file does the same reduction for
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.IsCompatible`, the condition under which a
family of morphisms on the charts glues to a morphism of the glued sheaves of modules: a family
`α V : mod V ⟶ mod' V` commuting with the two families of isomorphisms it was peeled from is
compatible with the comparisons the peeling produces. With this, making the glued module
functorial in the datum takes only the naturality of `θ`, which is the actual mathematics.

## Main results

* `AlgebraicGeometry.AffineOpensGlue.isCompatible_of_restrictIso`: **the reduction.** A family of
  morphisms commuting with the restriction isomorphisms is compatible with the comparisons of
  `AlgebraicGeometry.AffineOpensGlue.compOfRestrictIso`.
* `AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso_at`: the same reduction asking for
  the cocycle condition only at the chain in question, and with the inequality in
  `AlgebraicGeometry.restrictLocal` spelled as the `comp_trans` field of a glueing datum spells
  it.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueIso_congr`: the glued isomorphism depends
  only on the family, the compatibility condition being a proposition.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueIso_refl` and
  `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueIso_trans`: **the glued isomorphism is
  functorial in the family**, which is
  `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom_id` and `glueHom_comp` read on
  isomorphisms.

## Implementation notes

Both peeling isomorphisms are natural in the module —
`AlgebraicGeometry.AffineOpensGlue.restrictPushforwardIso_hom_naturality` and
`AlgebraicGeometry.AffineOpensGlue.restrictPushforwardLeIso_hom_naturality` — and
`AlgebraicGeometry.AffineOpensGlue.pushRes` is exactly the restricted pushforward appearing in
both. So the compatibility square is the naturality of the outer peeling isomorphism, the
hypothesis on `θ`, and the naturality of the inner one, in that order, with nothing unfolded.

The cocycle conditions `hθ` and `hθ'` are carried as arguments only because
`AlgebraicGeometry.AffineOpensGlue.ofRestrictIso` needs them to form the two data; the proof does
not use them.

`AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso_at` exists because the universally
quantified `AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso` cannot be instantiated at
the determinant's family of comparisons: the kernel does not finish reconciling the two Π-types,
and reports `(kernel) deterministic timeout`. Asking for the cocycle condition at one chain
replaces that reconciliation by one equation, and spelling the inequality of
`AlgebraicGeometry.restrictLocal` as `show (V.1 : X.Opens) ≤ (V'.1 : X.Opens) from h` — the
spelling of the `comp_trans` field — removes the last reconciliation, so the field of a glueing
datum is a plain application of this lemma.

## References

* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AffineOpensGlue

variable {X : Scheme.{u}}

/-- **A family of morphisms commuting with the restriction isomorphisms is compatible with the
comparisons obtained by peeling.** Let `mod` and `mod'` be two families of sheaves of modules on
the affine opens of `X`, each equipped with a family of isomorphisms along the inclusions and the
cocycle condition for it, so that
`AlgebraicGeometry.AffineOpensGlue.ofRestrictIso` turns each into a glueing datum. A family of
morphisms `α V : mod V ⟶ mod' V` which commutes with the two families of isomorphisms satisfies
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.IsCompatible`, and therefore glues to a
morphism of the two glued sheaves of modules by
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom`.

The comparison of the peeled datum is the outer peeling isomorphism, the given isomorphism, and
the inverse of the inner peeling isomorphism; both peeling isomorphisms are natural in the
module, and the middle square is the hypothesis. -/
theorem isCompatible_of_restrictIso
    (mod mod' : ∀ V : X.affineOpens, ((V.1 : X.Opens) : Scheme.{u}).Modules)
    (θ : ∀ (V W : X.affineOpens) (h : V ≤ W),
      mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE (coe_le_coe h)))
    (hθ : ∀ (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W),
      (θ V V' h).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE (coe_le_coe h))).map (θ V' W h').hom ≫
          (restrictFunctorTransIso (coe_le_coe h) (coe_le_coe h')
            (coe_le_coe (h.trans h'))).hom.app (mod W) =
        (θ V W (h.trans h')).hom)
    (θ' : ∀ (V W : X.affineOpens) (h : V ≤ W),
      mod' V ≅ Scheme.Modules.restrict (mod' W) (X.homOfLE (coe_le_coe h)))
    (hθ' : ∀ (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W),
      (θ' V V' h).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE (coe_le_coe h))).map (θ' V' W h').hom ≫
          (restrictFunctorTransIso (coe_le_coe h) (coe_le_coe h')
            (coe_le_coe (h.trans h'))).hom.app (mod' W) =
        (θ' V W (h.trans h')).hom)
    (α : ∀ V : X.affineOpens, mod V ⟶ mod' V)
    (hα : ∀ (V W : X.affineOpens) (h : V ≤ W),
      (θ V W h).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE (coe_le_coe h))).map (α W) =
        α V ≫ (θ' V W h).hom) :
    ChartComparison.IsCompatible (D := ofRestrictIso mod θ hθ)
      (D' := ofRestrictIso mod' θ' hθ') α := by
  intro V W h
  have hout := restrictPushforwardIso_hom_naturality (α V)
  have hin := restrictPushforwardLeIso_hom_naturality (coe_le_coe h) (α W)
  have hinv : (restrictPushforwardLeIso (coe_le_coe h) (mod W)).inv ≫
      pushRes (V.1 : X.Opens) W (α W) =
      (Scheme.Modules.restrictFunctor (X.homOfLE (coe_le_coe h))).map (α W) ≫
        (restrictPushforwardLeIso (coe_le_coe h) (mod' W)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hin, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  change (compOfRestrictIso mod θ V W h).hom ≫ pushRes (V.1 : X.Opens) W (α W) =
    pushRes (V.1 : X.Opens) V (α V) ≫ (compOfRestrictIso mod' θ' V W h).hom
  dsimp only [compOfRestrictIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hinv, reassoc_of% hα V W h, ← Category.assoc, hout, Category.assoc]

/-! ### The cocycle condition at a single chain -/

/-- **The reduction lemma at a single chain of two inclusions.**
`AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso` asks for the cocycle condition for
`θ` at every chain; this asks for it only at the chain in question, which is the form in which the
condition is available when the family `θ` is a concrete construction.

The proof is the one of `comp_trans_of_restrictIso`, which uses the hypothesis only at that
chain. -/
theorem comp_trans_of_restrictIso_at
    (mod : ∀ V : X.affineOpens, ((V.1 : X.Opens) : Scheme.{u}).Modules)
    (θ : ∀ (V W : X.affineOpens) (h : V ≤ W),
      mod V ≅ Scheme.Modules.restrict (mod W) (X.homOfLE (coe_le_coe h)))
    (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W)
    (hθ : (θ V V' h).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (coe_le_coe h))).map (θ V' W h').hom ≫
        (restrictFunctorTransIso (coe_le_coe h) (coe_le_coe h')
          (coe_le_coe (h.trans h'))).hom.app (mod W) =
      (θ V W (h.trans h')).hom) :
    (compOfRestrictIso mod θ V V' h).hom ≫
        restrictLocal (compOfRestrictIso mod θ V' W h').hom
          (show (V.1 : X.Opens) ≤ (V'.1 : X.Opens) from h) =
      (compOfRestrictIso mod θ V W (h.trans h')).hom := by
  dsimp only [compOfRestrictIso]
  rw [restrictLocal_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [restrictPushforwardLeIso_inv_comp_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← restrictFunctorTransIso_hom_app_comp_inv (coe_le_coe h) (coe_le_coe h')
      (coe_le_coe (h.trans h')) (mod W),
    reassoc_of% hθ]

/-! ### The glued isomorphism is functorial -/

namespace ChartComparison

/-- **The glued isomorphism depends only on the family.** The compatibility condition is a
proposition, so two compatible families which are equal glue to the same isomorphism. -/
theorem glueIso_congr (D D' : ChartComparison X)
    {α β : ∀ V : X.affineOpens, D.mod V ≅ D'.mod V} (hαβ : α = β)
    (hα : IsCompatible fun V => (α V).hom) (hβ : IsCompatible fun V => (β V).hom) :
    D.glueIso D' α hα = D.glueIso D' β hβ := by
  subst hαβ
  rfl

/-- **The family of identity isomorphisms glues to the identity.** This is
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom_id`; the compatibility hypothesis is a
proposition, so the one supplied is the one that lemma uses. -/
theorem glueIso_refl (D : ChartComparison X)
    (hα : IsCompatible fun V : X.affineOpens => (Iso.refl (D.mod V)).hom) :
    D.glueIso D (fun V => Iso.refl (D.mod V)) hα = Iso.refl D.glued :=
  Iso.ext (glueHom_id D)

/-- **The family of composites glues to the composite isomorphism.** This is
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom_comp`; the compatibility hypothesis is a
proposition, so the one supplied is the one that lemma uses. -/
theorem glueIso_trans (D D' D'' : ChartComparison X)
    (α : ∀ V : X.affineOpens, D.mod V ≅ D'.mod V)
    (β : ∀ V : X.affineOpens, D'.mod V ≅ D''.mod V)
    (hα : IsCompatible fun V => (α V).hom) (hβ : IsCompatible fun V => (β V).hom)
    (hαβ : IsCompatible fun V => (α V ≪≫ β V).hom) :
    D.glueIso D'' (fun V => α V ≪≫ β V) hαβ =
      D.glueIso D' α hα ≪≫ D'.glueIso D'' β hβ :=
  Iso.ext (glueHom_comp D D' D'' (fun V => (α V).hom) (fun V => (β V).hom) hα hβ)

end ChartComparison

end AlgebraicGeometry.AffineOpensGlue

end
