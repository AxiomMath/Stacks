module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCompBottomPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep3CompositionLaw
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorTransitionLower

/-!
# The compositor of Stacks 03D8 is monoidal

Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed
topoi. The compositor of **Stacks 03D8** is the comparison
`Stacks.SheafOfModules.pullbackModulesCompAdjIso` of `(ψ ∘ φ)^*` with `ψ^* ⋙ φ^*`, and this file
proves that it is compatible with the comparison of **Tag 03EL**:

`c⁻¹_{A ⊗ B} ≫ cmp_{ψ∘φ} = φ^*(cmp_ψ) ≫ cmp_φ ≫ (c⁻¹_A ⊗ c⁻¹_B)`,

which is `Stacks.SheafOfModules.PullbackTensorTransitionCoherence` at the transition
`θ = (pullbackModulesCompAdjIso φ ψ).inv`. This is the one input that
`StacksDraft.…​.PullbackTensorToposTransition` records as still owed, and with it every `θ` arising
from a factorisation and a 2-morphism of Stacks 04IC is covered, by
`Stacks.SheafOfModules.pullbackTensorTransitionCoherence_comp_pullbackModulesMap`.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep2_pullbackTensorLower_val`: **the five lower steps of
  the chain of Tag 03EL, read as a bilinear pairing.** It is the unit of `f⁻¹ ⊣ f_*` followed by
  the direct image of the product comparison, the pairing at the bottom of the chain, and the
  given morphism.
* `Stacks.SheafOfModules.pullbackTensorBottomPairing_comp_pullbackTensorLower`: **the identity
  upstairs.** The pairing at the bottom of the chain for `ψ`, followed by the five lower steps for
  `φ` at the compositor, is the unit of `φ⁻¹ ⊣ φ_*` followed by the direct image of the product
  comparison and the pairing at the bottom of the chain for `ψ ∘ φ`.
* `Stacks.SheafOfModules.pullbackTensorLower_comp_pushforwardModulesCompAppIso`: the equation
  between the five lower steps that the reduction
  `Stacks.SheafOfModules.pullbackTensorTransitionCoherence_of_lower` asks for.
* `Stacks.SheafOfModules.pullbackTensorTransitionCoherence_pullbackModulesCompAdjIso_inv`:
  **the compositor of Stacks 03D8 is monoidal.**

## Implementation notes

The route taken is the one `Stacks.SheafOfModules.pullbackTensorTransitionCoherence_of_lower`
opens: the coherence is transposed, which removes step 1 and all three comparisons of Tag 03EL,
and what is left is an equation between the five lower steps of the chain. That equation is then
reduced by the composition laws of steps 2 and 3 — each of which is a *bijection*, so each can be
inverted — to an equation between two pairings of `ψ⁻¹A^♯ ⨯ ψ⁻¹B^♯`, where
`Stacks.SheafOfModules.prodMap_comp_pullbackTensorBottomPairing` finishes it.

**No composition law for steps 4, 5 or 6 is used.** The bottom of the chain is never traversed
step by step: `Stacks.SheafOfModules.pairingApp_pullbackTensorBottom` and
`Stacks.SheafOfModules.pullbackTensorStep2to6_symm_val_app_unit_tmul` evaluate the whole of it at
once. So the two transports along equalities of sheaves of rings that step 5's law carries, and the
instantiation of step 6's law at `Stacks.SheafOfModules.fSharpCommRing_comp`, are never reached,
and the three universes of sections stay independent.

**Every bookkeeping step is a declaration of its own, with both of its sides written out**, for the
reason recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMateMonoidal`: the heartbeat budget is
per declaration, and a composite of two of these steps assembled inside one proof exhausts it at
`whnf` even though each step costs a fraction of a second on its own. The two transpositions are
written through the *unit* form of the hom-set bijection
(`Stacks.SheafOfModules.homEquiv_symm_unit_comp`) rather than through `Equiv.symm_apply_apply`,
because the two bijections that have to be identified carry differently spelled index objects and
deciding that identification from the `Equiv` costs the whole budget.

**One definitional equality here is unbounded and has to be routed around.** The underlying sheaf
of sets of `ψ_*(φ_*N)` and that of `(ψ ∘ φ)_*N` are the same object — `Eq.refl` decides it in no
time — but asking the *unifier* to identify `Sheaf.moduleSheaf _ (ψ_*(φ_*N))` with
`Sheaf.moduleSheaf _ ((ψ ∘ φ)_*N)` inside a larger term does not terminate within the budget: the
two have the same head, so congruence is tried first, and that asks for the two *sheaves of
modules* to be identified — which they are not, their scalar actions agreeing only propositionally
(that is exactly what `Stacks.SheafOfModules.pushforwardModulesCompAppIso` is for). So no statement
below ever puts a morphism out of the one spelling where a morphism out of the other is expected.
Where the two must meet, the meeting is arranged through the *iterated geometric* direct image
`φ_* ⋙ ψ_*`, whose head is different and against which the unifier therefore unfolds; that is why
`Stacks.SheafOfModules.id_eq_moduleSheafFunctor_map_pushforwardModulesCompAppIso_hom` is stated
with the identity on the left and at that spelling, and why
`Stacks.SheafOfModules.comp_eq_of_id_eq` takes it in that orientation. The same unfolding issue rules out
coercing a bilinear pairing with values in `ψ_*(φ_*N)` into the subtype of pairings with values in
`(ψ ∘ φ)_*N`, which is why the coherence is transposed with the comparison of direct images already
composed in rather than cancelled first.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

/-! ## Two transpositions and two product comparisons, over abstract categories -/

section Generic

variable {C₁ : Type u} [Category.{v} C₁] {D₁ : Type u'} [Category.{v'} D₁]

/-- **A morphism written in unit form is transposed back to itself.** For an adjunction
`L ⊣ R`, the inverse of the hom-set bijection carries `η_a ≫ R.map v` to `v`.

This is `CategoryTheory.Adjunction.homEquiv_unit` together with `Equiv.symm_apply_apply`, and it
is stated separately because the two bijections it is applied to below carry differently spelled
index objects: identifying them through the `Equiv` itself exhausts the heartbeat budget, whereas
in unit form the identification is a single definitional check. -/
lemma homEquiv_symm_unit_comp {L : C₁ ⥤ D₁} {R : D₁ ⥤ C₁} (adj : L ⊣ R) (a : C₁) (b : D₁)
    (v : L.obj a ⟶ b) :
    (adj.homEquiv a b).symm (adj.unit.app a ≫ R.map v) = v :=
  (congrArg (adj.homEquiv a b).symm (adj.homEquiv_unit a b v).symm).trans
    ((adj.homEquiv a b).symm_apply_apply v)

/-- **A morphism recognised in unit form is transposed back to the morphism inside.** The previous
lemma with its argument supplied by an equation, which is the form a `.trans` chain consumes. -/
lemma homEquiv_symm_eq_of_eq_unit_comp {L : C₁ ⥤ D₁} {R : D₁ ⥤ C₁} (adj : L ⊣ R) {a : C₁} {b : D₁}
    (u : a ⟶ R.obj b) (v : L.obj a ⟶ b) (h : u = adj.unit.app a ≫ R.map v) :
    (adj.homEquiv a b).symm u = v :=
  (congrArg (adj.homEquiv a b).symm h).trans (homEquiv_symm_unit_comp adj a b v)

/-- The inverse of the product comparison of a product-preserving functor cancels the product
comparison. Stated over abstract categories so that the two product comparisons of the composition
law for step 3 of the chain of Tag 03EL — which is the only place it is used — are matched by
unification rather than by a rewrite. -/
lemma preservesLimitPair_iso_inv_comp_prodComparison (Φ : C₁ ⥤ D₁) (P Q : C₁)
    [HasBinaryProduct P Q] [HasBinaryProduct (Φ.obj P) (Φ.obj Q)]
    [PreservesLimit (pair P Q) Φ] {W : D₁} (m : Φ.obj P ⨯ Φ.obj Q ⟶ W) :
    (PreservesLimitPair.iso Φ P Q).inv ≫ prodComparison Φ P Q ≫ m = m := by
  rw [← PreservesLimitPair.iso_hom Φ P Q, Iso.inv_hom_id_assoc]

/-- **One transposition against one product comparison.** If a morphism `u` out of `P ⨯ Q` is the
unit of `adj : L ⊣ R` followed by `R` of the product comparison of `L` and a morphism `m`, then
transposing `u` back across `adj` and cancelling the product comparison gives `m`. -/
private lemma preservesLimitPair_inv_comp_homEquiv_symm {C₂ : Type*} [Category C₂] {D₂ : Type*}
    [Category D₂] {L : C₂ ⥤ D₂} {R : D₂ ⥤ C₂} (adj : L ⊣ R) (P Q : C₂) [HasBinaryProduct P Q]
    [HasBinaryProduct (L.obj P) (L.obj Q)] [PreservesLimit (pair P Q) L] {W : D₂}
    {m : L.obj P ⨯ L.obj Q ⟶ W} {u : P ⨯ Q ⟶ R.obj W}
    (hu : u = adj.unit.app (P ⨯ Q) ≫ R.map (prodComparison L P Q ≫ m)) :
    (PreservesLimitPair.iso L P Q).inv ≫ (adj.homEquiv (P ⨯ Q) W).symm u = m :=
  (congrArg (fun k ↦ (PreservesLimitPair.iso L P Q).inv ≫ k)
      (homEquiv_symm_eq_of_eq_unit_comp adj u (prodComparison L P Q ≫ m) hu)).trans
    (preservesLimitPair_iso_inv_comp_prodComparison L P Q m)

/-- **Two successive transpositions against two product comparisons.** Let `adj₁ : L₁ ⊣ R₁` and
`adj₂ : L₂ ⊣ R₂` be adjunctions, let `P` and `Q` be two objects at the bottom and `n` a morphism
out of `L₂L₁P ⨯ L₂L₁Q`. If a morphism `u` out of `P ⨯ Q` is the unit of `adj₁` followed by `R₁` of
the product comparison of `L₁` and a morphism `m`, and `m` is in turn the unit of `adj₂` followed
by `R₂` of the product comparison of `L₂` and `n`, then transposing `u` back across `adj₁` and then
across `adj₂`, cancelling a product comparison each time, gives `n`.

This is the whole of the two transpositions that the composition law for step 3 of the chain of
Tag 03EL performs, and it is stated over abstract categories because the objects it is applied to
carry two spellings each — the inverse image of a sheaf of modules against the sheaf of modules of
an inverse image — and matching them by unification costs one definitional check rather than a
rewrite that is reported ill-typed. -/
lemma preservesLimitPair_inv_comp_homEquiv_symm_comp {C₂ : Type*} [Category C₂] {D₂ : Type*}
    [Category D₂] {E₂ : Type*} [Category E₂] {L₁ : C₂ ⥤ D₂} {R₁ : D₂ ⥤ C₂} (adj₁ : L₁ ⊣ R₁)
    {L₂ : D₂ ⥤ E₂} {R₂ : E₂ ⥤ D₂} (adj₂ : L₂ ⊣ R₂) (P Q : C₂) [HasBinaryProduct P Q]
    [HasBinaryProduct (L₁.obj P) (L₁.obj Q)]
    [HasBinaryProduct (L₂.obj (L₁.obj P)) (L₂.obj (L₁.obj Q))]
    [PreservesLimit (pair P Q) L₁] [PreservesLimit (pair (L₁.obj P) (L₁.obj Q)) L₂]
    {W : E₂} {n : L₂.obj (L₁.obj P) ⨯ L₂.obj (L₁.obj Q) ⟶ W}
    {m : L₁.obj P ⨯ L₁.obj Q ⟶ R₂.obj W} {u : P ⨯ Q ⟶ R₁.obj (R₂.obj W)}
    (hu : u = adj₁.unit.app (P ⨯ Q) ≫ R₁.map (prodComparison L₁ P Q ≫ m))
    (hm : m = adj₂.unit.app (L₁.obj P ⨯ L₁.obj Q) ≫
      R₂.map (prodComparison L₂ (L₁.obj P) (L₁.obj Q) ≫ n)) :
    (PreservesLimitPair.iso L₂ (L₁.obj P) (L₁.obj Q)).inv ≫
        (adj₂.homEquiv (L₁.obj P ⨯ L₁.obj Q) W).symm
          ((PreservesLimitPair.iso L₁ P Q).inv ≫
            (adj₁.homEquiv (P ⨯ Q) (R₂.obj W)).symm u) = n :=
  (congrArg (fun k ↦ (PreservesLimitPair.iso L₂ (L₁.obj P) (L₁.obj Q)).inv ≫
        (adj₂.homEquiv (L₁.obj P ⨯ L₁.obj Q) W).symm k)
      (preservesLimitPair_inv_comp_homEquiv_symm adj₁ P Q hu)).trans
    (preservesLimitPair_inv_comp_homEquiv_symm adj₂ (L₁.obj P) (L₁.obj Q) hm)

/-- **A morphism recognised as the identity composes away, and the other factor may be rewritten
at the same time.**

The identity is given *first*, as the left-hand side of `hk`, and that is what makes the lemma
usable: the object `V` is then read off the spelling `hk` is stated at, and the two other spellings
of it — the source and the target of `k`, and the target of `q` — are each decided against that one
by unfolding. Supplied the other way round, `V` is read off `k`'s source and the unifier is asked
to identify `k`'s source with its target by congruence, which at the objects this is applied to is
an unbounded search. -/
lemma comp_eq_of_id_eq {C₁' : Type*} [Category C₁'] {U V : C₁'} {k : V ⟶ V}
    (hk : CategoryStruct.id V = k) {q q' : U ⟶ V} (h : q = q') : q ≫ k = q' :=
  (congrArg (fun z ↦ q ≫ z) hk.symm).trans ((Category.comp_id q).trans h)

end Generic

/-! ## The five lower steps of the chain of Tag 03EL as a bilinear pairing -/

section Lower

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

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify Y.J AddCommGrpCat]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Steps 5 and 6 of the chain of Tag 03EL, traversed backwards from `k`, are the bottom of the
chain followed by `k`.** This is `CategoryTheory.Adjunction.homEquiv_naturality_right` for the
adjunction of Stacks 03CZ that step 5 is, once step 6 — an isomorphism read as a bijection of
hom-sets — has been unfolded across the two spellings of the tensor product of the two
pullbacks. -/
lemma pullbackTensorStep5_symm_step6_symm (k : pullbackTensorTarget f F G ⟶ N) :
    (pullbackTensorStep5 f F G N).symm ((pullbackTensorStep6 f F G N).symm k) =
      pullbackTensorBottomHom f F G ≫
        (SheafOfModules.restrictScalars f.fSharpInverseImage).map k := by
  have h6 : (pullbackTensorStep6 f F G N).symm k =
      (pullbackTensorStep6 f F G (pullbackTensorTarget f F G)).symm
        (𝟙 (pullbackTensorTarget f F G)) ≫ k := by
    show _ ≫ k = (_ ≫ 𝟙 _) ≫ k
    exact congrArg (fun m ↦ m ≫ k) (Category.comp_id _).symm
  rw [h6]
  exact (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv_naturality_right _ k

/-- Step 2 of the chain of Tag 03EL undoes the outermost step of the five lower steps. -/
lemma pullbackTensorStep2_pullbackTensorLower
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
      ((f.pullbackModules).obj F, (f.pullbackModules).obj G) ⟶ N) :
    pullbackTensorStep2 f F G N (pullbackTensorLower f F G N g) =
      (pullbackTensorStep3 f F G N).symm ((pullbackTensorStep4 f F G N).symm
        ((pullbackTensorStep5 f F G N).symm ((pullbackTensorStep6 f F G N).symm g))) :=
  Equiv.apply_symm_apply (pullbackTensorStep2 f F G N) _

omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Step 3 of the chain of Tag 03EL traversed backwards, on the underlying pairing.** It is the
unit of `f⁻¹ ⊣ f_*` followed by the direct image of the given pairing precomposed with the product
comparison of `f⁻¹`. This is
`Stacks.SheafOfModules.inverseImageBilinearEquiv_apply_coe_eq_unit_comp` read at the restriction of
scalars the chain takes its values in. -/
lemma pullbackTensorStep3_symm_apply_coe
    (p : { p : Sheaf.moduleSheaf
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
          Sheaf.moduleSheaf
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
          Sheaf.moduleSheaf
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) //
        IsBilinearPairing
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) p }) :
    ((pullbackTensorStep3 f F G N).symm p).1 =
      f.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
        f.toToposHom.pushforward.map
          (prodComparison f.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫ p.1) :=
  inverseImageBilinearEquiv_apply_coe_eq_unit_comp f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F G
    ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) p

/-- **The five lower steps of the chain of Tag 03EL, read as a bilinear pairing.** For a morphism
`k : f^*F ⊗_{O_C} f^*G ⟶ N`, the morphism `F ⊗_{O_D} G ⟶ f_*N` that the five lower steps produce
is, as a pairing of the underlying sheaves of sets, the unit of `f⁻¹ ⊣ f_*` followed by the direct
image of: the product comparison of `f⁻¹`, the pairing at the bottom of the chain, and `k`.

This is the shape in which both sides of the coherence of the compositor of Stacks 03D8 are
read. -/
lemma pullbackTensorStep2_pullbackTensorLower_val (k : pullbackTensorTarget f F G ⟶ N) :
    (pullbackTensorStep2 f F G N (pullbackTensorLower f F G N k)).1 =
      f.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
        f.toToposHom.pushforward.map
          (prodComparison f.toToposHom.inverseImage
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
            (((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
                  (pullbackTensorBottomHom f F G)).1 ≫
              (Sheaf.moduleSheafFunctor
                  (inverseImageRingSheaf f.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
                ((SheafOfModules.restrictScalars f.fSharpInverseImage).map k))) :=
  (congrArg Subtype.val
      ((pullbackTensorStep2_pullbackTensorLower f F G N k).trans
        (congrArg (pullbackTensorStep3 f F G N).symm
          ((congrArg (pullbackTensorStep4 f F G N).symm
              (pullbackTensorStep5_symm_step6_symm f F G N k)).trans
            (pullbackTensorStep4_symm_bottom_comp f F G N k))))).trans
    (pullbackTensorStep3_symm_apply_coe f F G N _)

/-- **Step 2 of the chain of Tag 03EL at the five lower steps traversed backwards from the
identity** is step 3 traversed backwards from the pairing at the bottom of the chain. The two
bottom steps at the identity are the bottom of the chain by definition. -/
lemma pullbackTensorStep2_pullbackTensorLower_id :
    pullbackTensorStep2 f F G (pullbackTensorTarget f F G)
        (pullbackTensorLower f F G (pullbackTensorTarget f F G)
          (𝟙 (pullbackTensorTarget f F G))) =
      (pullbackTensorStep3 f F G (pullbackTensorTarget f F G)).symm
        ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
          (pullbackTensorBottomHom f F G)) :=
  pullbackTensorStep2_pullbackTensorLower f F G (pullbackTensorTarget f F G)
    (𝟙 (pullbackTensorTarget f F G))

end Lower

/-! ## The identity upstairs -/

section Upstairs

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
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)
  (A B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The product comparison of `φ⁻¹` against the pairing at the bottom of the chain of Tag 03EL
for `ψ ∘ φ`.** The product comparison of `φ⁻¹` at the two inverse images along `ψ`, followed by the
pairing at the bottom of the chain for the composite, is the inverse image along `φ` of the two
units of Stacks 03CZ for `ψ`, followed by the product comparison of `φ⁻¹` at the two pullbacks
along `ψ`, the pairing at the bottom of the chain for `φ`, and the compositor of Stacks 03D8.

It is `Stacks.SheafOfModules.prodMap_comp_pullbackTensorBottomPairing` with the two units moved
across the product comparison by `CategoryTheory.Limits.prodComparison_natural`. -/
private lemma prodComparison_comp_pullbackTensorBottomPairing :
    prodComparison φ.toToposHom.inverseImage
          (Sheaf.moduleSheaf
            (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
            ((inverseImageModules ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A))
          (Sheaf.moduleSheaf
            (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
            ((inverseImageModules ψ.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫
        ((pullbackTensorStep4 (ψ.comp φ).toModulesHom A B
              (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).symm
            (pullbackTensorBottomHom (ψ.comp φ).toModulesHom A B)).1 =
      φ.toToposHom.inverseImage.map
          (prod.map (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B)) ≫
        prodComparison φ.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B)
                (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B))).symm
              (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B :=
  (congrArg (fun m ↦ prodComparison φ.toToposHom.inverseImage
        (Sheaf.moduleSheaf
          (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
          ((inverseImageModules ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A))
        (Sheaf.moduleSheaf
          (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
          ((inverseImageModules ψ.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫ m)
      (prodMap_comp_pullbackTensorBottomPairing φ ψ A B).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫
            ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B)
                  (pullbackTensorTarget φ.toModulesHom
                    ((ψ.toModulesHom.pullbackModules).obj A)
                    ((ψ.toModulesHom.pullbackModules).obj B))).symm
                (pullbackTensorBottomHom φ.toModulesHom
                  ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
              compTensorSheafHom φ ψ A B)
          (prodComparison_natural φ.toToposHom.inverseImage
            (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B)).symm).trans
        (Category.assoc _ _ _)))

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The left-hand side of the identity upstairs on a pair of local sections**: the pairing at the
bottom of the chain of Tag 03EL for `ψ`, followed by the five lower steps for `φ` at the compositor
of Stacks 03D8, carries a pair of sections to the pair of their images under the two units of
Stacks 03CZ for `ψ`, pushed through the unit of `φ⁻¹ ⊣ φ_*` and then through the direct image of
the product comparison of `φ⁻¹`, the pairing at the bottom of the chain for `φ` and the
compositor. -/
private lemma sectionsFunctor_map_pullbackTensorBottomPairing_comp_lower (V : Y.Cᵒᵖ)
    (x : ((inverseImageModules ψ.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A).val.obj V)
    (s : ((inverseImageModules ψ.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B).val.obj V) :
    (Sheaf.sectionsFunctor Y.J V).map
        (((pullbackTensorStep4 ψ.toModulesHom A B
                (pullbackTensorTarget ψ.toModulesHom A B)).symm
              (pullbackTensorBottomHom ψ.toModulesHom A B)).1 ≫
          (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).map
            ((SheafOfModules.restrictScalars ψ.toModulesHom.fSharpInverseImage).map
              (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B)
                (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
                (compTensorHom φ ψ A B))))
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V) x s) =
      (Sheaf.sectionsFunctor Y.J V).map
        (φ.toToposHom.pushforward.map
          (prodComparison φ.toToposHom.inverseImage
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                ((ψ.toModulesHom.pullbackModules).obj A))
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                ((ψ.toModulesHom.pullbackModules).obj B)) ≫
            ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B)
                  (pullbackTensorTarget φ.toModulesHom
                    ((ψ.toModulesHom.pullbackModules).obj A)
                    ((ψ.toModulesHom.pullbackModules).obj B))).symm
                (pullbackTensorBottomHom φ.toModulesHom
                  ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
              compTensorSheafHom φ ψ A B))
        ((Sheaf.sectionsFunctor Y.J V).map
          (φ.toToposHom.adj.unit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj A) ⨯
              Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                ((ψ.toModulesHom.pullbackModules).obj B)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V)
            (((extendRestrictScalarsAdjunction Y.J (fSharpCommRing ψ.toModulesHom)
                  (inverseImageRingSheaf ψ.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).property
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property).unit.app
                ((inverseImageModules ψ.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A)).val.app V x)
            (((extendRestrictScalarsAdjunction Y.J (fSharpCommRing ψ.toModulesHom)
                  (inverseImageRingSheaf ψ.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).property
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property).unit.app
                ((inverseImageModules ψ.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)).val.app V s))) :=
  (pairingApp_comp
      ((pullbackTensorStep4 ψ.toModulesHom A B
            (pullbackTensorTarget ψ.toModulesHom A B)).symm
          (pullbackTensorBottomHom ψ.toModulesHom A B)).1
      ((SheafOfModules.restrictScalars ψ.toModulesHom.fSharpInverseImage).map
        (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
          ((ψ.toModulesHom.pullbackModules).obj B)
          (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
          (compTensorHom φ ψ A B))) V x s).trans
    ((congrArg ((Sheaf.sectionsFunctor Y.J V).map
          ((Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).map
            ((SheafOfModules.restrictScalars ψ.toModulesHom.fSharpInverseImage).map
              (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B)
                (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
                (compTensorHom φ ψ A B)))))
        (pairingApp_pullbackTensorBottom ψ.toModulesHom A B V x s)).trans
      ((sectionsFunctor_map_moduleSheafFunctor_map'
          (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
          ((SheafOfModules.restrictScalars ψ.toModulesHom.fSharpInverseImage).map
            (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
              (compTensorHom φ ψ A B))) V _).trans
        (pullbackTensorStep2to6_symm_val_app_unit_tmul φ.toModulesHom
          ((ψ.toModulesHom.pullbackModules).obj A) ((ψ.toModulesHom.pullbackModules).obj B)
          (pullbackTensorTarget (ψ.comp φ).toModulesHom A B) (compTensorHom φ ψ A B) V _ _)))

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The identity upstairs with the two units of Stacks 03CZ for `ψ` moved to the front.** The
unit of `φ⁻¹ ⊣ φ_*` followed by the direct image of the product comparison of `φ⁻¹` and the pairing
at the bottom of the chain of Tag 03EL for `ψ ∘ φ` is the two units of Stacks 03CZ for `ψ`,
followed by the unit of `φ⁻¹ ⊣ φ_*` at the two pullbacks along `ψ` and then by the direct image of
the product comparison, the pairing at the bottom of the chain for `φ` and the compositor.

It is the previous lemma together with the naturality of the unit of `φ⁻¹ ⊣ φ_*`, which is what
moves the inverse image of the two units out of the direct image. -/
private lemma unit_comp_pushforward_map_prodComparison_comp_pullbackTensorBottomPairing :
    φ.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf
        (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A) ⨯
            Sheaf.moduleSheaf
              (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫
        φ.toToposHom.pushforward.map (prodComparison φ.toToposHom.inverseImage
          (Sheaf.moduleSheaf
            (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A))
            (Sheaf.moduleSheaf
              (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫
          ((pullbackTensorStep4 (ψ.comp φ).toModulesHom A B
              (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).symm
            (pullbackTensorBottomHom (ψ.comp φ).toModulesHom A B)).1) =
      (prod.map (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B) ≫
          φ.toToposHom.adj.unit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B))) ≫
        φ.toToposHom.pushforward.map (prodComparison φ.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B) :=
  (congrArg (fun m ↦ φ.toToposHom.adj.unit.app
    (Sheaf.moduleSheaf
      (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A) ⨯
            Sheaf.moduleSheaf
              (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫
        φ.toToposHom.pushforward.map m)
      (prodComparison_comp_pullbackTensorBottomPairing φ ψ A B)).trans
    ((congrArg (fun m ↦ φ.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf
        (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A) ⨯
            Sheaf.moduleSheaf
              (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫ m)
        (φ.toToposHom.pushforward.map_comp
          (φ.toToposHom.inverseImage.map (prod.map (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B)))
          (prodComparison φ.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun m ↦ m ≫ φ.toToposHom.pushforward.map
          (prodComparison φ.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B))
          (φ.toToposHom.adj.unit.naturality (prod.map (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B))).symm)))

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The right-hand side of the identity upstairs on a pair of local sections**: the two units of
Stacks 03CZ for `ψ`, the unit of `φ⁻¹ ⊣ φ_*` and the direct image of the rest, applied in turn. -/
private lemma sectionsFunctor_map_prodMap_comp_unit (V : Y.Cᵒᵖ)
    (x : ((inverseImageModules ψ.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A).val.obj V)
    (s : ((inverseImageModules ψ.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B).val.obj V) :
    (Sheaf.sectionsFunctor Y.J V).map
        ((prod.map (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B) ≫
            φ.toToposHom.adj.unit.app
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B))) ≫
          φ.toToposHom.pushforward.map (prodComparison φ.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B))
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V) x s) =
      (Sheaf.sectionsFunctor Y.J V).map
        (φ.toToposHom.pushforward.map (prodComparison φ.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B))
        ((Sheaf.sectionsFunctor Y.J V).map
          (φ.toToposHom.adj.unit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)))
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V)
            (((extendRestrictScalarsAdjunction Y.J (fSharpCommRing ψ.toModulesHom)
                (inverseImageRingSheaf ψ.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property).unit.app
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A)).val.app V x)
                (((extendRestrictScalarsAdjunction Y.J (fSharpCommRing ψ.toModulesHom)
                (inverseImageRingSheaf ψ.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property).unit.app
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)).val.app V s))) :=
  ((Sheaf.sectionsFunctor Y.J V).map_comp_apply
      (prod.map (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B) ≫
        φ.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)))
      (φ.toToposHom.pushforward.map (prodComparison φ.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B)) _).trans
    (congrArg ((Sheaf.sectionsFunctor Y.J V).map
        (φ.toToposHom.pushforward.map (prodComparison φ.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((ψ.toModulesHom.pullbackModules).obj A))
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B)))
      ((((Sheaf.sectionsFunctor Y.J V).map_comp_apply
        (prod.map (extendScalarsUnitSheafHom ψ.toModulesHom A)
            (extendScalarsUnitSheafHom ψ.toModulesHom B))
            (φ.toToposHom.adj.unit.app
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)))
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V) x s)).trans
          (congrArg ((Sheaf.sectionsFunctor Y.J V).map
              (φ.toToposHom.adj.unit.app
                (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                  ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B))))
            (Limits.map_prodMap_prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V)
              (extendScalarsUnitSheafHom ψ.toModulesHom A)
              (extendScalarsUnitSheafHom ψ.toModulesHom B) x s))).trans
        ((congrArg (fun z ↦ (Sheaf.sectionsFunctor Y.J V).map
              (φ.toToposHom.adj.unit.app
                (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                  ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)))
              (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V) z
                ((Sheaf.sectionsFunctor Y.J V).map
                  (extendScalarsUnitSheafHom ψ.toModulesHom B) s)))
            (sectionsFunctor_map_extendScalarsUnitSheafHom ψ.toModulesHom A V x)).trans
          (congrArg (fun z ↦ (Sheaf.sectionsFunctor Y.J V).map
              (φ.toToposHom.adj.unit.app
                (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
                  ((ψ.toModulesHom.pullbackModules).obj A) ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
              ((ψ.toModulesHom.pullbackModules).obj B)))
              (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V)
                (((extendRestrictScalarsAdjunction Y.J (fSharpCommRing ψ.toModulesHom)
                (inverseImageRingSheaf ψ.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).property
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property).unit.app
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A)).val.app V x) z))
            (sectionsFunctor_map_extendScalarsUnitSheafHom ψ.toModulesHom B V s)))))

omit [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The identity upstairs: the pairing at the bottom of the chain of Tag 03EL for `ψ`, followed
by the five lower steps of the chain for `φ` at the compositor of Stacks 03D8, is the unit of
`φ⁻¹ ⊣ φ_*` followed by the direct image of the product comparison of `φ⁻¹` and the pairing at the
bottom of the chain for `ψ ∘ φ`.**

Both sides are pairings of the two inverse images along `ψ`, so they agree as soon as they agree on
every pair of local sections; there both sides carry the pair through the two units of Stacks 03CZ
for `ψ`, through the unit of `φ⁻¹ ⊣ φ_*`, and then through the direct image of one and the same
morphism upstairs, which is
`Stacks.SheafOfModules.prodMap_comp_pullbackTensorBottomPairing`.

This is the whole mathematical content of the monoidality of the compositor; what surrounds it is
the two composition laws of steps 2 and 3 of the chain, inverted. -/
theorem pullbackTensorBottomPairing_comp_pullbackTensorLower :
    ((pullbackTensorStep4 ψ.toModulesHom A B
            (pullbackTensorTarget ψ.toModulesHom A B)).symm
          (pullbackTensorBottomHom ψ.toModulesHom A B)).1 ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).map
          ((SheafOfModules.restrictScalars ψ.toModulesHom.fSharpInverseImage).map
            (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
              (compTensorHom φ ψ A B))) =
      φ.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf
            (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A) ⨯
            Sheaf.moduleSheaf
              (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
              ((inverseImageModules ψ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫
        φ.toToposHom.pushforward.map
          (prodComparison φ.toToposHom.inverseImage
              (Sheaf.moduleSheaf
                (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
                ((inverseImageModules ψ.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A))
              (Sheaf.moduleSheaf
                (inverseImageRingSheaf ψ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
                ((inverseImageModules ψ.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B)) ≫
            ((pullbackTensorStep4 (ψ.comp φ).toModulesHom A B
                  (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).symm
                (pullbackTensorBottomHom (ψ.comp φ).toModulesHom A B)).1) :=
  hom_ext_prod' fun V x s ↦
    (sectionsFunctor_map_pullbackTensorBottomPairing_comp_lower φ ψ A B V x s).trans
      ((sectionsFunctor_map_prodMap_comp_unit φ ψ A B V x s).symm.trans
        (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J V).map m
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J V) x s))
          (unit_comp_pushforward_map_prodComparison_comp_pullbackTensorBottomPairing
            φ ψ A B)).symm)

omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The comparison `ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of direct images is the identity on underlying
sheaves of sets.** The comparison of the geometric direct images it is built from is
`Stacks.SheafOfModules.compPushforwardToposIso`, which is `Iso.refl`, and
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModulesCompIsoApp_hom` says
the comparison of sheaves of modules is that comparison on underlying sheaves of sets.

The identity is written at the *iterated geometric* direct image rather than at the underlying
sheaf of sets of the iterated direct image of modules. The two are the same object, but only the
former makes the unifier unfold: against the latter it tries congruence on `Sheaf.moduleSheaf`
first, which asks it to identify two sheaves of modules that agree only propositionally, and that
search is unbounded. -/
theorem id_eq_moduleSheafFunctor_map_pushforwardModulesCompAppIso_hom
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    CategoryStruct.id ((φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward).obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (pushforwardModulesCompAppIso φ ψ N).hom := rfl

/-- **The five lower steps for `ψ` after the five lower steps for `φ`, followed by the comparison
of direct images, read as a bilinear pairing.** It is the unit of `ψ⁻¹ ⊣ ψ_*` followed by the
direct image of the product comparison of `ψ⁻¹`, the pairing at the bottom of the chain of Tag 03EL
for `ψ`, and the five lower steps for `φ`: the comparison of direct images contributes nothing,
being the identity on underlying sheaves of sets. -/
private lemma pullbackTensorStep2_pullbackTensorLower_comp_val :
    (pullbackTensorStep2 (ψ.comp φ).toModulesHom A B
        (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
        (pullbackTensorLower ψ.toModulesHom A B
          ((pushforwardModules φ.toModulesHom).obj
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
          (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
            ((ψ.toModulesHom.pullbackModules).obj B)
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B) (compTensorHom φ ψ A B)) ≫
          (pushforwardModulesCompAppIso φ ψ
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).hom)).1 =
      ψ.toToposHom.adj.unit.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) B) ≫
        ψ.toToposHom.pushforward.map
          (prodComparison ψ.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) B) ≫
            (((pullbackTensorStep4 ψ.toModulesHom A B
                  (pullbackTensorTarget ψ.toModulesHom A B)).symm
                (pullbackTensorBottomHom ψ.toModulesHom A B)).1 ≫
              (Sheaf.moduleSheafFunctor
                  (inverseImageRingSheaf ψ.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).map
                ((SheafOfModules.restrictScalars ψ.toModulesHom.fSharpInverseImage).map
                  (pullbackTensorLower φ.toModulesHom
                    ((ψ.toModulesHom.pullbackModules).obj A)
                    ((ψ.toModulesHom.pullbackModules).obj B)
                    (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
                    (compTensorHom φ ψ A B))))) := by
  refine Eq.trans (pullbackTensorStep2_comp' φ ψ
    (pullbackTensorTarget (ψ.comp φ).toModulesHom A B) A B
    (pullbackTensorLower ψ.toModulesHom A B
      ((pushforwardModules φ.toModulesHom).obj (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
      (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
        ((ψ.toModulesHom.pullbackModules).obj B)
        (pullbackTensorTarget (ψ.comp φ).toModulesHom A B) (compTensorHom φ ψ A B)))) ?_
  exact comp_eq_of_id_eq
    (id_eq_moduleSheafFunctor_map_pushforwardModulesCompAppIso_hom φ ψ
      (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
    (pullbackTensorStep2_pullbackTensorLower_val ψ.toModulesHom A B
      ((pushforwardModules φ.toModulesHom).obj (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
      (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
        ((ψ.toModulesHom.pullbackModules).obj B)
        (pullbackTensorTarget (ψ.comp φ).toModulesHom A B) (compTensorHom φ ψ A B)))

/-- **Step 3 of the chain of Tag 03EL at the five lower steps for `ψ` after the five lower steps
for `φ`.** The pairing that step 3 for `ψ ∘ φ` produces is the pairing at the bottom of the chain
for `ψ ∘ φ`.

This is the composition law for step 3 — two transpositions, each cancelling a product comparison
— read against the identity upstairs. -/
private lemma pullbackTensorStep3_pullbackTensorStep2_pullbackTensorLower :
    (pullbackTensorStep3 (ψ.comp φ).toModulesHom A B
        (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
        (pullbackTensorStep2 (ψ.comp φ).toModulesHom A B
          (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
          (pullbackTensorLower ψ.toModulesHom A B
              ((pushforwardModules φ.toModulesHom).obj
                (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
              (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B)
                (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
                (compTensorHom φ ψ A B)) ≫
            (pushforwardModulesCompAppIso φ ψ
              (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).hom))).1 =
      ((pullbackTensorStep4 (ψ.comp φ).toModulesHom A B
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).symm
          (pullbackTensorBottomHom (ψ.comp φ).toModulesHom A B)).1 := by
  refine Eq.trans (pullbackTensorStep3_comp φ ψ
    (pullbackTensorTarget (ψ.comp φ).toModulesHom A B) A B
    (pullbackTensorStep2 (ψ.comp φ).toModulesHom A B
      (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
      (pullbackTensorLower ψ.toModulesHom A B
            ((pushforwardModules φ.toModulesHom).obj
              (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
            (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
              (compTensorHom φ ψ A B)) ≫
          (pushforwardModulesCompAppIso φ ψ
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).hom))) ?_
  exact preservesLimitPair_inv_comp_homEquiv_symm_comp ψ.toToposHom.adj φ.toToposHom.adj
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A)
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) B)
    (pullbackTensorStep2_pullbackTensorLower_comp_val φ ψ A B)
    (pullbackTensorBottomPairing_comp_pullbackTensorLower φ ψ A B)

/-- **The equation between the five lower steps of the chain of Tag 03EL that the coherence of the
compositor of Stacks 03D8 reduces to.** The five lower steps for `ψ` applied to the five lower
steps for `φ` at the compositor, followed by the comparison `ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of direct
images, are the five lower steps for `ψ ∘ φ` at the identity.

This is the hypothesis `h2` of
`Stacks.SheafOfModules.pullbackTensorTransitionCoherence_of_lower` at
`θ = (pullbackModulesCompAdjIso φ ψ).inv`. The proof applies steps 2 and 3 of the chain for
`ψ ∘ φ` — both bijections — to the two sides; step 2's composition law disposes of the comparison
of direct images and step 3's reduces what is left to the identity upstairs. -/
theorem pullbackTensorLower_comp_pushforwardModulesCompAppIso :
    pullbackTensorLower ψ.toModulesHom A B
          ((pushforwardModules φ.toModulesHom).obj
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
          (pullbackTensorLower φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
            ((ψ.toModulesHom.pullbackModules).obj B)
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B) (compTensorHom φ ψ A B)) ≫
        (pushforwardModulesCompAppIso φ ψ (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).hom =
      pullbackTensorLower (ψ.comp φ).toModulesHom A B
        (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)
        (𝟙 (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)) := by
  refine (pullbackTensorStep2 (ψ.comp φ).toModulesHom A B
    (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).injective
    ((pullbackTensorStep3 (ψ.comp φ).toModulesHom A B
      (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).injective (Subtype.ext ?_))
  refine Eq.trans (pullbackTensorStep3_pullbackTensorStep2_pullbackTensorLower φ ψ A B) ?_
  exact (congrArg Subtype.val
    ((congrArg (pullbackTensorStep3 (ψ.comp φ).toModulesHom A B
      (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
        (pullbackTensorStep2_pullbackTensorLower_id (ψ.comp φ).toModulesHom A B)).trans
      (Equiv.apply_symm_apply (pullbackTensorStep3 (ψ.comp φ).toModulesHom A B
        (pullbackTensorTarget (ψ.comp φ).toModulesHom A B))
        ((pullbackTensorStep4 (ψ.comp φ).toModulesHom A B
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).symm
          (pullbackTensorBottomHom (ψ.comp φ).toModulesHom A B))))).symm

/-- **The compositor of Stacks 03D8 is monoidal.** For morphisms of ringed topoi
`φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` and sheaves of
`O_E`-modules `A` and `B`, the inverse compositor `(ψ ∘ φ)^* ⟸ ψ^*φ^*` of Stacks 03D8 commutes
with the comparison of **Tag 03EL** for `ψ ∘ φ`, for `ψ` and for `φ`:

`c⁻¹ ≫ cmp_(ψ∘φ) = φ^*(cmp_ψ) ≫ cmp_φ ≫ (c⁻¹ ⊗ c⁻¹)`.

This is `Stacks.SheafOfModules.PullbackTensorTransitionCoherence` at the one transition that
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposTransition` records as the single
input still owed, and no invertibility or cartesianness is assumed: the statement holds for an
arbitrary sheaf of rings on each of the three sites, at three independent universes of sections. -/
theorem pullbackTensorTransitionCoherence_pullbackModulesCompAdjIso_inv :
    PullbackTensorTransitionCoherence φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
      (pullbackModulesCompAdjIso φ ψ).inv :=
  pullbackTensorTransitionCoherence_of_lower φ.toModulesHom ψ.toModulesHom
    (ψ.comp φ).toModulesHom (pullbackModulesCompAdjIso φ ψ).inv
    (fun A' B' ↦ pushforwardModulesCompAppIso φ ψ
      (pullbackTensorTarget (ψ.comp φ).toModulesHom A' B'))
    (fun A' B' ↦ pullbackTensorStep1_comp' φ ψ
      (pullbackTensorTarget (ψ.comp φ).toModulesHom A' B') A' B'
      ((pullbackTensorIso (ψ.comp φ).toModulesHom).hom.app (A', B')))
    (fun A' B' ↦ pullbackTensorLower_comp_pushforwardModulesCompAppIso φ ψ A' B')

end Upstairs

end Stacks.SheafOfModules

end
