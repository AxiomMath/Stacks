module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeIdentityFreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConePushout

/-!
# Goodness is closed under the cone of a morphism out of a free differential graded module

Let `f : X ⟶ Y` be a morphism of ringed topoi, let `A` be a sheaf of differential graded
`O_Y`-algebras, let `S` be a sheaf of graded sets on `Y`, let `P` be a right differential graded
`A`-module and let `g : A[S] ⟶ P` be a homomorphism. **If `P` is good then so is the cone of
`g`.** This is the induction step of the tower of the first proof of Tag 0FSH: each stage of
that tower is the twisted extension of the previous one by a free module, which is the cone of a
homomorphism whose *source* is free.

The argument is the one the source gives, read at the quantification of
`SheafOfModules.IsGoodToposBaseChange`.

* **Existence.** `SheafOfModules.DifferentialGradedModule.ConePackage.isPushout` presents
  `C(g)` as the pushout of the span `C(𝟙_{A[S]}) ⟵ A[S] ⟶ P`. A morphism out of a pushout is a
  pair of morphisms out of the two corners agreeing on the span's apex, and each of the three
  has a known base change: `A[S]` by Tag 0FSG, `C(𝟙_{A[S]})` by
  `ConeIdentityFreeDifferentialGradedModuleToposPullback.lean`, and `P` by hypothesis. The
  pushout on the target topos is again a cone — of the induced morphism
  `SheafOfModules.baseChangeHom : B[f⁻¹S] ⟶ T_P` — so the base change of `C(g)` is `C(g')`.
* **Flatness.** *Not* from the pushout: pushouts do not preserve flatness. `C(g')` sits in the
  admissible short exact sequence `0 → T_P → C(g') → B[f⁻¹S][1] → 0`, both ends are flat and
  K-flat — `T_P` because `P` is good, `B[f⁻¹S]` because it is free — and conditions (1) and (2)
  satisfy two-out-of-three along such a sequence. That is Tag 0FSC, and
  `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_cone` is it at a cone.

## Main definitions

* `SheafOfModules.baseChangeUnit` is the unit `P ⟶ f_{*,ψ}T_P` of a corepresentability datum for
  the base change of `P`, and `SheafOfModules.baseChangeHom` the induced morphism
  `B[f⁻¹S] ⟶ T_P`, the base change of `g`.
* `SheafOfModules.coneToposHomEquiv` is the bijection
  `Hom_B(C(g'), Q) ≃ Hom_A(C(g), f_{*,ψ}Q)`, and
  `SheafOfModules.coneToposCorepresentableBy` the corepresentability witness it assembles into.

## Main results

* `SheafOfModules.coneToposHomEquiv_comp`: the bijection is natural in `Q`.
* `SheafOfModules.cone_freeDGModule_isGoodToposBaseChange`: **goodness is closed under the cone
  of a morphism out of a free differential graded module.**

## Implementation notes

**Why the source of the cone must be free, and why this is not a two-out-of-three.** An
admissible short exact sequence `0 → P' → P'' → P''' → 0` makes the middle term a cone, so one
might expect conditions (1), (2) and (3) of Tag 0FSA all to satisfy two-out-of-three along it.
Conditions (1) and (2) do — they are properties of a given object — but condition (3) does not,
because it carries an **existential**: a pullback of the middle term has to be *constructed*,
and the construction is the cone, whose universal property needs the base change of
`C(𝟙_{P'''[-1]})`, not just that of `P'''[-1]`. Those are different data. A morphism out of a
cone on an identity is a degree `-1` right `A`-linear family, which is a homomorphism of
*graded* modules into `SheafOfModules.DifferentialGradedModule.gradedShiftDown`, whereas every
clause of `SheafOfModules.IsGoodToposBaseChange` speaks of homomorphisms of *differential*
graded modules out of the module in question; no clause of it constrains a graded-module datum.

So the base change of the cone on an identity is an **input** to this lemma, not a consequence
of it, and the lemma holds here only because the source of the cone is a free module, for which
that input is available —
`SheafOfModules.coneIdentityFreeDGModule_isGoodToposBaseChange` together with
`SheafOfModules.freeDGModuleToposHomEquiv_inclusion`. The second of those, the compatibility of
the free module's base change with the cone's inclusion, is what makes the two pushout data
match: bare corepresentability of the three corners would not identify the span.

The four comparisons used are all formal consequences of the corepresentability data:
`SheafOfModules.homEquiv_eq_unit_comp` expands a corepresentability bijection as the unit
followed by the direct image of the morphism, and
`SheafOfModules.freeDGModuleToposHomEquiv_baseChangeHom_comp` is the resulting compatibility of
the free module's base change with `g`. The two round trips and the naturality are then
`ConePackage.pushoutDesc_uniq`, applied on whichever of the two topoi the morphism being
characterized lives over.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.SheafOfGradedSets Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules

open DifferentialGradedModule

section ToposPullback

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J (Type w)]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [HasSheafify K (Type w)]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (ν : toSetSheaf (toRingCat J Osharp) ⋙ f.pushforward ≅
    G ⋙ toSetSheaf (toRingCat K Psharp))
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
  (S : SheafOfGradedSets.{w} K)

/-! ### The base change of a morphism out of a free module -/

section BaseChange

variable {P : DifferentialGradedModule.{w, w, w} A} {TP : DifferentialGradedModule.{w, w, w} B}
  (g : freeDGModule S A ⟶ P)
  (e : ((toposPushforward G ψ hψ) ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy TP)

/-- **The unit of a corepresentability datum for the base change of `P`**: the image of the
identity, a morphism `P ⟶ f_{*,ψ}T_P`. -/
noncomputable abbrev baseChangeUnit : P ⟶ (toposPushforward G ψ hψ).obj TP :=
  e.homEquiv (𝟙 TP)

omit [HasSheafify J (Type w)] [HasSheafify K (Type w)] in
/-- **A corepresentability bijection is the unit followed by the direct image.** -/
theorem homEquiv_eq_unit_comp {Q : DifferentialGradedModule.{w, w, w} B} (k : TP ⟶ Q) :
    e.homEquiv k =
      baseChangeUnit G ψ hψ e ≫ (toposPushforward G ψ hψ).map k :=
  (congrArg e.homEquiv (Category.id_comp k)).symm.trans (e.homEquiv_comp k (𝟙 TP))

omit [HasSheafify J (Type w)] [HasSheafify K (Type w)] in
/-- **A corepresentability bijection is natural in the target**, with the composition on the
right written out rather than as the action of the corepresented functor. -/
theorem homEquiv_comp_right {Q Q' : DifferentialGradedModule.{w, w, w} B} (k : TP ⟶ Q)
    (v : Q ⟶ Q') :
    e.homEquiv (k ≫ v) = e.homEquiv k ≫ (toposPushforward G ψ hψ).map v :=
  e.homEquiv_comp v k

/-- **The base change of `g : A[S] ⟶ P`**: the morphism `B[f⁻¹S] ⟶ T_P` corresponding, under the
universal property of `B[f⁻¹S]`, to `g` followed by the unit. -/
noncomputable def baseChangeHom :
    freeDGModule (SheafOfGradedSets.inverseImage f S) B ⟶ TP :=
  (freeDGModuleToposHomEquiv G f ν ψ hψ S TP).symm (g ≫ baseChangeUnit G ψ hψ e)

/-- **The base change of `g` is compatible with `g`**: transporting `g' ≫ k` across the free
module's base change gives `g` followed by the transport of `k`. -/
theorem freeDGModuleToposHomEquiv_baseChangeHom_comp
    {Q : DifferentialGradedModule.{w, w, w} B} (k : TP ⟶ Q) :
    freeDGModuleToposHomEquiv G f ν ψ hψ S Q (baseChangeHom G f ν ψ hψ S g e ≫ k) =
      g ≫ e.homEquiv k := by
  rw [freeDGModuleToposHomEquiv_comp, baseChangeHom, Equiv.apply_symm_apply,
    homEquiv_eq_unit_comp, Category.assoc]

/-! ### The two pushout conditions -/

/-- The cocone condition on the target topos: the two coordinates of a morphism out of `C(g')`,
transported, agree on `A[S]`. -/
theorem coneToposCondition_target (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone (baseChangeHom G f ν ψ hψ S g e) ⟶ Q) :
    (conePackage (𝟙 (freeDGModule S A))).inclusion ≫
        coneIdentityToposHomEquiv G f ν ψ hψ S Q
          ((conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId ≫ w) =
      g ≫ e.homEquiv ((conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion ≫ w) := by
  have hw : (conePackage (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B))).inclusion ≫
        ((conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId ≫ w) =
      baseChangeHom G f ν ψ hψ S g e ≫
        ((conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion ≫ w) := by
    rw [← Category.assoc, (conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion_fromConeId,
      Category.assoc]
  rw [← freeDGModuleToposHomEquiv_inclusion, hw,
    freeDGModuleToposHomEquiv_baseChangeHom_comp]

/-- The cocone condition on the source topos: the two coordinates of a morphism out of `C(g)`,
transported back, agree on `B[f⁻¹S]`. -/
theorem coneToposCondition_source (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone g ⟶ (toposPushforward G ψ hψ).obj Q) :
    (conePackage (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B))).inclusion ≫
        (coneIdentityToposHomEquiv G f ν ψ hψ S Q).symm
          ((conePackage g).fromConeId ≫ w) =
      baseChangeHom G f ν ψ hψ S g e ≫
        e.homEquiv.symm ((conePackage g).inclusion ≫ w) := by
  refine (freeDGModuleToposHomEquiv G f ν ψ hψ S Q).injective ?_
  rw [freeDGModuleToposHomEquiv_inclusion, Equiv.apply_symm_apply,
    freeDGModuleToposHomEquiv_baseChangeHom_comp, Equiv.apply_symm_apply, ← Category.assoc,
    (conePackage g).inclusion_fromConeId, Category.assoc]

/-! ### The bijection -/

/-- **The morphism out of `C(g)` determined by a morphism out of `C(g')`**: the descent, along
the pushout presenting `C(g)`, of the two transported coordinates. -/
noncomputable def coneToposDesc (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone (baseChangeHom G f ν ψ hψ S g e) ⟶ Q) :
    cone g ⟶ (toposPushforward G ψ hψ).obj Q :=
  (conePackage g).pushoutDesc
    (coneIdentityToposHomEquiv G f ν ψ hψ S Q
      ((conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId ≫ w))
    (e.homEquiv ((conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion ≫ w))
    (coneToposCondition_target G f ν ψ hψ S g e Q w)

/-- The restriction of `coneToposDesc` to `C(𝟙_{A[S]})` is the transport of the restriction of `w`
to `C(𝟙_{B[f⁻¹S]})`. -/
theorem fromConeId_coneToposDesc (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone (baseChangeHom G f ν ψ hψ S g e) ⟶ Q) :
    (conePackage g).fromConeId ≫ coneToposDesc G f ν ψ hψ S g e Q w =
      coneIdentityToposHomEquiv G f ν ψ hψ S Q
        ((conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId ≫ w) :=
  (conePackage g).fromConeId_pushoutDesc _ _ _

/-- The restriction of `coneToposDesc` to `P` is the transport of the restriction of `w` to
`T_P`. -/
theorem inclusion_coneToposDesc (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone (baseChangeHom G f ν ψ hψ S g e) ⟶ Q) :
    (conePackage g).inclusion ≫ coneToposDesc G f ν ψ hψ S g e Q w =
      e.homEquiv ((conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion ≫ w) :=
  (conePackage g).inclusion_pushoutDesc _ _ _

/-- **The morphism out of `C(g')` determined by a morphism out of `C(g)`**: the descent, along
the pushout presenting `C(g')`, of the two coordinates transported back. -/
noncomputable def coneToposUndesc (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone g ⟶ (toposPushforward G ψ hψ).obj Q) :
    cone (baseChangeHom G f ν ψ hψ S g e) ⟶ Q :=
  (conePackage (baseChangeHom G f ν ψ hψ S g e)).pushoutDesc
    ((coneIdentityToposHomEquiv G f ν ψ hψ S Q).symm ((conePackage g).fromConeId ≫ w))
    (e.homEquiv.symm ((conePackage g).inclusion ≫ w))
    (coneToposCondition_source G f ν ψ hψ S g e Q w)

/-- The restriction of `coneToposUndesc` to `C(𝟙_{B[f⁻¹S]})` is the transport back of the
restriction of `w` to `C(𝟙_{A[S]})`. -/
theorem fromConeId_coneToposUndesc (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone g ⟶ (toposPushforward G ψ hψ).obj Q) :
    (conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId ≫
        coneToposUndesc G f ν ψ hψ S g e Q w =
      (coneIdentityToposHomEquiv G f ν ψ hψ S Q).symm ((conePackage g).fromConeId ≫ w) :=
  (conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId_pushoutDesc _ _ _

/-- The restriction of `coneToposUndesc` to `T_P` is the transport back of the restriction of `w`
to `P`. -/
theorem inclusion_coneToposUndesc (Q : DifferentialGradedModule.{w, w, w} B)
    (w : cone g ⟶ (toposPushforward G ψ hψ).obj Q) :
    (conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion ≫
        coneToposUndesc G f ν ψ hψ S g e Q w =
      e.homEquiv.symm ((conePackage g).inclusion ≫ w) :=
  (conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion_pushoutDesc _ _ _

/-- **The pullback of `C(g)` along `f` is `C(g')`**, as a bijection of hom-sets: both sides are
morphisms out of a pushout, and the three corners of the span correspond. -/
noncomputable def coneToposHomEquiv (Q : DifferentialGradedModule.{w, w, w} B) :
    (cone (baseChangeHom G f ν ψ hψ S g e) ⟶ Q) ≃
      (cone g ⟶ (toposPushforward G ψ hψ).obj Q) where
  toFun w := coneToposDesc G f ν ψ hψ S g e Q w
  invFun w := coneToposUndesc G f ν ψ hψ S g e Q w
  left_inv w := by
    refine (ConePackage.pushoutDesc_uniq (conePackage (baseChangeHom G f ν ψ hψ S g e))
      ((coneIdentityToposHomEquiv G f ν ψ hψ S Q).symm
        ((conePackage g).fromConeId ≫ coneToposDesc G f ν ψ hψ S g e Q w))
      (e.homEquiv.symm ((conePackage g).inclusion ≫ coneToposDesc G f ν ψ hψ S g e Q w))
      (coneToposCondition_source G f ν ψ hψ S g e Q (coneToposDesc G f ν ψ hψ S g e Q w))
      w ?_ ?_).symm
    · rw [fromConeId_coneToposDesc, Equiv.symm_apply_apply]
    · rw [inclusion_coneToposDesc, Equiv.symm_apply_apply]
  right_inv w := by
    refine (ConePackage.pushoutDesc_uniq (conePackage g)
      (coneIdentityToposHomEquiv G f ν ψ hψ S Q
        ((conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId ≫
          coneToposUndesc G f ν ψ hψ S g e Q w))
      (e.homEquiv ((conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion ≫
        coneToposUndesc G f ν ψ hψ S g e Q w))
      (coneToposCondition_target G f ν ψ hψ S g e Q (coneToposUndesc G f ν ψ hψ S g e Q w))
      w ?_ ?_).symm
    · rw [fromConeId_coneToposUndesc, Equiv.apply_symm_apply]
    · rw [inclusion_coneToposUndesc, Equiv.apply_symm_apply]

/-- **The bijection is natural in `Q`.** Both sides are morphisms out of the pushout presenting
`C(g)`, so they are compared on the two corners of the span, where the naturality is that of
the base change of `C(𝟙_{A[S]})` and of the corepresentability datum for `P`. -/
theorem coneToposHomEquiv_comp {Q Q' : DifferentialGradedModule.{w, w, w} B} (v : Q ⟶ Q')
    (w : cone (baseChangeHom G f ν ψ hψ S g e) ⟶ Q) :
    coneToposHomEquiv G f ν ψ hψ S g e Q' (w ≫ v) =
      coneToposHomEquiv G f ν ψ hψ S g e Q w ≫ (toposPushforward G ψ hψ).map v := by
  refine (ConePackage.pushoutDesc_uniq (conePackage g)
    (coneIdentityToposHomEquiv G f ν ψ hψ S Q'
      ((conePackage (baseChangeHom G f ν ψ hψ S g e)).fromConeId ≫ w ≫ v))
    (e.homEquiv ((conePackage (baseChangeHom G f ν ψ hψ S g e)).inclusion ≫ w ≫ v))
    (coneToposCondition_target G f ν ψ hψ S g e Q' (w ≫ v))
    (coneToposDesc G f ν ψ hψ S g e Q w ≫ (toposPushforward G ψ hψ).map v) ?_ ?_).symm
  · rw [← Category.assoc, fromConeId_coneToposDesc, ← coneIdentityToposHomEquiv_comp,
      Category.assoc]
  · rw [← Category.assoc, inclusion_coneToposDesc, ← homEquiv_comp_right, Category.assoc]

/-- **The corepresentability witness.** `C(g')` corepresents `Q ↦ Hom_A(C(g), f_{*,ψ}Q)`. -/
noncomputable def coneToposCorepresentableBy :
    ((toposPushforward G ψ hψ) ⋙ coyoneda.obj (Opposite.op (cone g))).CorepresentableBy
      (cone (baseChangeHom G f ν ψ hψ S g e)) where
  homEquiv {Q} := coneToposHomEquiv G f ν ψ hψ S g e Q
  homEquiv_comp v w := coneToposHomEquiv_comp G f ν ψ hψ S g e v w

/-! ### Conditions (1) and (2) of Tag 0FSA for the pullback -/

section Flat

variable [HasSheafify J AddCommGrpCat.{w}]

/-- **The constructed pullback of `C(g)` is flat as a graded module and K-flat**, given that the
pullback `T_P` of `P` is. It is the cone of `g' : B[f⁻¹S] ⟶ T_P`, so it sits in an admissible
short exact sequence whose two ends are `T_P` and the shift of the free module `B[f⁻¹S]`; both
conditions satisfy two-out-of-three along such a sequence. -/
theorem isGradedFlat_isKFlat_cone_baseChangeHom
    (hT : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded TP) ∧
      RelativeTensor.IsKFlat TP) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded
        (cone (baseChangeHom G f ν ψ hψ S g e))) ∧
      RelativeTensor.IsKFlat (cone (baseChangeHom G f ν ψ hψ S g e)) :=
  isGradedFlat_and_isKFlat_cone (baseChangeHom G f ν ψ hψ S g e)
    ⟨freeDGModule_isGradedFlat B (SheafOfGradedSets.inverseImage f S),
      freeDGModule_isKFlat (SheafOfGradedSets.inverseImage f S) B⟩ hT

include f ν e in
/-- **Every object corepresenting the pullback of `C(g)` is flat as a graded module and
K-flat**, given that the pullback of `P` is. -/
theorem isGradedFlat_isKFlat_of_coneToposCorepresentableBy
    (hT : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded TP) ∧
      RelativeTensor.IsKFlat TP)
    {T' : DifferentialGradedModule.{w, w, w} B}
    (e' : ((toposPushforward G ψ hψ) ⋙
      coyoneda.obj (Opposite.op (cone g))).CorepresentableBy T') :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded T') ∧
      RelativeTensor.IsKFlat T' := by
  have h := isGradedFlat_isKFlat_cone_baseChangeHom G f ν ψ hψ S g e hT
  have i := e'.uniqueUpToIso (coneToposCorepresentableBy G f ν ψ hψ S g e)
  exact ⟨RelativeTensor.IsGradedFlat.of_iso (GradedModule.ofDifferentialGradedIso i).symm h.1,
    RelativeTensor.IsKFlat.of_iso i.symm h.2⟩

end Flat

end BaseChange

end ToposPullback

/-! ### Goodness is closed under the cone of a morphism out of a free module -/

section Predicate

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **Goodness is closed under the cone of a morphism out of a free differential graded
module.** If `P` is good and `g : A[S] ⟶ P` is a homomorphism, then the cone of `g` is good.

This is the induction step of the tower of the first proof of Tag 0FSH, whose stages are the
twisted extensions of `SheafOfModules.DifferentialGradedModule.twistedExtension` — the cones of
the homomorphisms out of free modules that
`SheafOfModules.DifferentialGradedModule.exists_towerStep` produces.

Conditions (1) and (2) are two-out-of-three along the admissible short exact sequence of the
cone. Condition (3) is the pushout presentation of the cone: the base change of `A[S]` is
Tag 0FSG, that of `C(𝟙_{A[S]})` is
`SheafOfModules.coneIdentityFreeDGModule_isGoodToposBaseChange`, that of `P` is the hypothesis,
and the three match up along the span because the base change of `A[S] ⟶ C(𝟙_{A[S]})` is the
corresponding inclusion — `SheafOfModules.freeDGModuleToposHomEquiv_inclusion`. The pushout on
the target topos is again a cone, which is what the flatness clause needs: it is the admissible
short exact sequence of *that* cone, not the pushout, that gives conditions (1) and (2) of the
base change. -/
theorem cone_freeDGModule_isGoodToposBaseChange [HasWeakSheafify Y.J (Type w)]
    (S : Stacks.SheafOfGradedSets.{w} Y.J) {P : DifferentialGradedModule.{w, w, w} A}
    (hP : IsGoodToposBaseChange.{w, v₁, u₁} P) (g : freeDGModule S A ⟶ P) :
    IsGoodToposBaseChange.{w, v₁, u₁} (cone g) := by
  obtain ⟨h₁, h₂⟩ := isGradedFlat_and_isKFlat_cone g
    ⟨freeDGModule_isGradedFlat A S, freeDGModule_isKFlat S A⟩ ⟨hP.1, hP.2.1⟩
  refine ⟨h₁, h₂, ?_⟩
  intro X _ _ _ _ _ _ fm B ψ hψ
  obtain ⟨TP, ⟨eP⟩⟩ := (hP.2.2 fm B ψ hψ).1
  have hT := (hP.2.2 fm B ψ hψ).2 TP eP
  exact ⟨⟨cone (baseChangeHom (toposDirectImageModules fm) fm.toToposHom
        (toposDirectImageModulesSetIso fm) ψ hψ S g eP),
      ⟨coneToposCorepresentableBy (toposDirectImageModules fm) fm.toToposHom
        (toposDirectImageModulesSetIso fm) ψ hψ S g eP⟩⟩,
    fun _T' e' => isGradedFlat_isKFlat_of_coneToposCorepresentableBy
      (toposDirectImageModules fm) fm.toToposHom (toposDirectImageModulesSetIso fm) ψ hψ S g eP
      hT e'⟩

end Predicate

end SheafOfModules

end
