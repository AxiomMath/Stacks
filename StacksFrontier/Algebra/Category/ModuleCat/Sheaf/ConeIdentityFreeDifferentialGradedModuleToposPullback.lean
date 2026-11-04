module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeIdentityFreeDifferentialGradedModuleSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodResolutionDataConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback

/-!
# The pullback of the cone on the identity of a free differential graded module

Let `f : X ⟶ Y` be a morphism of ringed topoi, let `A` be a sheaf of differential graded
`O_Y`-algebras, let `B` be a sheaf of differential graded `O_X`-algebras, let `ψ : A ⟶ f_*B` be a
unital homomorphism, and let `S` be a sheaf of graded sets on `Y`. **The cone on the identity of
the free differential graded `B`-module `B[f⁻¹S]` corepresents morphisms out of the cone on the
identity of `A[S]` into the direct image**, that is

`Hom_B(C(𝟙_{B[f⁻¹S]}), Q) ≃ Hom_A(C(𝟙_{A[S]}), f_{*,ψ}Q)` naturally in `Q`,

**and that bijection is compatible with the two cones' inclusions.** The chain is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`
with the closedness condition dropped from both ends:

`Hom_B(C(𝟙_{B[f⁻¹S]}), Q)`
  `≃ ∀ i, ((f⁻¹S)_i ⟶ Q^{i-1})`         the universal property of `C(𝟙_{B[f⁻¹S]})` on `X`
  `≃ ∀ i, (f⁻¹(S_i) ⟶ Q^{i-1})`          the grading survives the inverse image
  `≃ ∀ i, (S_i ⟶ f_* Q^{i-1})`           the adjunction `f⁻¹ ⊣ f_*` of sheaves of sets
  `≃ ∀ i, (S_i ⟶ (f_{*,ψ}Q)^{i-1})`      the comparison `ν` in degree `i - 1`
  `≃ Hom_A(C(𝟙_{A[S]}), f_{*,ψ}Q)`       the universal property of `C(𝟙_{A[S]})` on `Y`,

where `S_i` is the sheaf of degree-`i` local sections of `S`. The middle three steps are the
three of that file; only the two ends change, the sheaf of **closed** degree-`i` sections of `Q`
being replaced by the sheaf of **all** degree-`(i-1)` sections, and the fourth step accordingly
simplifying from `closedSectionToposPushforwardIso` to the comparison `ν` itself.

## Main definitions

* `SheafOfModules.inverseImageDegreeStep` is the common first-and-second step, for an arbitrary
  sheaf of sets on the source: the grading of the inverse image followed by the adjunction. The
  closed chain of the file above runs through it too.
* `SheafOfModules.toposDegreeStepSections` is the per-degree step of the chain, and
  `SheafOfModules.coneIdentityToposHomEquiv` the composite bijection.
* `SheafOfModules.coneIdentityToposCorepresentableBy`: **the corepresentability witness**, in
  Mathlib's `CategoryTheory.Functor.CorepresentableBy`.

## Main results

* `SheafOfModules.coneIdentityToposHomEquiv_comp`: the bijection is natural in `Q`.
* `SheafOfModules.freeDGModuleToposHomEquiv_inclusion`: **the bijection is compatible with the
  two cones' inclusions** — the base change of `A[S] ⟶ C(𝟙_{A[S]})` is `B[f⁻¹S] ⟶ C(𝟙_{B[f⁻¹S]})`.
  This is what identifies the base change of the cone *as a cone*, which corepresentability alone
  does not: flatness of the base change comes from the admissible short exact sequence of the
  cone, not from any colimit presentation of it, and that sequence is only available once the
  inclusion is identified.
* `SheafOfModules.isGradedFlat_isKFlat_coneIdentity_inverseImage` and
  `SheafOfModules.isGradedFlat_isKFlat_of_coneIdentityToposCorepresentableBy`: conditions (1) and
  (2) of Tag 0FSA for the constructed pullback and for every object corepresenting it. The first
  is `isGradedFlat_and_isKFlat_cone` at the identity of `B[f⁻¹S]`: the cone sits in the admissible
  short exact sequence `0 → B[f⁻¹S] → C(𝟙) → B[f⁻¹S][1] → 0`, both ends are flat and K-flat, and
  both conditions satisfy two-out-of-three along such a sequence.
* `SheafOfModules.coneIdentityFreeDGModule_isGoodToposBaseChange`: **the cone on the identity of
  `A[S]` is good** in the sense of `SheafOfModules.IsGoodToposBaseChange`.

## Implementation notes

The three middle steps are not reproved. `SheafOfModules.inverseImageDegreeStep` is extracted
from the closed chain — `SheafOfModules.toposDegreeStep` is now that step followed by
`closedSectionToposPushforwardIso`, which is what `toposDegreeStep_apply` already said — and the
step here is the same one followed by the comparison `ν` in degree `i - 1`, which is
`SheafOfModules.DifferentialGradedModule.toposPushforwardPieceIso`. The closedness step of the
source's chain drops out: there is nothing to compare, both sides being the plain sections of a
homogeneous piece.

The compatibility with the inclusions is proved on the canonical generators of `A[S]`, by
`SheafOfModules.dgHom_ext_generator`. There each side is the transport of a morphism of sheaves
of sets, and the two transports differ exactly by `ν`'s naturality at the differential
`Q^{i-1} ⟶ Q^i` of `Q`: the closed side carries the generators the cone's inclusion names, the
plain side the sections the cone's own universal property names, and
`SheafOfModules.freeDGModuleHomToClosed_comp_ι_inclusion` says the first is the differential of
the second.

Flatness is **not** obtained from a colimit presentation of the cone. Pushouts do not preserve
flatness; what the cone gives is an admissible short exact sequence, split in the underlying
graded category, and conditions (1) and (2) satisfy two-out-of-three along one. That is Tag 0FSC,
and `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_cone` is its statement at a
cone.

The hypotheses are those of `FreeDifferentialGradedModuleToposPullback.lean`, with no addition.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
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

/-! ### The grading of the inverse image, followed by the adjunction -/

section DegreeStep

variable (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (S : SheafOfGradedSets.{w} K)

/-- **The first two steps of the base change of a free module's universal property**, for an
arbitrary sheaf of sets on the source: a morphism from the degree-`i` sections of `f⁻¹S` into a
sheaf of sets `Z` is a morphism from the degree-`i` sections of `S` into `f_*Z`. Read the source
through `Stacks.inverseImageDegreeFiberIso` and transpose across `f⁻¹ ⊣ f_*`. -/
noncomputable def inverseImageDegreeStep (Z : Sheaf J (Type w)) (i : ℤ) :
    (degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶ Z) ≃
      (degreeFiberSheaf S i ⟶ f.pushforward.obj Z) :=
  (Iso.homCongr (inverseImageDegreeFiberIso f S i) (Iso.refl Z)).symm.trans
    (f.adj.homEquiv (degreeFiberSheaf S i) Z)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}] in
/-- `inverseImageDegreeStep f S Z i F` is the transpose across `f⁻¹ ⊣ f_*` of the composite of
`(inverseImageDegreeFiberIso f S i).hom` with `F`. -/
@[simp]
theorem inverseImageDegreeStep_apply (Z : Sheaf J (Type w)) (i : ℤ)
    (F : degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶ Z) :
    inverseImageDegreeStep f S Z i F =
      f.adj.homEquiv (degreeFiberSheaf S i) Z
        ((inverseImageDegreeFiberIso f S i).hom ≫ F) := by
  show f.adj.homEquiv (degreeFiberSheaf S i) Z
      ((inverseImageDegreeFiberIso f S i).hom ≫ F ≫ (Iso.refl Z).inv) = _
  rw [Iso.refl_inv, Category.comp_id]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}] in
/-- **The first two steps are natural in the target sheaf of sets.** -/
theorem inverseImageDegreeStep_comp {Z Z' : Sheaf J (Type w)} (i : ℤ)
    (F : degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶ Z) (k : Z ⟶ Z') :
    inverseImageDegreeStep f S Z' i (F ≫ k) =
      inverseImageDegreeStep f S Z i F ≫ f.pushforward.map k := by
  rw [inverseImageDegreeStep_apply, inverseImageDegreeStep_apply,
    ← f.adj.homEquiv_naturality_right, Category.assoc]

end DegreeStep

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (ν : toSetSheaf (toRingCat J Osharp) ⋙ f.pushforward ≅
    G ⋙ toSetSheaf (toRingCat K Psharp))
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
  (S : SheafOfGradedSets.{w} K)

/-- **The per-degree step of the chain.** A morphism from the degree-`i` sections of `f⁻¹S` into
the degree-`(i-1)` sections of `Q` is a morphism from the degree-`i` sections of `S` into the
degree-`(i-1)` sections of the direct image: transpose across `f⁻¹ ⊣ f_*` and apply the
comparison `ν` in degree `i - 1`. -/
noncomputable def toposDegreeStepSections (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ) :
    (degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶
        (toSetSheaf (toRingCat J Osharp)).obj (Q.complex.X (i - 1))) ≃
      (degreeFiberSheaf S i ⟶ (toSetSheaf (toRingCat K Psharp)).obj
        (((toposPushforward G ψ hψ).obj Q).complex.X (i - 1))) :=
  (inverseImageDegreeStep f S ((toSetSheaf (toRingCat J Osharp)).obj
      (Q.complex.X (i - 1))) i).trans
    (Iso.homCongr (Iso.refl (degreeFiberSheaf S i))
      (toposPushforwardPieceIso G f ν ψ hψ Q (i - 1)))

/-- `toposDegreeStepSections G f ν ψ hψ S Q i F` is `inverseImageDegreeStep f S _ i F` followed by
the comparison `toposPushforwardPieceIso G f ν ψ hψ Q (i - 1)`. -/
@[simp]
theorem toposDegreeStepSections_apply (Q : DifferentialGradedModule.{w, w, w} B) (i : ℤ)
    (F : degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶
      (toSetSheaf (toRingCat J Osharp)).obj (Q.complex.X (i - 1))) :
    toposDegreeStepSections G f ν ψ hψ S Q i F =
      inverseImageDegreeStep f S ((toSetSheaf (toRingCat J Osharp)).obj
          (Q.complex.X (i - 1))) i F ≫
        (toposPushforwardPieceIso G f ν ψ hψ Q (i - 1)).hom := by
  show (Iso.refl (degreeFiberSheaf S i)).inv ≫
      inverseImageDegreeStep f S _ i F ≫
        (toposPushforwardPieceIso G f ν ψ hψ Q (i - 1)).hom = _
  rw [Iso.refl_inv, Category.id_comp]

/-- **The per-degree step is natural in `Q`.** -/
theorem toposDegreeStepSections_comp {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q')
    (i : ℤ) (F : degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i ⟶
      (toSetSheaf (toRingCat J Osharp)).obj (Q.complex.X (i - 1))) :
    toposDegreeStepSections G f ν ψ hψ S Q' i
        (F ≫ (toSetSheaf (toRingCat J Osharp)).map (g.toHomologicalComplex.f (i - 1))) =
      toposDegreeStepSections G f ν ψ hψ S Q i F ≫
        (toSetSheaf (toRingCat K Psharp)).map
          (((toposPushforward G ψ hψ).map g).toHomologicalComplex.f (i - 1)) := by
  rw [toposDegreeStepSections_apply, toposDegreeStepSections_apply,
    inverseImageDegreeStep_comp, Category.assoc,
    toposPushforwardPieceIso_naturality G f ν ψ hψ g (i - 1), Category.assoc]

/-! ### The bijection -/

/-- **The pullback of `C(𝟙_{A[S]})` along `f` is `C(𝟙_{B[f⁻¹S]})`**, as a bijection of hom-sets:
a morphism `C(𝟙_{B[f⁻¹S]}) ⟶ Q` is a morphism `C(𝟙_{A[S]}) ⟶ f_{*,ψ}Q`. -/
noncomputable def coneIdentityToposHomEquiv (Q : DifferentialGradedModule.{w, w, w} B) :
    (cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B)) ⟶ Q) ≃
      (cone (𝟙 (freeDGModule S A)) ⟶ (toposPushforward G ψ hψ).obj Q) :=
  (coneIdentityHomEquiv (SheafOfGradedSets.inverseImage f S) B Q).trans
    ((Equiv.piCongrRight (toposDegreeStepSections G f ν ψ hψ S Q)).trans
      (coneIdentityHomEquiv S A ((toposPushforward G ψ hψ).obj Q)).symm)

/-- `coneIdentityToposHomEquiv G f ν ψ hψ S Q h` is the morphism out of `C(𝟙_{A[S]})` whose
degree-`i` datum is `toposDegreeStepSections G f ν ψ hψ S Q i` applied to the degree-`i` datum
of `h`. -/
theorem coneIdentityToposHomEquiv_apply (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B)) ⟶ Q) :
    coneIdentityToposHomEquiv G f ν ψ hψ S Q h =
      (coneIdentityHomEquiv S A ((toposPushforward G ψ hψ).obj Q)).symm (fun i =>
        toposDegreeStepSections G f ν ψ hψ S Q i
          (coneIdentityHomEquiv (SheafOfGradedSets.inverseImage f S) B Q h i)) :=
  rfl

/-- **The bijection is natural in `Q`.** Each of its three steps is. -/
theorem coneIdentityToposHomEquiv_comp {Q Q' : DifferentialGradedModule.{w, w, w} B}
    (g : Q ⟶ Q')
    (h : cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B)) ⟶ Q) :
    coneIdentityToposHomEquiv G f ν ψ hψ S Q' (h ≫ g) =
      coneIdentityToposHomEquiv G f ν ψ hψ S Q h ≫ (toposPushforward G ψ hψ).map g := by
  rw [coneIdentityToposHomEquiv_apply, coneIdentityToposHomEquiv_apply]
  refine Eq.trans (congrArg
    (coneIdentityHomEquiv S A ((toposPushforward G ψ hψ).obj Q')).symm (funext fun i => ?_))
    (coneIdentityHomEquiv_symm_comp S A ((toposPushforward G ψ hψ).obj Q) _ _)
  rw [coneIdentityHomEquiv_comp, toposDegreeStepSections_comp]

/-- **The corepresentability witness.** `C(𝟙_{B[f⁻¹S]})` corepresents
`Q ↦ Hom_A(C(𝟙_{A[S]}), f_{*,ψ}Q)`, which is the universal property of the pullback of
`C(𝟙_{A[S]})` at a morphism of ringed topoi — constructed, not assumed. -/
noncomputable def coneIdentityToposCorepresentableBy :
    ((toposPushforward G ψ hψ) ⋙
        coyoneda.obj (Opposite.op (cone (𝟙 (freeDGModule S A))))).CorepresentableBy
      (cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B))) where
  homEquiv {Q} := coneIdentityToposHomEquiv G f ν ψ hψ S Q
  homEquiv_comp g h := coneIdentityToposHomEquiv_comp G f ν ψ hψ S g h

include f ν in
/-- **The direct image of differential graded modules has a partial left adjoint defined at
`C(𝟙_{A[S]})`**, in the sense of Mathlib's `CategoryTheory.Functor.leftAdjointObjIsDefined`. -/
theorem leftAdjointObjIsDefined_coneIdentityFreeDGModule :
    (toposPushforward G ψ hψ).leftAdjointObjIsDefined (cone (𝟙 (freeDGModule S A))) :=
  (coneIdentityToposCorepresentableBy G f ν ψ hψ S).isCorepresentable

/-- **Every object corepresenting the pullback of `C(𝟙_{A[S]})` is `C(𝟙_{B[f⁻¹S]})`.** -/
noncomputable def isoConeIdentityOfToposCorepresentableBy
    {T : DifferentialGradedModule.{w, w, w} B}
    (e : ((toposPushforward G ψ hψ) ⋙
      coyoneda.obj (Opposite.op (cone (𝟙 (freeDGModule S A))))).CorepresentableBy T) :
    T ≅ cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B)) :=
  e.uniqueUpToIso (coneIdentityToposCorepresentableBy G f ν ψ hψ S)

/-! ### Compatibility with the two cones' inclusions -/

/-- **The bijection is compatible with the two cones' inclusions**: the base change of the
inclusion `A[S] ⟶ C(𝟙_{A[S]})` is the inclusion `B[f⁻¹S] ⟶ C(𝟙_{B[f⁻¹S]})`. Both sides are
morphisms out of a free module, so the identity is checked on the canonical generators; there it
is `ν`'s naturality at the differential `Q^{i-1} ⟶ Q^i`, the closed side carrying the generators
the cone's inclusion names and the plain side the sections the cone's own universal property
names. -/
theorem freeDGModuleToposHomEquiv_inclusion (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B)) ⟶ Q) :
    freeDGModuleToposHomEquiv G f ν ψ hψ S Q
        ((conePackage (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B))).inclusion ≫ h) =
      (conePackage (𝟙 (freeDGModule S A))).inclusion ≫
        coneIdentityToposHomEquiv G f ν ψ hψ S Q h := by
  refine dgHom_ext_generator S A ((toposPushforward G ψ hψ).obj Q) fun i V s hs => ?_
  have hν : f.pushforward.map ((toSetSheaf (toRingCat J Osharp)).map
        (Q.complex.d (i - 1) i)) ≫ (toposPushforwardPieceIso G f ν ψ hψ Q i).hom =
      (toposPushforwardPieceIso G f ν ψ hψ Q (i - 1)).hom ≫
        (toSetSheaf (toRingCat K Psharp)).map
          (((toposPushforward G ψ hψ).obj Q).complex.d (i - 1) i) :=
    ν.hom.naturality (Q.complex.d (i - 1) i)
  have hsquare : toposDegreeStep G f ν ψ hψ S Q i
        (freeDGModuleHomToClosed (SheafOfGradedSets.inverseImage f S) B Q
          ((conePackage (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B))).inclusion ≫ h)
          i) ≫
      closedSectionι ((toposPushforward G ψ hψ).obj Q) i =
    toposDegreeStepSections G f ν ψ hψ S Q i
        (coneIdentityHomEquiv (SheafOfGradedSets.inverseImage f S) B Q h i) ≫
      (toSetSheaf (toRingCat K Psharp)).map
        (((toposPushforward G ψ hψ).obj Q).complex.d (i - 1) i) :=
    calc toposDegreeStep G f ν ψ hψ S Q i
            (freeDGModuleHomToClosed (SheafOfGradedSets.inverseImage f S) B Q
              ((conePackage (𝟙 (freeDGModule
                (SheafOfGradedSets.inverseImage f S) B))).inclusion ≫ h) i) ≫
          closedSectionι ((toposPushforward G ψ hψ).obj Q) i
        = f.adj.homEquiv (degreeFiberSheaf S i) (closedSectionSheaf Q i)
              ((inverseImageDegreeFiberIso f S i).hom ≫
                freeDGModuleHomToClosed (SheafOfGradedSets.inverseImage f S) B Q
                  ((conePackage (𝟙 (freeDGModule
                    (SheafOfGradedSets.inverseImage f S) B))).inclusion ≫ h) i) ≫
            f.pushforward.map (closedSectionι Q i) ≫
              (toposPushforwardPieceIso G f ν ψ hψ Q i).hom := by
          rw [toposDegreeStep_apply, Category.assoc,
            closedSectionToposPushforwardIso_hom_comp_ι]
      _ = f.adj.homEquiv (degreeFiberSheaf S i)
              ((toSetSheaf (toRingCat J Osharp)).obj (Q.complex.X i))
              ((inverseImageDegreeFiberIso f S i).hom ≫
                coneIdentityHomEquiv (SheafOfGradedSets.inverseImage f S) B Q h i ≫
                  (toSetSheaf (toRingCat J Osharp)).map (Q.complex.d (i - 1) i)) ≫
            (toposPushforwardPieceIso G f ν ψ hψ Q i).hom := by
          rw [← Category.assoc, ← f.adj.homEquiv_naturality_right, Category.assoc,
            freeDGModuleHomToClosed_comp_ι_inclusion]
      _ = f.adj.homEquiv (degreeFiberSheaf S i)
              ((toSetSheaf (toRingCat J Osharp)).obj (Q.complex.X i))
              (((inverseImageDegreeFiberIso f S i).hom ≫
                  coneIdentityHomEquiv (SheafOfGradedSets.inverseImage f S) B Q h i) ≫
                (toSetSheaf (toRingCat J Osharp)).map (Q.complex.d (i - 1) i)) ≫
            (toposPushforwardPieceIso G f ν ψ hψ Q i).hom := by
          rw [Category.assoc]
      _ = (f.adj.homEquiv (degreeFiberSheaf S i)
              ((toSetSheaf (toRingCat J Osharp)).obj (Q.complex.X (i - 1)))
              ((inverseImageDegreeFiberIso f S i).hom ≫
                coneIdentityHomEquiv (SheafOfGradedSets.inverseImage f S) B Q h i) ≫
            (toposPushforwardPieceIso G f ν ψ hψ Q (i - 1)).hom) ≫
            (toSetSheaf (toRingCat K Psharp)).map
              (((toposPushforward G ψ hψ).obj Q).complex.d (i - 1) i) := by
          rw [f.adj.homEquiv_naturality_right, Category.assoc, hν, ← Category.assoc]
      _ = _ := by
          rw [toposDegreeStepSections_apply, inverseImageDegreeStep_apply]
  have hLHS := dgLiftHom_generator S A ((toposPushforward G ψ hψ).obj Q)
    (generatorFamilyOfClosed S A ((toposPushforward G ψ hψ).obj Q)
      (fun j => toposDegreeStep G f ν ψ hψ S Q j
        (freeDGModuleHomToClosed (SheafOfGradedSets.inverseImage f S) B Q
          ((conePackage (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S)
            B))).inclusion ≫ h) j)))
    (generatorFamilyOfClosed_closed S A ((toposPushforward G ψ hψ).obj Q) _) i V s hs
  have hRHS : ((Hom.toHomologicalComplex ((conePackage (𝟙 (freeDGModule S A))).inclusion ≫
          coneIdentityToposHomEquiv G f ν ψ hψ S Q h)).f i).val.app V
        (freeGeneratorSection A.toGradedAlgebra S i V s hs) =
      (toposDegreeStepSections G f ν ψ hψ S Q i
          (coneIdentityHomEquiv (SheafOfGradedSets.inverseImage f S) B Q h i) ≫
        (toSetSheaf (toRingCat K Psharp)).map
          (((toposPushforward G ψ hψ).obj Q).complex.d (i - 1) i)).hom.app V ⟨s, hs⟩ := by
    refine Eq.trans (congrArg (fun φ : freeDGModule S A ⟶ (toposPushforward G ψ hψ).obj Q =>
        ((Hom.toHomologicalComplex φ).f i).val.app V
          (freeGeneratorSection A.toGradedAlgebra S i V s hs))
      (inclusion_comp_eq_dgLiftHom S A ((toposPushforward G ψ hψ).obj Q)
        (coneIdentityToposHomEquiv G f ν ψ hψ S Q h))) ?_
    refine Eq.trans (dgLiftHom_generator S A ((toposPushforward G ψ hψ).obj Q) _ _ i V s hs) ?_
    refine congrArg (fun z => homSections
        (((toposPushforward G ψ hψ).obj Q).complex.d (i - 1) i) V z) ?_
    exact congrArg (fun F => (F i).hom.app V (⟨s, hs⟩ : (degreeFiber S i).obj V))
      ((coneIdentityHomEquiv S A ((toposPushforward G ψ hψ).obj Q)).apply_symm_apply _)
  exact hLHS.trans ((congrArg (fun φ : degreeFiberSheaf S i ⟶
      (toSetSheaf (toRingCat K Psharp)).obj
        (((toposPushforward G ψ hψ).obj Q).complex.X i) =>
    φ.hom.app V (⟨s, hs⟩ : (degreeFiber S i).obj V)) hsquare).trans hRHS.symm)

/-! ### Conditions (1) and (2) of Tag 0FSA for the pullback -/

section Flat

variable [HasSheafify J AddCommGrpCat.{w}]

omit [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}] in
/-- **The constructed pullback of `C(𝟙_{A[S]})` is flat as a graded module and K-flat.** It is
the cone on the identity of `B[f⁻¹S]`, so it sits in the admissible short exact sequence
`0 → B[f⁻¹S] → C(𝟙) → B[f⁻¹S][1] → 0`; both ends are flat and K-flat, being a free module and
the shift of one, and both conditions satisfy two-out-of-three along such a sequence. -/
theorem isGradedFlat_isKFlat_coneIdentity_inverseImage :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded
        (cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B)))) ∧
      RelativeTensor.IsKFlat
        (cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B))) :=
  isGradedFlat_and_isKFlat_cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B))
    ⟨freeDGModule_isGradedFlat B (SheafOfGradedSets.inverseImage f S),
      freeDGModule_isKFlat (SheafOfGradedSets.inverseImage f S) B⟩
    ⟨freeDGModule_isGradedFlat B (SheafOfGradedSets.inverseImage f S),
      freeDGModule_isKFlat (SheafOfGradedSets.inverseImage f S) B⟩

include f ν in
/-- **Every object corepresenting the pullback of `C(𝟙_{A[S]})` is flat as a graded module and
K-flat.** This is the clause of condition (3) of Tag 0FSA for `C(𝟙_{A[S]})` at the base change
`(f, B, ψ)`, quantified over the chosen pullback rather than fixing one. -/
theorem isGradedFlat_isKFlat_of_coneIdentityToposCorepresentableBy
    {T : DifferentialGradedModule.{w, w, w} B}
    (e : ((toposPushforward G ψ hψ) ⋙
      coyoneda.obj (Opposite.op (cone (𝟙 (freeDGModule S A))))).CorepresentableBy T) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded T) ∧
      RelativeTensor.IsKFlat T :=
  ⟨RelativeTensor.IsGradedFlat.of_iso (GradedModule.ofDifferentialGradedIso
        (isoConeIdentityOfToposCorepresentableBy G f ν ψ hψ S e)).symm
      (isGradedFlat_isKFlat_coneIdentity_inverseImage f S).1,
    RelativeTensor.IsKFlat.of_iso
      (isoConeIdentityOfToposCorepresentableBy G f ν ψ hψ S e).symm
      (isGradedFlat_isKFlat_coneIdentity_inverseImage f S).2⟩

include f ν in
/-- **The clause of condition (3) of Tag 0FSA for `C(𝟙_{A[S]})` at a geometric base change, with
existence included and not assumed.** -/
theorem nonempty_corepresentableBy_and_flat_coneIdentity :
    Nonempty (((toposPushforward G ψ hψ) ⋙
        coyoneda.obj (Opposite.op (cone (𝟙 (freeDGModule S A))))).CorepresentableBy
      (cone (𝟙 (freeDGModule (SheafOfGradedSets.inverseImage f S) B)))) ∧
      ∀ {T : DifferentialGradedModule.{w, w, w} B},
        ((toposPushforward G ψ hψ) ⋙
          coyoneda.obj (Opposite.op (cone (𝟙 (freeDGModule S A))))).CorepresentableBy T →
        RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded T) ∧
          RelativeTensor.IsKFlat T :=
  ⟨⟨coneIdentityToposCorepresentableBy G f ν ψ hψ S⟩,
    fun e => isGradedFlat_isKFlat_of_coneIdentityToposCorepresentableBy G f ν ψ hψ S e⟩

end Flat

end ToposPullback

/-! ### Goodness of the cone on the identity of a free module -/

section Predicate

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **The cone on the identity of the free differential graded module `A[S]` on a sheaf of graded
sets is good**, at the source's own quantification. Conditions (1) and (2) are
`isGradedFlat_and_isKFlat_cone` at the identity of `A[S]`; condition (3) is the
corepresentability of `C(𝟙_{B[f⁻¹S]})` together with the flatness of every object corepresenting
the same functor. There is no hypothesis beyond those under which `A[S]` exists.

This is the base case of the tower of the first proof of Tag 0FSH which is not an instance of
Tag 0FSG: the tower's stages are cones of morphisms out of free modules, each a pushout of the
cone on an identity, and the cone on an identity is the one object in that span whose base change
neither Tag 0FSG nor closure under colimits supplies.

**It does not follow from the goodness of `A[S]`, and the reason is structural.** A morphism out
of `C(𝟙_{A[S]})` is a degree `-1` right `A`-linear family out of `A[S]`, which is a homomorphism
of *graded* modules into `SheafOfModules.DifferentialGradedModule.gradedShiftDown`; every clause
of `IsGoodToposBaseChange` is about homomorphisms of *differential* graded modules out of the
module in question, so no clause of it constrains such a datum. The same observation says that
condition (3) does **not** satisfy two-out-of-three along an admissible short exact sequence,
even though conditions (1) and (2) do: condition (3) carries an existential, a pullback of the
middle term has to be constructed, that construction is a cone, and its universal property needs
the base change of the cone on an identity rather than that of the sub-object. So this theorem is
an input to the closure lemma of
`ConeFreeDifferentialGradedModuleToposPullback.lean`, not a consequence of it. -/
theorem coneIdentityFreeDGModule_isGoodToposBaseChange [HasWeakSheafify Y.J (Type w)]
    (S : Stacks.SheafOfGradedSets.{w} Y.J) :
    IsGoodToposBaseChange.{w, v₁, u₁} (cone (𝟙 (freeDGModule S A))) := by
  have hcone := isGradedFlat_and_isKFlat_cone (𝟙 (freeDGModule S A))
    ⟨freeDGModule_isGradedFlat A S, freeDGModule_isKFlat S A⟩
    ⟨freeDGModule_isGradedFlat A S, freeDGModule_isKFlat S A⟩
  refine ⟨hcone.1, hcone.2, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  have hex := nonempty_corepresentableBy_and_flat_coneIdentity (toposDirectImageModules f)
    f.toToposHom (toposDirectImageModulesSetIso f) ψ hψ S
  exact ⟨⟨cone (𝟙 (freeDGModule
        (Stacks.SheafOfGradedSets.inverseImage f.toToposHom S) B)), hex.1⟩, fun _T e => hex.2 e⟩

end Predicate

end SheafOfModules

end
