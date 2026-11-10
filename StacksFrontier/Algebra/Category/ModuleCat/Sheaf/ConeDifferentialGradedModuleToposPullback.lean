module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeIdentityFreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodResolutionDataToposBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImageCofree

/-!
# The base change of a cone, and the goodness of a cone

Let `f : X ⟶ Y` be a morphism of ringed topoi, let `A` be a sheaf of differential graded
`O_Y`-algebras, let `B` be a sheaf of differential graded `O_X`-algebras and let `ψ : A ⟶ f_*B` be
a unital homomorphism. Let `φ : P ⟶ P'` be a homomorphism of right differential graded
`A`-modules whose two ends have base changes `T` and `T'` along `(f, B, ψ)` — that is, objects
corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)` and `Q ↦ Hom_A(P', f_{*,ψ}Q)`. Then **the cone of the base
change of `φ` is a base change of the cone of `φ`**, compatibly with the two cones' inclusions,
and consequently

`IsGoodToposBaseChange P → IsGoodToposBaseChange P' → IsGoodToposBaseChange (cone φ)`,

which is Tag 0FSC at the goodness of Tag 0FSA.

## The obstruction and how it is removed

A morphism out of `C(φ)` is a pair: a morphism `P' ⟶ N` together with a right `A`-linear family
of degree `-1` out of `P`, that is a homomorphism of **graded** modules `P ⟶ N[-1]`, whose
commutator with the differentials is `φ` followed by the first. Every clause of
`SheafOfModules.IsGoodToposBaseChange` is about homomorphisms of **differential** graded modules
out of the module in question, so no clause of it constrains the second datum; that is why
condition (3) does not satisfy two-out-of-three along the admissible short exact sequence of a
cone, and why the free case had to be done by hand.

What removes the obstruction is that the second datum is a morphism of differential graded
modules **into a cofree object**: a homomorphism of graded modules `P ⟶ N[-1]` is a morphism of
differential graded modules `P ⟶ Cofree(N[-1])`, so the degree-zero universal property of a base
change reaches it at that one test object. The transport is then
`SheafOfModules.DifferentialGradedModule.toposShiftDownEquiv`, built from

* the cofree adjunction `SheafOfModules.Cofree.homEquiv`,
* the corepresentability of the base change at `Cofree(Q[-1])`, and
* `SheafOfModules.DifferentialGradedModule.toposCofreeIso`, the identification
  `f_{*,ψ}(Cofree(Q[-1])) ≅ Cofree((f_{*,ψ}Q)[-1])`.

Bare corepresentability of the two cones would not identify the span. What identifies it is that
the transport carries the *commutator* across:
`SheafOfModules.DifferentialGradedModule.deltaHom_toposShiftDownEquiv`, which holds because the
commutator factors as the cofree lift followed by the counit
(`SheafOfModules.DifferentialGradedModule.deltaHom_eq`) and the comparison is compatible with the
two counits (`SheafOfModules.DifferentialGradedModule.toposCofreeDesc_comp_counit`). Both factors
are morphisms of differential graded modules, which is all a base change sees.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.toposShiftDownEquiv`: **the base change of a right
  `A`-linear family of degree `-1`** -- the graded transport the obstruction says the goodness
  predicate does not supply, obtained from the degree-zero universal property at one cofree test
  object.
* `SheafOfModules.DifferentialGradedModule.baseChangeHom` is the base change of a morphism, read
  off the two corepresentability data.
* `SheafOfModules.DifferentialGradedModule.coneToposHomEquiv` and
  `coneToposCorepresentableBy`: **the cone of the base change corepresents the base change of the
  cone.**

## Main results

* `SheafOfModules.DifferentialGradedModule.deltaHom_toposShiftDownEquiv`: **the base change of a
  degree `-1` family carries its commutator with the differentials across.**
* `SheafOfModules.DifferentialGradedModule.coneToposHomEquiv_inclusion`: **the bijection is
  compatible with the two cones' inclusions**, which is what identifies the base change of the
  cone *as a cone* and what the admissible short exact sequence of the cone consumes.
* `SheafOfModules.DifferentialGradedModule.cone_isGoodToposBaseChange`: **Tag 0FSC at the
  goodness of Tag 0FSA** -- the cone of a homomorphism of good right differential graded modules
  is good.

## Implementation notes

No `ν` and no sheaf of graded sets appear. The construction uses only the functor `G`, its
additivity and lax monoidal structure, and the unital `ψ`; in particular it is independent of the
comparison of underlying sheaves of sets which the free case needs, because nothing here is
computed through `Stacks.degreeFiberSheaf`.

Conditions (1) and (2) for a cone are Tag 0FSC at flatness,
`SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_cone`, applied twice: once to
`φ` over the target and once to its base change over the source. The second application is where
the inclusion compatibility is used in the form in which the admissible sequence needs it: the
object whose flatness is asserted is the *cone of the base change*, and every object
corepresenting the same functor is isomorphic to it by
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`.

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section ToposPullback

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)
  {P P' : DifferentialGradedModule.{w, w, w} A}
  {T T' : DifferentialGradedModule.{w, w, w} B}

/-- The transpose through a base change is natural: it commutes with postcomposition. -/
private theorem homEquiv_comp_map
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    {X X' : DifferentialGradedModule.{w, w, w} B} (a : T ⟶ X) (g : X ⟶ X') :
    e.homEquiv (a ≫ g) = e.homEquiv a ≫ (toposPushforward G ψ hψ).map g :=
  e.homEquiv_comp g a

/-! ### The base change of a degree `-1` family -/

/-- **The base change of a right `A`-linear family of degree `-1`.** A homomorphism of graded
modules `T ⟶ Q[-1]` is a morphism of differential graded modules `T ⟶ Cofree(Q[-1])`, so the
degree-zero universal property of the base change reaches it at that one test object; the
identification `f_{*,ψ}(Cofree(Q[-1])) ≅ Cofree((f_{*,ψ}Q)[-1])` then reads the result back as a
homomorphism of graded modules `P ⟶ (f_{*,ψ}Q)[-1]`. -/
noncomputable def toposShiftDownEquiv
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (Q : DifferentialGradedModule.{w, w, w} B) :
    GradedModule.Hom (GradedModule.ofDifferentialGraded T) (gradedShiftDown Q) ≃
      GradedModule.Hom (GradedModule.ofDifferentialGraded P)
        (gradedShiftDown ((toposPushforward G ψ hψ).obj Q)) where
  toFun Φ := Cofree.lowerHom _
    (e.homEquiv (Cofree.liftDgHom (gradedShiftDown Q) Φ) ≫ toposCofreeDesc G ψ hψ Q)
  invFun Ψ := Cofree.lowerHom _
    (e.homEquiv.symm (Cofree.liftDgHom _ Ψ ≫ (toposCofreeIso G ψ hψ Q).inv))
  left_inv Φ := by
    dsimp only
    rw [Cofree.liftDgHom_lowerHom, ← toposCofreeIso_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Equiv.symm_apply_apply]
    exact Cofree.lowerHom_liftDgHom _ Φ
  right_inv Ψ := by
    dsimp only
    rw [Cofree.liftDgHom_lowerHom, Equiv.apply_symm_apply, ← toposCofreeIso_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Cofree.lowerHom_liftDgHom _ Ψ

/-- **The cofree lift of the base change of a degree `-1` family** is the base change of its own
cofree lift, followed by the comparison. -/
theorem liftDgHom_toposShiftDownEquiv
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (Q : DifferentialGradedModule.{w, w, w} B)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded T) (gradedShiftDown Q)) :
    Cofree.liftDgHom _ (toposShiftDownEquiv G ψ hψ e Q Φ) =
      e.homEquiv (Cofree.liftDgHom (gradedShiftDown Q) Φ) ≫ toposCofreeDesc G ψ hψ Q :=
  Cofree.liftDgHom_lowerHom _ _

/-- **The base change of a degree `-1` family carries its commutator with the differentials
across.** This is what identifies the base change of a cone *as a cone*: the commutator factors
as the cofree lift followed by the counit, and both factors are morphisms of differential graded
modules, which is all the universal property of a base change sees. -/
theorem deltaHom_toposShiftDownEquiv
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (Q : DifferentialGradedModule.{w, w, w} B)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded T) (gradedShiftDown Q)) :
    deltaHom (toposShiftDownEquiv G ψ hψ e Q Φ) = e.homEquiv (deltaHom Φ) := by
  rw [deltaHom_eq, liftDgHom_toposShiftDownEquiv, Category.assoc,
    toposCofreeDesc_comp_counit, ← homEquiv_comp_map, deltaHom_eq]

/-- **The base change of a degree `-1` family is natural in the target.** -/
theorem toposShiftDownEquiv_comp
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q')
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded T) (gradedShiftDown Q)) :
    toposShiftDownEquiv G ψ hψ e Q' (Φ.comp (gradedShiftDownMap g)) =
      (toposShiftDownEquiv G ψ hψ e Q Φ).comp
        (gradedShiftDownMap ((toposPushforward G ψ hψ).map g)) := by
  refine liftDgHom_injective _ ?_
  rw [liftDgHom_toposShiftDownEquiv, liftDgHom_comp, liftDgHom_comp,
    liftDgHom_toposShiftDownEquiv, homEquiv_comp_map, Category.assoc, toposCofreeDesc_naturality,
    Category.assoc]

/-! ### The base change of a homomorphism of underlying graded modules -/

/-- **The base change of a homomorphism of the underlying graded modules.** The topos-level
counterpart of `SheafOfModules.DifferentialGradedModule.PullbackData.gradedMap`: a homomorphism
of graded modules `T ⟶ Q` is a morphism of differential graded modules `T ⟶ Cofree(gr Q)`, which
the degree-zero universal property of the base change reaches, and
`SheafOfModules.DifferentialGradedModule.toposCofreeIsoGraded` reads the result back as a
homomorphism of graded modules out of `P`.

This is the transport whose absence
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedAdmissible.lean` records as
the reason two out of three for goodness is not stated at `SheafOfModules.IsGoodToposBaseChange`:
the retraction and the section of a `GradedSplitting` are homomorphisms of the underlying graded
modules, not morphisms of differential graded modules. -/
noncomputable def toposGradedEquiv
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (Q : DifferentialGradedModule.{w, w, w} B) :
    GradedModule.Hom (GradedModule.ofDifferentialGraded T)
        (GradedModule.ofDifferentialGraded Q) ≃
      GradedModule.Hom (GradedModule.ofDifferentialGraded P)
        (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj Q)) where
  toFun Φ := Cofree.lowerHom _
    (e.homEquiv (Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ) ≫
      toposCofreeDescGraded G ψ hψ Q)
  invFun Ψ := Cofree.lowerHom _
    (e.homEquiv.symm (Cofree.liftDgHom _ Ψ ≫ (toposCofreeIsoGraded G ψ hψ Q).inv))
  left_inv Φ := by
    dsimp only
    rw [Cofree.liftDgHom_lowerHom, ← toposCofreeIsoGraded_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Equiv.symm_apply_apply]
    exact Cofree.lowerHom_liftDgHom _ Φ
  right_inv Ψ := by
    dsimp only
    rw [Cofree.liftDgHom_lowerHom, Equiv.apply_symm_apply, ← toposCofreeIsoGraded_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Cofree.lowerHom_liftDgHom _ Ψ

/-- **The cofree lift of the base change of a graded homomorphism.** -/
theorem liftDgHom_toposGradedEquiv
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (Q : DifferentialGradedModule.{w, w, w} B)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded T)
      (GradedModule.ofDifferentialGraded Q)) :
    Cofree.liftDgHom _ (toposGradedEquiv G ψ hψ e Q Φ) =
      e.homEquiv (Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ) ≫
        toposCofreeDescGraded G ψ hψ Q :=
  Cofree.liftDgHom_lowerHom _ _

/-- **The unit formula**: the base change of a homomorphism of graded modules is the unit of the
base change followed by the *direct image* of that homomorphism. This is the topos-level form of
`SheafOfModules.DifferentialGradedModule.PullbackData.gradedShiftMap_unit`, and it is what makes
the transport determined: the other side of the bijection is the only thing the unit can be
composed with. -/
theorem toposGradedEquiv_eq
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (Q : DifferentialGradedModule.{w, w, w} B)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded T)
      (GradedModule.ofDifferentialGraded Q)) :
    toposGradedEquiv G ψ hψ e Q Φ =
      (GradedModule.ofDifferentialGradedMap (e.homEquiv (𝟙 T))).comp
        (toposGradedPushMap G ψ hψ Φ) := by
  have h1 : e.homEquiv (Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ) =
      e.homEquiv (𝟙 T) ≫ (toposPushforward G ψ hψ).map
        (Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ) :=
    e.homEquiv_eq _
  change Cofree.lowerHom _
      (e.homEquiv (Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ) ≫
        toposCofreeDescGraded G ψ hψ Q) = _
  rw [h1, Category.assoc]
  refine GradedModule.Hom.ext fun n => ?_
  rw [lowerHom_comp_left]
  change (e.homEquiv (𝟙 T)).toHomologicalComplex.f n ≫
      (Cofree.lowerHom _ ((toposPushforward G ψ hψ).map
        (Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ) ≫
          toposCofreeDescGraded G ψ hψ Q)).app n = _
  rw [lowerHom_map_liftDgHom]
  rfl

/-- **The base change of a homomorphism of graded modules is natural in the target.** -/
theorem toposGradedEquiv_comp
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q')
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded T)
      (GradedModule.ofDifferentialGraded Q)) :
    toposGradedEquiv G ψ hψ e Q' (Φ.comp (GradedModule.ofDifferentialGradedMap g)) =
      (toposGradedEquiv G ψ hψ e Q Φ).comp
        (GradedModule.ofDifferentialGradedMap ((toposPushforward G ψ hψ).map g)) := by
  refine liftDgHom_injective _ ?_
  rw [liftDgHom_toposGradedEquiv, liftDgHom_comp, liftDgHom_comp,
    liftDgHom_toposGradedEquiv, homEquiv_comp_map, Category.assoc, toposCofreeDescGraded_naturality,
    Category.assoc]

/-! ### The base change of a morphism -/

/-- **The base change of a morphism of right differential graded modules**, read off the two
corepresentability data: the unique morphism of the two base changes whose transpose is
precomposition with the given one. -/
noncomputable def baseChangeHom
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (φ : P ⟶ P') : T ⟶ T' :=
  e.homEquiv.symm (φ ≫ e'.homEquiv (𝟙 T'))

/-- **The transpose of a morphism through the base change of a morphism is precomposition with
that morphism.** -/
theorem homEquiv_baseChangeHom_comp
    (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
    (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
    (φ : P ⟶ P') {X : DifferentialGradedModule.{w, w, w} B} (k : T' ⟶ X) :
    e.homEquiv (baseChangeHom G ψ hψ e e' φ ≫ k) = φ ≫ e'.homEquiv k := by
  rw [homEquiv_comp_map, baseChangeHom, Equiv.apply_symm_apply, Category.assoc,
    ← homEquiv_comp_map, Category.id_comp]

/-! ### The base change of a cone -/

section Cone

variable
  (e : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy T)
  (e' : (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op P')).CorepresentableBy T')
  (φ : P ⟶ P')

/-- **The commutator condition for the forward transport.** -/
theorem deltaHom_coneFam_toposShiftDown (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) :
    deltaHom (toposShiftDownEquiv G ψ hψ e Q (coneFam h)) =
      φ ≫ e'.homEquiv
        ((conePackage (baseChangeHom G ψ hψ e e' φ)).inclusion ≫ h) := by
  rw [deltaHom_toposShiftDownEquiv, deltaHom_coneFam, homEquiv_baseChangeHom_comp]

/-- **The commutator condition for the backward transport.** -/
theorem deltaHom_coneFam_toposShiftDown_symm (Q : DifferentialGradedModule.{w, w, w} B)
    (H : cone φ ⟶ (toposPushforward G ψ hψ).obj Q) :
    deltaHom ((toposShiftDownEquiv G ψ hψ e Q).symm (coneFam H)) =
      baseChangeHom G ψ hψ e e' φ ≫
        e'.homEquiv.symm ((conePackage φ).inclusion ≫ H) := by
  refine e.homEquiv.injective ?_
  rw [← deltaHom_toposShiftDownEquiv G ψ hψ e Q, Equiv.apply_symm_apply,
    deltaHom_coneFam, homEquiv_baseChangeHom_comp, Equiv.apply_symm_apply]

/-- **The transport of a morphism out of the cone of the base change of `φ`.** -/
noncomputable def coneToposDesc (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) :
    cone φ ⟶ (toposPushforward G ψ hψ).obj Q :=
  coneDescOf (e'.homEquiv ((conePackage (baseChangeHom G ψ hψ e e' φ)).inclusion ≫ h))
    (toposShiftDownEquiv G ψ hψ e Q (coneFam h))
    (deltaHom_coneFam_toposShiftDown G ψ hψ e e' φ Q h)

/-- **The transport of a morphism out of the cone of `φ` into the direct image.** -/
noncomputable def coneToposLift (Q : DifferentialGradedModule.{w, w, w} B)
    (H : cone φ ⟶ (toposPushforward G ψ hψ).obj Q) :
    cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q :=
  coneDescOf (e'.homEquiv.symm ((conePackage φ).inclusion ≫ H))
    ((toposShiftDownEquiv G ψ hψ e Q).symm (coneFam H))
    (deltaHom_coneFam_toposShiftDown_symm G ψ hψ e e' φ Q H)

/-- The restriction of `coneToposDesc` along the inclusion `P' ⟶ C(φ)` is the transport, by the
universal property of the base change of `P'`, of the restriction of `h` along `T' ⟶ C(φ_T)`. -/
theorem inclusion_coneToposDesc (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) :
    (conePackage φ).inclusion ≫ coneToposDesc G ψ hψ e e' φ Q h =
      e'.homEquiv ((conePackage (baseChangeHom G ψ hψ e e' φ)).inclusion ≫ h) :=
  inclusion_coneDescOf _ _ (deltaHom_coneFam_toposShiftDown G ψ hψ e e' φ Q h)

/-- The degree `-1` family of `coneToposDesc` is the transport of the degree `-1` family of `h` by
`SheafOfModules.DifferentialGradedModule.toposShiftDownEquiv`. -/
theorem coneFam_coneToposDesc (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) :
    coneFam (coneToposDesc G ψ hψ e e' φ Q h) =
      toposShiftDownEquiv G ψ hψ e Q (coneFam h) :=
  coneFam_coneDescOf _ _ (deltaHom_coneFam_toposShiftDown G ψ hψ e e' φ Q h)

/-- The restriction of `coneToposLift` along the inclusion `T' ⟶ C(φ_T)` is the inverse transport
of the restriction of `H` along the inclusion `P' ⟶ C(φ)`. -/
theorem inclusion_coneToposLift (Q : DifferentialGradedModule.{w, w, w} B)
    (H : cone φ ⟶ (toposPushforward G ψ hψ).obj Q) :
    (conePackage (baseChangeHom G ψ hψ e e' φ)).inclusion ≫
        coneToposLift G ψ hψ e e' φ Q H =
      e'.homEquiv.symm ((conePackage φ).inclusion ≫ H) :=
  inclusion_coneDescOf _ _ (deltaHom_coneFam_toposShiftDown_symm G ψ hψ e e' φ Q H)

/-- The degree `-1` family of `coneToposLift` is the inverse transport of the degree `-1` family of
`H` by `SheafOfModules.DifferentialGradedModule.toposShiftDownEquiv`. -/
theorem coneFam_coneToposLift (Q : DifferentialGradedModule.{w, w, w} B)
    (H : cone φ ⟶ (toposPushforward G ψ hψ).obj Q) :
    coneFam (coneToposLift G ψ hψ e e' φ Q H) =
      (toposShiftDownEquiv G ψ hψ e Q).symm (coneFam H) :=
  coneFam_coneDescOf _ _ (deltaHom_coneFam_toposShiftDown_symm G ψ hψ e e' φ Q H)

/-- **The cone of the base change of `φ` represents the base change of the cone of `φ`**, as a
bijection of hom-sets: a morphism out of `C(φ_T)` is a morphism out of `C(φ)` into the direct
image. A morphism out of a cone is a morphism out of its target together with a right-linear
degree `-1` family out of its source whose commutator with the differentials is the first; the
first is transported by the universal property of the base change of `P'`, the second by
`SheafOfModules.DifferentialGradedModule.toposShiftDownEquiv`, and the commutator condition is
preserved because that transport carries commutators across. -/
noncomputable def coneToposHomEquiv (Q : DifferentialGradedModule.{w, w, w} B) :
    (cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) ≃
      (cone φ ⟶ (toposPushforward G ψ hψ).obj Q) where
  toFun h := coneToposDesc G ψ hψ e e' φ Q h
  invFun H := coneToposLift G ψ hψ e e' φ Q H
  left_inv h := by
    refine cone_hom_ext ?_ ?_
    · rw [inclusion_coneToposLift, inclusion_coneToposDesc, Equiv.symm_apply_apply]
    · rw [coneFam_coneToposLift, coneFam_coneToposDesc, Equiv.symm_apply_apply]
  right_inv H := by
    refine cone_hom_ext ?_ ?_
    · rw [inclusion_coneToposDesc, inclusion_coneToposLift, Equiv.apply_symm_apply]
    · rw [coneFam_coneToposDesc, coneFam_coneToposLift, Equiv.apply_symm_apply]

/-- The bijection `coneToposHomEquiv` sends `h` to `coneToposDesc h`. -/
@[simp] theorem coneToposHomEquiv_apply (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) :
    coneToposHomEquiv G ψ hψ e e' φ Q h = coneToposDesc G ψ hψ e e' φ Q h := rfl

/-- **The bijection is compatible with the two cones' inclusions**: the base change of the
inclusion `P' ⟶ C(φ)` is the inclusion `T' ⟶ C(φ_T)`. This is what identifies the base change of
the cone *as a cone*, which corepresentability alone does not: the flatness of the base change
comes from the admissible short exact sequence of the cone, and that sequence is only available
once the inclusion is identified. -/
theorem coneToposHomEquiv_inclusion (Q : DifferentialGradedModule.{w, w, w} B)
    (h : cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) :
    e'.homEquiv ((conePackage (baseChangeHom G ψ hψ e e' φ)).inclusion ≫ h) =
      (conePackage φ).inclusion ≫ coneToposHomEquiv G ψ hψ e e' φ Q h :=
  (inclusion_coneToposDesc G ψ hψ e e' φ Q h).symm

/-- **The bijection is natural in `Q`.** Both sides are morphisms out of a cone, so they are
compared on the two coordinates a morphism out of a cone has. -/
theorem coneToposHomEquiv_comp {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q')
    (h : cone (baseChangeHom G ψ hψ e e' φ) ⟶ Q) :
    coneToposHomEquiv G ψ hψ e e' φ Q' (h ≫ g) =
      coneToposHomEquiv G ψ hψ e e' φ Q h ≫ (toposPushforward G ψ hψ).map g := by
  simp only [coneToposHomEquiv_apply]
  refine cone_hom_ext ?_ ?_
  · rw [inclusion_coneToposDesc, ← Category.assoc _ h g, homEquiv_comp_map, ← Category.assoc,
      inclusion_coneToposDesc]
  · rw [coneFam_coneToposDesc, coneFam_comp, coneFam_comp, coneFam_coneToposDesc,
      toposShiftDownEquiv_comp]

/-- **The cone of the base change of `φ` corepresents the base change of the cone of `φ`.** -/
noncomputable def coneToposCorepresentableBy :
    (toposPushforward G ψ hψ ⋙ coyoneda.obj (Opposite.op (cone φ))).CorepresentableBy
      (cone (baseChangeHom G ψ hψ e e' φ)) where
  homEquiv {Q} := coneToposHomEquiv G ψ hψ e e' φ Q
  homEquiv_comp g h := coneToposHomEquiv_comp G ψ hψ e e' φ g h

end Cone

end ToposPullback

/-! ### Tag 0FSC at the goodness of Tag 0FSA -/

section Predicate

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

omit [HasSheafify Y.J (Type w)] in
/-- **Tag 0FSC at the goodness of Tag 0FSA: the cone of a homomorphism of good right differential
graded modules is good.** Conditions (1) and (2) are Tag 0FSC at flatness, applied to `φ` over
the target. Condition (3) is the content: at a base change `(f, B, ψ)` the two ends of `φ` have
base changes `T` and `T'` by their goodness, the cone of the base change of `φ` corepresents the
base change of `C(φ)` by
`SheafOfModules.DifferentialGradedModule.coneToposCorepresentableBy`, and it is flat as a graded
module and K-flat by Tag 0FSC at flatness applied over the source -- the two ends of the base
changed morphism being flat and K-flat, again by the goodness of `P` and `P'`. Every other object
corepresenting the same functor is isomorphic to it, so the clause holds for all of them.

The identification of the base change of the cone is **as a cone**, not merely up to
corepresentability: `coneToposHomEquiv_inclusion` says the base change of the inclusion is the
inclusion, which is what the admissible short exact sequence of the cone consumes. -/
theorem cone_isGoodToposBaseChange [HasWeakSheafify Y.J (Type w)]
    {P P' : DifferentialGradedModule.{w, w, w} A} (φ : P ⟶ P')
    (hP : IsGoodToposBaseChange.{w, v₁, u₁} P)
    (hP' : IsGoodToposBaseChange.{w, v₁, u₁} P') :
    IsGoodToposBaseChange.{w, v₁, u₁} (cone φ) := by
  have h := isGradedFlat_and_isKFlat_cone φ ⟨hP.isGradedFlat, hP.isKFlat⟩
    ⟨hP'.isGradedFlat, hP'.isKFlat⟩
  refine ⟨h.1, h.2, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  obtain ⟨T, ⟨e⟩⟩ := (hP.baseChange f B ψ hψ).1
  obtain ⟨T', ⟨e'⟩⟩ := (hP'.baseChange f B ψ hψ).1
  have hT := (hP.baseChange f B ψ hψ).2 T e
  have hT' := (hP'.baseChange f B ψ hψ).2 T' e'
  have hcone := isGradedFlat_and_isKFlat_cone
    (baseChangeHom (toposDirectImageModules f) ψ hψ e e' φ) hT hT'
  refine ⟨⟨cone (baseChangeHom (toposDirectImageModules f) ψ hψ e e' φ),
    ⟨coneToposCorepresentableBy (toposDirectImageModules f) ψ hψ e e' φ⟩⟩, ?_⟩
  intro Tc ec
  have hiso := ec.uniqueUpToIso
    (coneToposCorepresentableBy (toposDirectImageModules f) ψ hψ e e' φ)
  exact ⟨RelativeTensor.IsGradedFlat.of_iso
      (GradedModule.ofDifferentialGradedIso hiso).symm hcone.1,
    RelativeTensor.IsKFlat.of_iso hiso.symm hcone.2⟩

/-- **The flat-resolution theory of `(𝒜, d)` at the goodness of Tag 0FSA, with no hypothesis.**
`SheafOfModules.DifferentialGradedModule.GoodResolutionData.ofIsGoodToposBaseChange` takes Tag
0FSC at that goodness as its one argument, and `cone_isGoodToposBaseChange` is it. So the
`GoodResolutionData` whose good modules are the good right differential graded modules of
Tag 0FSA exists unconditionally. -/
noncomputable def goodResolutionDataOfIsGoodToposBaseChange [HasWeakSheafify Y.J (Type w)] :
    GoodResolutionData.{w, w, w, v₂, u₂} A :=
  GoodResolutionData.ofIsGoodToposBaseChange.{w, v₁, u₁, v₂, u₂}
    fun φ hP hP' => cone_isGoodToposBaseChange.{w, v₁, u₁, v₂, u₂} φ hP hP'

/-- The good modules of that resolution theory are the good ones of Tag 0FSA. -/
@[simp]
theorem goodResolutionDataOfIsGoodToposBaseChange_isGood [HasWeakSheafify Y.J (Type w)] :
    (goodResolutionDataOfIsGoodToposBaseChange.{w, v₁, u₁, v₂, u₂} (A := A)).IsGood =
      fun P => IsGoodToposBaseChange.{w, v₁, u₁} P :=
  rfl

end Predicate

end SheafOfModules.DifferentialGradedModule

end
