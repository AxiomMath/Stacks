module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# `f^*f_! = id` for a morphism of ringed topoi with invertible structure map

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi whose pullback `f^*` of
sheaves of modules (**Stacks 03D6** part (2)) admits a left adjoint `f_!`, as
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackLowerShriek.lean` arranges. This
file proves that the unit `id ⟶ f^*f_!` of `f_! ⊣ f^*` is an isomorphism under two hypotheses:

* the inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map is invertible, and
* the counit `f⁻¹f_* ⟶ id` of the adjunction of the underlying morphism of topoi is an
  isomorphism, i.e. `f` presents `Sh(C)` as a subtopos of `Sh(D)`.

Both hold for the inclusion of a continuous, cocontinuous and fully faithful full subsite, which
is the situation of **Stacks 0788**; the conclusion is then the assertion `g^*g_! = id` of
**Stacks 0789**.

## The argument

The source derives `g^*g_! = id` from `g^* = g^{-1}` together with the corresponding equality for
abelian sheaves. Neither is used here. Instead the adjoint triple `f_! ⊣ f^* ⊣ f_*` is exploited:
the unit of the left-hand adjunction is an isomorphism exactly when the counit of the right-hand
one is (`CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit`), and the right-hand
adjunction is the Stacks 03D7 adjunction `f^* ⊣ f_*`, which does not mention `f_!` at all. So the
whole question becomes whether `f_*` is fully faithful on sheaves of modules.

It is, and for the two displayed reasons separately: the direct image of sheaves of modules is
restriction of scalars along the inverse-image structure map followed by the Stacks 03D3 direct
image, the first factor being an equivalence because that map is invertible, and the second being
fully faithful because the counit of the Stacks 03D3 adjunction `f⁻¹ ⊣ f_*` on modules is carried
by the counit of `f⁻¹ ⊣ f_*` on sheaves of sets, which is an isomorphism by hypothesis. That last
step is `moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app` below: the hom-set
bijection of Stacks 03D3 is the one of sheaves of sets on underlying sheaves, so its value at the
identity — the counit — is too.

## Main results

* `Stacks.Sheaves.RingedToposModules.isIso_inverseImageAdjDirectImageModules_counit`: the counit
  of the Stacks 03D3 adjunction on sheaves of modules is an isomorphism when the counit on
  sheaves of sets is.
* `Stacks.Sheaves.RingedToposModules.fullyFaithfulDirectImageModules`: hence the Stacks 03D3
  direct image of sheaves of modules is fully faithful.
* `AlgebraicGeometry.RingedToposHom.fullyFaithfulPushforwardModules`: the direct image of sheaves
  of modules along a morphism of ringed topoi with invertible inverse-image structure map is
  fully faithful.
* `AlgebraicGeometry.RingedToposHom.isIso_pullbackAdjPushforwardModules_counit`: hence the counit
  of `f^* ⊣ f_*` is an isomorphism.
* `AlgebraicGeometry.RingedToposHom.isIso_lowerShriekAdjPullbackModules_unit`: hence the unit of
  `f_! ⊣ f^*` is an isomorphism, which is `f^*f_! = id`.

## References

* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- **The counit of the Stacks 03D3 adjunction on sheaves of modules is the counit on sheaves of
sets**, on underlying sheaves. The hom-set bijection of Stacks 03D3 sends a morphism to the
transpose of its underlying morphism of sheaves of sets, so its value at the identity — which is
what the counit of an adjunction presented by a hom-set bijection is — is the transpose of the
identity, namely the counit of `f⁻¹ ⊣ f_*`. -/
theorem moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app
    (F : SheafOfModules.{w} (inverseImageRingSheaf f O)) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map
        ((inverseImageAdjDirectImageModules f O).counit.app F) =
      f.adj.counit.app (Sheaf.moduleSheaf (inverseImageRingSheaf f O) F) := by
  change (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map
      ((toposModulesHomEquiv f O ((directImageModules f O).obj F) F).symm (𝟙 _)) = _
  rw [moduleSheafFunctor_map_toposModulesHomEquiv_symm]
  change (f.adj.homEquiv (Sheaf.moduleSheaf O ((directImageModules f O).obj F))
    (Sheaf.moduleSheaf (inverseImageRingSheaf f O) F)).symm (𝟙 _) = _
  exact f.adj.homEquiv_symm_id _

/-- **The counit of the Stacks 03D3 adjunction on sheaves of modules is an isomorphism** as soon
as the counit `f⁻¹f_* ⟶ id` on sheaves of sets is. Its components are those of the latter on
underlying sheaves, and a morphism of sheaves of modules whose underlying morphism of sheaves is
invertible is invertible. -/
theorem isIso_inverseImageAdjDirectImageModules_counit [IsIso f.adj.counit] :
    IsIso (inverseImageAdjDirectImageModules f O).counit := by
  have : ∀ F, IsIso ((inverseImageAdjDirectImageModules f O).counit.app F) := fun F => by
    have : IsIso ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map
        ((inverseImageAdjDirectImageModules f O).counit.app F)) := by
      rw [moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app]
      exact NatIso.isIso_app_of_isIso _ _
    exact isIso_of_reflects_iso _ (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O))
  exact NatIso.isIso_of_isIso_app _

/-- **The Stacks 03D3 direct image of sheaves of modules is fully faithful** when the counit
`f⁻¹f_* ⟶ id` on sheaves of sets is an isomorphism: it is the right adjoint of an adjunction
whose counit is an isomorphism. -/
def fullyFaithfulDirectImageModules [IsIso f.adj.counit] :
    (directImageModules f O).FullyFaithful :=
  have := isIso_inverseImageAdjDirectImageModules_counit f O
  (inverseImageAdjDirectImageModules f O).fullyFaithfulROfIsIsoCounit

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y)

/-- **The direct image of sheaves of modules along a morphism of ringed topoi whose
inverse-image structure map is invertible and which presents a subtopos is fully faithful.** It
is restriction of scalars along the inverse-image structure map followed by the Stacks 03D3
direct image; the first is an equivalence because that map is invertible, the second is fully
faithful because the counit `f⁻¹f_* ⟶ id` on sheaves of sets is an isomorphism. -/
def fullyFaithfulPushforwardModules
    [IsIso f.fSharpInverseImage] [IsIso f.toToposHom.adj.counit] :
    f.pushforwardModules.FullyFaithful :=
  haveI := f.isIso_fSharpInverseImageRing
  Functor.FullyFaithful.ofIso
    (Functor.FullyFaithful.comp
      (Functor.FullyFaithful.ofFullyFaithful
        (SheafOfModules.restrictScalars f.fSharpInverseImageRing))
      (Stacks.Sheaves.RingedToposModules.fullyFaithfulDirectImageModules f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
    f.toModulesPushforwardIso

/-- **The counit `f^*f_* ⟶ id` of the Stacks 03D7 adjunction on sheaves of modules is an
isomorphism** when the inverse-image structure map is invertible and `f` presents a subtopos: the
right adjoint `f_*` is then fully faithful. -/
theorem isIso_pullbackAdjPushforwardModules_counit
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsIso f.fSharpInverseImage] [IsIso f.toToposHom.adj.counit] :
    IsIso f.pullbackAdjPushforwardModules.counit :=
  have := f.fullyFaithfulPushforwardModules.full
  have := f.fullyFaithfulPushforwardModules.faithful
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- **`f^*f_! = id` on sheaves of modules**: the unit `id ⟶ f^*f_!` of the adjunction defining the
lower shriek is an isomorphism, when the inverse-image structure map is invertible and `f`
presents a subtopos.

In the adjoint triple `f_! ⊣ f^* ⊣ f_*` the unit of the left-hand adjunction is an isomorphism
exactly when the counit of the right-hand one is, and the latter is
`AlgebraicGeometry.RingedToposHom.isIso_pullbackAdjPushforwardModules_counit`. No model of `f_!`
and no identification of `f^*` with `f⁻¹` enters. -/
theorem isIso_lowerShriekAdjPullbackModules_unit
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(f.toModulesHom.pullbackModules).IsRightAdjoint]
    [IsIso f.fSharpInverseImage] [IsIso f.toToposHom.adj.counit] :
    IsIso f.lowerShriekAdjPullbackModules.unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨f.lowerShriekAdjPullbackModules, f.pullbackAdjPushforwardModules⟩).2
      f.isIso_pullbackAdjPushforwardModules_counit

end AlgebraicGeometry.RingedToposHom

end
