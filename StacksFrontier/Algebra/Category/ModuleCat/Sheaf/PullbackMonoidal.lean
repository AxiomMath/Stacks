module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso

/-!
# The pullback of presheaves of modules is a monoidal functor

Let `F : C ⥤ D` be a functor, let `S : Cᵒᵖ ⥤ CommRingCat` and `R : Dᵒᵖ ⥤ CommRingCat` be
presheaves of commutative rings and let `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings
(read through `forget₂ CommRingCat RingCat`, which is the shape `PresheafOfModules.pushforward`
and `PresheafOfModules.pullback` consume). The categories of presheaves of modules over `S` and
over `R` are monoidal, by the objectwise tensor product (Mathlib's
`PresheafOfModules.monoidalCategory`), and this file shows:

* the pushforward `f_* : PresheafOfModules R ⥤ PresheafOfModules S` is **lax monoidal**, and
* the pullback `f^* : PresheafOfModules S ⥤ PresheafOfModules R` is **oplax monoidal**, with
  oplax tensorator the canonical comparison `f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N`, and
* for a morphism of ringed spaces that oplax structure is **strong**: both structure maps are
  isomorphisms, so `f^*` is a monoidal functor.

This is the coherence that Stacks Tag 01CD by itself does not supply.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison` and
`...PullbackTensorCanonical` prove that the canonical comparison
`Stacks.RingedSpace.comparison` is an isomorphism and that it is the only candidate, which is
01CD; but an isomorphism of bifunctors says nothing about its compatibility with the associator
and the unitors, and that compatibility is exactly what a `SheafOfModules.GradedAlgebra`
structure on `f^*A` needs in order to have an *associative* multiplication conjugated from
`A.mul`. Here that compatibility is proved — at the level of presheaves of modules.

## Main definitions

* `PresheafOfModules.pushforwardEpsilon` and `PresheafOfModules.pushforwardMu`: the unit and the
  tensorator of the pushforward, given objectwise by the lax monoidal structure of
  `ModuleCat.restrictScalars`.
* `PresheafOfModules.pushforwardLaxMonoidal`: the lax monoidal structure on
  `PresheafOfModules.pushforward φ`.
* `PresheafOfModules.pullbackOplaxMonoidal`: the oplax monoidal structure on
  `PresheafOfModules.pullback φ`, obtained from the previous one by
  `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`.
* `PresheafOfModules.pullbackAdjUnit`: a local section of a presheaf of modules, carried into
  the pullback by the unit of the adjunction `f^* ⊣ f_*`.
* `PresheafOfModules.pushforwardSections`: the map from the sections of a presheaf of modules to
  the sections of its pushforward.
* `Stacks.PullbackMonoidal.structurePresheafHom`: the structure morphism of a morphism of ringed
  spaces, at the type the presheaf-level pullback expects.
* `Stacks.PullbackMonoidal.presheafPullbackMonoidal`: **the presheaf-level pullback along a
  morphism of ringed spaces is a monoidal functor.**

## Main results

* `PresheafOfModules.pushforwardLaxMonoidal` proves all five lax monoidal laws for the
  pushforward: naturality of the tensorator in each variable, **associativity**, and left and
  right **unitality**. Each one reduces objectwise to the corresponding law for
  `ModuleCat.restrictScalars`, because the monoidal structure on presheaves of modules is
  objectwise and the pushforward is objectwise restriction of scalars along `φ` composed with
  evaluation at `F.op.obj X`.
* `PresheafOfModules.pullbackOplaxMonoidal` therefore proves all five *oplax* laws for the
  pullback: naturality of `δ` in each variable, **oplax associativity** — the compatibility of
  the comparison with the associator — and oplax left and right unitality.
* `PresheafOfModules.delta_pullbackAdjUnit_tmul`: **the oplax tensorator is the canonical
  comparison**, read on sections: it carries the unit image of a pure tensor to the pure tensor
  of the two unit images. This is the clause that makes the structure canonical rather than
  merely existent.
* `PresheafOfModules.pullback_tensor_hom_ext`: two morphisms out of the pullback of an
  objectwise tensor product which agree on the unit images of pure tensors are equal.
* `PresheafOfModules.bijective_pushforwardSections`: the sections of a pushforward are the
  sections, when `F` is final. This is the presheaf-level counterpart of Mathlib's
  `SheafOfModules.bijective_pushforwardSections`, and it is what makes the oplax unit
  invertible.
* `PresheafOfModules.isIso_eta`: **the oplax unit `f^*𝒪 ⟶ 𝒪` is an isomorphism** when `F` is
  final. The proof is Mathlib's proof of `SheafOfModules.instIsIsoPullbackObjUnitToUnit`,
  transposed to presheaves: both objects corepresent the sections functor.
* `Stacks.PullbackMonoidal.delta_eq_pullbackTensorIso`: for a morphism of ringed spaces the
  oplax tensorator **is** `Stacks.PullbackTensor.pullbackTensorIso`, the presheaf-level
  comparison of Tag 01CD, and `Stacks.PullbackMonoidal.isIso_delta` concludes that it is an
  isomorphism.
* `Stacks.PullbackMonoidal.presheafPullbackMonoidal_delta` and
  `..._eta` record that the structure maps of the monoidal structure are the oplax ones, i.e.
  that the monoidal functor produced here is the one whose tensorator is the canonical
  comparison, not some other one.

## Implementation notes

**The sheaf-level statement.** The monoidal functor produced here is the **presheaf-level**
pullback. The sheaf-level statement — that `RingedSpaceModuleAdjunction.modulePullback f` is
monoidal for the monoidal structure of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` —
does **not** follow by restriction, because the tensor product of sheaves of modules is the
*sheafification* of the objectwise one. It follows from what is proved here by exactly one
application of Mathlib's `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`, whose three
inputs are:

* `L := Stacks.SheafOfModules.sheafifyFunctor`, a monoidal localization functor at
  `Stacks.SheafOfModules.localIso` (the monoidal structure on sheaves of modules *is* the
  localized one, so `L.Monoidal` is Mathlib's instance on
  `CategoryTheory.Localization.Monoidal.toMonoidalCategory`);
* `G :=` the presheaf-level pullback followed by sheafification, monoidal as a composite of the
  monoidal functor built here with the monoidal localization functor on the target site;
* `Lifting L W G F` for `F :=` the sheaf-level pullback, supplied by Mathlib's
  `SheafOfModules.sheafificationCompPullback`, whose type is literally `L ⋙ F ≅ G`.

Transporting the result from `Stacks.SheafOfModules.monoidalCategory` (whose tensor product is
the sheafified objectwise one) to `Stacks.SheafOfModules.Strict.monoidalCategory` (whose tensor
product is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` on the nose) is a further step,
through `CategoryTheory.Monoidal.induced`.

**No new tensor product and no new monoidal structure are introduced.** The monoidal structures
used are Mathlib's `PresheafOfModules.monoidalCategory` on both sides; the only new data are the
(op)lax structure maps of the two functors, and those are pinned to the canonical comparison.

**Why the structure maps are given objectwise rather than by an adjunction.** The lax structure
on the pushforward could be assembled as `pushforward₀OfCommRingCat` (monoidal, in Mathlib)
followed by restriction of scalars; but `PresheafOfModules.pushforward φ` is
`pushforward₀ F R ⋙ restrictScalars φ` with the intermediate category spelled
`PresheafOfModules (F.op ⋙ R ⋙ forget₂ _ _)`, whose monoidal structure instance search does not
find — the instance is declared for `PresheafOfModules (? ⋙ forget₂ _ _)` and the unifier will
not reassociate the composite. Giving the structure maps objectwise avoids the intermediate
category entirely, and each law is then one `ext1` away from the `ModuleCat` law.

**`pushforwardRingHom` and `structurePresheafHom` are retypings, not new content.** The first
spells the target ring of `φ.app X` as `(R ⋙ forget₂ _ _).obj (F.op.obj X)` so that the
`CommRing` instance of a presheaf of commutative rings is found; the second spells the target of
the structure morphism of a morphism of ringed spaces as `(f⁻¹).op ⋙ 𝒪_X ⋙ forget₂ _ _` rather
than through `Functor.sheafPushforwardContinuous`, so that `F` and `R` are determined before
instance search runs.

**`rw` is unusable across the `tensorObj`/`⊗` boundary.** The two spellings of the objectwise
tensor product of presheaves of modules are definitionally equal but not syntactically so, and a
`rw` in a goal mixing them fails with the target reported as not type-correct at `implicit`
transparency. Every step across that boundary here is an `exact`, an `Eq.trans` or a `congrArg`.

**Universes.** The single module universe `u`, equal to the universe of the two presheaves of
commutative rings, is forced: Mathlib's monoidal structure on presheaves of modules is declared
only for `PresheafOfModules.{u}` over a ring presheaf of the shape
`R ⋙ forget₂ CommRingCat RingCat` with `R : Cᵒᵖ ⥤ CommRingCat.{u}`. The site universes are
independent of `u` and of each other in the general section; the ringed-space section collapses
them to `u`, which is forced by `RingedSpaceModuleAdjunction.modulePullback`.

**No `@[stacks]` attribute.** Tag 01CD is closed and sits on
`Stacks.RingedSpace.comparisonIso`; nothing here restates it. What is here is the coherence of
that comparison, which Stacks does not state as a numbered result.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
    F.op ⋙ R ⋙ forget₂ CommRingCat.{u} RingCat.{u})

/-- The component of `φ` at `X`, retyped so that its target ring is spelled
`(R ⋙ forget₂ _ _).obj (F.op.obj X)`, which is the spelling at which the `CommRing`
instance of a presheaf of commutative rings is found. -/
noncomputable abbrev pushforwardRingHom (X : Cᵒᵖ) :
    (S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj X ⟶
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (F.op.obj X) :=
  φ.app X

/-- The unit map of the pushforward. -/
noncomputable def pushforwardEpsilon :
    𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) ⟶
      (pushforward φ).obj (𝟙_ (PresheafOfModules.{u}
        (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))) where
  app X := ε (ModuleCat.restrictScalars (pushforwardRingHom φ X).hom)
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
    refine Eq.trans (ModuleCat.restrictScalars_η (pushforwardRingHom φ Y).hom ((S.map f) r)) ?_
    refine Eq.trans (RingHom.congr_fun (congrArg RingCat.Hom.hom (φ.naturality f)) r) ?_
    exact congrArg (fun z ↦ ((pushforward φ).obj
        (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})))).map f z)
      (ModuleCat.restrictScalars_η (pushforwardRingHom φ X).hom r).symm

/-- The tensorator of the pushforward. -/
noncomputable def pushforwardMu
    (M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    (pushforward φ).obj M₁ ⊗ (pushforward φ).obj M₂ ⟶ (pushforward φ).obj (M₁ ⊗ M₂) where
  app X := μ (ModuleCat.restrictScalars (pushforwardRingHom φ X).hom)
    (M₁.obj (F.op.obj X)) (M₂.obj (F.op.obj X))
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m₁ m₂ ↦ ?_
    refine Eq.trans (ModuleCat.restrictScalars_μ_tmul (pushforwardRingHom φ Y).hom
      (M₁.obj (F.op.obj Y)) (M₂.obj (F.op.obj Y))
      (M₁.map (F.op.map f) m₁) (M₂.map (F.op.map f) m₂)) ?_
    exact (congrArg (fun z ↦ ((pushforward φ).obj (M₁ ⊗ M₂)).map f z)
      (ModuleCat.restrictScalars_μ_tmul (pushforwardRingHom φ X).hom
        (M₁.obj (F.op.obj X)) (M₂.obj (F.op.obj X)) m₁ m₂)).symm

/-- The pushforward of presheaves of modules is lax monoidal. -/
@[instance_reducible]
noncomputable def pushforwardLaxMonoidal : (pushforward.{u} φ).LaxMonoidal where
  ε := pushforwardEpsilon φ
  μ := pushforwardMu φ
  μ_natural_left {M₁ M₂} ψ M₃ := by
    ext1 X
    exact Functor.LaxMonoidal.μ_natural_left
      (ModuleCat.restrictScalars (pushforwardRingHom φ X).hom)
      (Hom.app ψ (F.op.obj X)) (M₃.obj (F.op.obj X))
  μ_natural_right {M₁ M₂} M₃ ψ := by
    ext1 X
    exact Functor.LaxMonoidal.μ_natural_right
      (ModuleCat.restrictScalars (pushforwardRingHom φ X).hom)
      (M₃.obj (F.op.obj X)) (Hom.app ψ (F.op.obj X))
  associativity M₁ M₂ M₃ := by
    ext1 X
    exact Functor.LaxMonoidal.associativity
      (ModuleCat.restrictScalars (pushforwardRingHom φ X).hom)
      (M₁.obj (F.op.obj X)) (M₂.obj (F.op.obj X)) (M₃.obj (F.op.obj X))
  left_unitality M := by
    ext1 X
    exact (PresheafOfModulesOfCommRing.leftUnitor_hom_app ((pushforward φ).obj M) X).trans
      (Functor.LaxMonoidal.left_unitality
        (ModuleCat.restrictScalars (pushforwardRingHom φ X).hom) (M.obj (F.op.obj X)))
  right_unitality M := by
    ext1 X
    exact (PresheafOfModulesOfCommRing.rightUnitor_hom_app ((pushforward φ).obj M) X).trans
      (Functor.LaxMonoidal.right_unitality
        (ModuleCat.restrictScalars (pushforwardRingHom φ X).hom) (M.obj (F.op.obj X)))

/-- The tensorator of the pushforward sends, at an object `W`, the pure tensor `m₁ ⊗ₜ m₂` over
the ring `S(W)` to the pure tensor `m₁ ⊗ₜ m₂` over the ring `R(F(W))`. -/
lemma pushforwardMu_app_tmul
    (M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (W : Cᵒᵖ)
    (m₁ : M₁.obj (F.op.obj W)) (m₂ : M₂.obj (F.op.obj W)) :
    Hom.app (pushforwardMu φ M₁ M₂) W
        (m₁ ⊗ₜ[(S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W] m₂) =
      (m₁ ⊗ₜ[(R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (F.op.obj W)] m₂) :=
  ModuleCat.restrictScalars_μ_tmul (pushforwardRingHom φ W).hom
    (M₁.obj (F.op.obj W)) (M₂.obj (F.op.obj W)) m₁ m₂

section Sections

/-- The canonical map from the sections of a presheaf of modules to the sections of its
pushforward. -/
def pushforwardSections {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (s : M.sections) : ((pushforward.{u} φ).obj M).sections where
  val _ := s.val _
  property _ := s.property _

/-- **The sections of a pushforward are the sections**, when the functor of sites is final. -/
lemma bijective_pushforwardSections [F.Final]
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    Function.Bijective (pushforwardSections φ (M := M)) :=
  Functor.bijective_sectionsPrecomp _ _

/-- The unit map of the pushforward, on a section of the structure presheaf: it is the
image of that section under `φ`. -/
lemma pushforwardEpsilon_app_apply (W : Cᵒᵖ) (a : S.obj W) :
    Hom.app (pushforwardEpsilon φ) W a = φ.app W a :=
  ModuleCat.restrictScalars_η (pushforwardRingHom φ W).hom a

/-- Compatibility of `pushforwardSections` with the corepresentation of sections by the unit
object. -/
lemma pushforwardSections_unitHomEquiv
    {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (g : 𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) ⟶ M) :
    pushforwardSections φ (M.unitHomEquiv g) =
      ((pushforward.{u} φ).obj M).unitHomEquiv
        (pushforwardEpsilon φ ≫ (pushforward.{u} φ).map g) := by
  ext W
  refine Eq.trans ?_ (congrArg (fun z ↦ Hom.app g (F.op.obj W) z)
    (pushforwardEpsilon_app_apply φ W 1)).symm
  refine congrArg (fun z ↦ Hom.app g (F.op.obj W) z) ?_
  exact (map_one (RingCat.Hom.hom (φ.app W))).symm

end Sections

/-- The pullback of presheaves of modules is oplax monoidal. -/
@[instance_reducible]
noncomputable def pullbackOplaxMonoidal [(pushforward.{u} φ).IsRightAdjoint] :
    (pullback.{u} φ).OplaxMonoidal :=
  letI := pushforwardLaxMonoidal φ
  (pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal

variable [(pushforward.{u} φ).IsRightAdjoint]

/-- A local section of a presheaf of modules, carried into the pullback by the unit of the
adjunction `f^* ⊣ f_*`. The ascribed type is the one in which the module of sections of the
pullback is spelled, which is what makes a pure tensor of two such sections elaborate. -/
noncomputable def pullbackAdjUnit
    (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (W : Cᵒᵖ)
    (z : M.obj W) : ((pullback.{u} φ).obj M).obj (F.op.obj W) :=
  Hom.app ((pullbackPushforwardAdjunction.{u} φ).unit.app M) W z

/-- A morphism out of a pullback, read on the unit image of a section: it is the adjoint
transpose evaluated at that section. -/
lemma homEquiv_symm_app_pullbackAdjUnit
    {M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (g : M ⟶ (pushforward.{u} φ).obj N) (W : Cᵒᵖ) (z : M.obj W) :
    Hom.app (((pullbackPushforwardAdjunction.{u} φ).homEquiv M N).symm g) (F.op.obj W)
        (pullbackAdjUnit φ M W z) = Hom.app g W z := by
  have h : g = (pullbackPushforwardAdjunction.{u} φ).unit.app M ≫
      (pushforward.{u} φ).map (((pullbackPushforwardAdjunction.{u} φ).homEquiv M N).symm g) := by
    simp [Adjunction.homEquiv_counit]
  exact (hom_congr_apply' h W z).symm

/-- **The oplax tensorator of the pullback of presheaves of modules is the canonical
comparison.** On the image of a pure tensor under the unit of the adjunction `f^* ⊣ f_*` it is
the pure tensor of the two unit images. -/
theorem delta_pullbackAdjUnit_tmul
    (M₁ M₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (W : Cᵒᵖ)
    (m₁ : M₁.obj W) (m₂ : M₂.obj W) :
    Hom.app (δ (self := pullbackOplaxMonoidal φ) (pullback.{u} φ) M₁ M₂) (F.op.obj W)
        (pullbackAdjUnit φ (M₁ ⊗ M₂) W
          (m₁ ⊗ₜ[(S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W] m₂)) =
      (pullbackAdjUnit φ M₁ W m₁ ⊗ₜ[
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (F.op.obj W)]
        pullbackAdjUnit φ M₂ W m₂) := by
  refine Eq.trans (homEquiv_symm_app_pullbackAdjUnit φ
    (((pullbackPushforwardAdjunction.{u} φ).unit.app M₁ ⊗ₘ
        (pullbackPushforwardAdjunction.{u} φ).unit.app M₂) ≫
      pushforwardMu φ ((pullback.{u} φ).obj M₁) ((pullback.{u} φ).obj M₂)) W
    (m₁ ⊗ₜ[(S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W] m₂)) ?_
  exact pushforwardMu_app_tmul φ ((pullback.{u} φ).obj M₁) ((pullback.{u} φ).obj M₂) W _ _

/-- An adjoint transpose of a morphism out of a pullback, read on a section. -/
lemma homEquiv_app_pullbackAdjUnit
    {M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (θ : (pullback.{u} φ).obj M ⟶ N) (W : Cᵒᵖ) (z : M.obj W) :
    Hom.app ((pullbackPushforwardAdjunction.{u} φ).homEquiv M N θ) W z =
      Hom.app θ (F.op.obj W) (pullbackAdjUnit φ M W z) := by
  have := homEquiv_symm_app_pullbackAdjUnit φ
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv M N θ) W z
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

/-- Two morphisms out of the pullback of an objectwise tensor product agree as soon as they
agree on the unit images of pure tensors of sections. -/
lemma pullback_tensor_hom_ext
    {M₁ M₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {θ₁ θ₂ : (pullback.{u} φ).obj (M₁ ⊗ M₂) ⟶ P}
    (h : ∀ (W : Cᵒᵖ) (m₁ : M₁.obj W) (m₂ : M₂.obj W),
      Hom.app θ₁ (F.op.obj W) (pullbackAdjUnit φ (M₁ ⊗ M₂) W
          (m₁ ⊗ₜ[(S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W] m₂)) =
        Hom.app θ₂ (F.op.obj W) (pullbackAdjUnit φ (M₁ ⊗ M₂) W
          (m₁ ⊗ₜ[(S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W] m₂))) :
    θ₁ = θ₂ := by
  refine ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).injective
    (tensorObj_hom_ext (F := M₁) (G := M₂) fun W m₁ m₂ ↦ ?_)
  exact (homEquiv_app_pullbackAdjUnit φ θ₁ W _).trans
    ((h W m₁ m₂).trans (homEquiv_app_pullbackAdjUnit φ θ₂ W _).symm)

/-- **The oplax unit of the pullback is an isomorphism**: the pullback of the structure
presheaf, read as a module over itself, is the structure presheaf of the source. -/
instance isIso_eta [F.Final] :
    IsIso (Functor.OplaxMonoidal.η (self := pullbackOplaxMonoidal φ) (pullback.{u} φ)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).bijective.of_comp_iff',
    ← (unitHomEquiv _).bijective.of_comp_iff']
  convert! (bijective_pushforwardSections φ M).comp (unitHomEquiv _).bijective
  ext g : 1
  dsimp
  rw [pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right]
  exact congrArg (fun z ↦ z ≫ (pushforward.{u} φ).map g)
    (Equiv.apply_symm_apply ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _)
      (pushforwardEpsilon φ))

end PresheafOfModules

namespace Stacks.PullbackMonoidal

open AlgebraicGeometry _root_.Stacks.PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.RingedSpace Stacks.PullbackTensor TopologicalSpace
open scoped TensorProduct

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The structure morphism `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X` of a morphism of ringed spaces, read as a
morphism of presheaves of not necessarily commutative rings, at the type the presheaf-level
pullback and pushforward expect: the source is `𝒪_Y ⋙ forget₂ _ _` and the target is
`(f⁻¹).op ⋙ 𝒪_X ⋙ forget₂ _ _`. This is `(Stacks.RingedSpace.structureSheafHom f).hom`, whose
own type spells the target through `Functor.sheafPushforwardContinuous`; the two are
definitionally equal, but the shape above is the one in which the presheaf of commutative rings
`𝒪_X` and the functor `f⁻¹` are visible to unification, and without it the instance
`(PresheafOfModules.pushforward _).IsRightAdjoint` is sought while they are still
metavariables. -/
noncomputable def structurePresheafHom :
    Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      (opensMap f).op ⋙ X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u} :=
  (structureSheafHom f).hom

/-- The pushforward of presheaves of modules along a morphism of ringed spaces is a right
adjoint, as a one-step instantiation of Mathlib's instance. -/
instance isRightAdjoint_presheafPushforward :
    (PresheafOfModules.pushforward.{u} (structurePresheafHom f)).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

variable (M N : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- **The oplax tensorator of the presheaf-level pullback is the canonical comparison of
Tag 01CD.** -/
theorem delta_eq_pullbackTensorIso :
    Functor.OplaxMonoidal.δ
        (self := PresheafOfModules.pullbackOplaxMonoidal (structurePresheafHom f))
        (PresheafOfModules.pullback.{u} (structurePresheafHom f)) M N =
      (pullbackTensorIso f.hom.c).hom.app (M, N) := by
  refine PresheafOfModules.pullback_tensor_hom_ext _ fun U x y ↦ ?_
  refine Eq.trans (PresheafOfModules.delta_pullbackAdjUnit_tmul _ M N U x y) ?_
  exact (pullbackTensorIso_hom_preUnit_tmul f M N U x y).symm

/-- The oplax tensorator of the presheaf-level pullback is an isomorphism. -/
instance isIso_delta : IsIso (Functor.OplaxMonoidal.δ
    (self := PresheafOfModules.pullbackOplaxMonoidal (structurePresheafHom f))
    (PresheafOfModules.pullback.{u} (structurePresheafHom f)) M N) := by
  rw [delta_eq_pullbackTensorIso]
  exact inferInstanceAs (IsIso ((pullbackTensorIso f.hom.c).app (M, N)).hom)

/-- **The pullback of presheaves of modules along a morphism of ringed spaces is a monoidal
functor**, with tensorator the canonical comparison of Tag 01CD. -/
@[instance_reducible]
noncomputable def presheafPullbackMonoidal :
    (PresheafOfModules.pullback.{u} (structurePresheafHom f)).Monoidal :=
  letI := PresheafOfModules.pullbackOplaxMonoidal (structurePresheafHom f)
  Functor.Monoidal.ofOplaxMonoidal _

/-- The tensorator of `presheafPullbackMonoidal` is the oplax one, hence by
`delta_eq_pullbackTensorIso` the canonical comparison of Tag 01CD. Without this the monoidal
structure would exist without being known to be the canonical one. -/
theorem presheafPullbackMonoidal_delta :
    Functor.OplaxMonoidal.δ (self := (presheafPullbackMonoidal f).toOplaxMonoidal)
        (PresheafOfModules.pullback.{u} (structurePresheafHom f)) M N =
      (pullbackTensorIso f.hom.c).hom.app (M, N) :=
  delta_eq_pullbackTensorIso f M N

/-- The unit of `presheafPullbackMonoidal` is the oplax one. -/
theorem presheafPullbackMonoidal_eta :
    Functor.OplaxMonoidal.η (self := (presheafPullbackMonoidal f).toOplaxMonoidal)
        (PresheafOfModules.pullback.{u} (structurePresheafHom f)) =
      Functor.OplaxMonoidal.η
        (self := PresheafOfModules.pullbackOplaxMonoidal (structurePresheafHom f))
        (PresheafOfModules.pullback.{u} (structurePresheafHom f)) :=
  rfl

end Stacks.PullbackMonoidal

end
