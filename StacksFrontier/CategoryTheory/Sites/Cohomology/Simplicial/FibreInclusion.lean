module

public import StacksFrontier.CategoryTheory.Sites.AbelianPullbackExact.LanCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.ProjectionDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteLowerShriek
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.OneMorphismContinuity
import StacksCore.Tactic.StacksAttribute

/-!
# The fibre inclusions of the simplicial site, and the acyclicity of `Lπ_!`

Let `C` be a small site with topology `J` and let `Δ × C` carry the topology
`Stacks.SimplicialModules.projectionTopology C J` it inherits from `(C, J)` along the projection
`π : Δ × C ⥤ C` of Stacks 09D0. For an object `n` of `Δ` the *fibre inclusion* is the section

`i_n : C ⥤ Δ × C`, `U ↦ (n, U)`

of `π`, that is `CategoryTheory.Functor.prodSectionSnd n`. This file shows that `i_n` is a
continuous and cocontinuous functor of sites, assembles the resulting pair of adjoint functors on
abelian sheaves, and uses them to **discharge the acyclicity hypothesis of Stacks 07AC for `π`**:

`Stacks.SimplicialModules.abelianLowerShriekAcyclic_projection`.

That is the hypothesis `h` of
`Stacks.SimplicialModules.isIso_derivedLowerShriekHomology_map_of_fibrewise`, and it is now
unconditional — in particular the abelian half of Stacks 0D6X is **not** needed for the
projection.

## How the acyclicity is obtained

`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing` reduces the
statement about complexes to the object-level vanishing

`Ext^{≥1}(j_{W!}ℤ_W, π⁻¹I) = 0` for every object `W` of `Δ × C` and every injective abelian
sheaf `I` on `C`,

which for a general functor of sites is the content of Stacks 0D6X and is proved there by a Čech
computation. For `π` no Čech computation is needed, because the generators factor through the
fibre inclusions and the fibre inclusions have *exact* lower shriek. Writing `W = (n, U)`:

* `j_{(n,U)!}ℤ ≅ (i_n)_!(j_{U!}ℤ_U)`, both sides corepresenting the sections over `(n, U)`
  (`Stacks.SimplicialModules.extensionByZeroUnitAbFibreIso`);
* `(i_n)_!` is exact, so its right adjoint — restriction along `i_n`, that is *evaluation in
  degree `n`* — carries injectives to injectives, and `Ext` out of `(i_n)_!X` in `Ab(Δ × C)` is
  `Ext` out of `X` in `Ab(C)` against the restriction
  (`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`);
* evaluation in degree `n` of `π⁻¹I` is `I` again, because `i_n ⋙ π = 𝟭 C`
  (`Stacks.SimplicialModules.fibreRestrictionCompProjectionRestrictionIso`);
* and `Ext^{≥1}(-, I) = 0` for an injective `I`.

The exactness of `(i_n)_!` is where the geometry of the simplicial site enters. It is **not** an
instance of Stacks 04BH as stated in
`StacksFrontier/CategoryTheory/Sites/Cocontinuous/LowerShriekExactness.lean`, whose hypotheses ask
`C` for fibre products and equalizers; it is an instance of the pseudofilteredness criterion
`Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_of_weaklyInitial`, which asks
nothing of `C` at all. The comma category of `i_n` over an object `(m, V)` is the disjoint union,
over the morphisms `φ : m ⟶ n` of `Δ`, of the category of objects of `C` under `V`, and each
summand has the initial object `(V, 𝟙)`; so the pointwise Kan extension is a finite direct sum of
copies of the coefficients and the colimits computing it are exact.

## Main definitions

* `Stacks.SimplicialModules.fibreInclusion`: `i_n : C ⥤ Δ × C`.
* `Stacks.SimplicialModules.fibreRestriction`: restriction along `i_n` on abelian sheaves, that
  is evaluation in degree `n`.
* `Stacks.SimplicialModules.fibreExtension`: `(i_n)_!`, its left adjoint, with
  `Stacks.SimplicialModules.fibreAdjunction`.

## Main results

* `Stacks.SimplicialModules.isContinuous_fibreInclusion` and
  `Stacks.SimplicialModules.isCocontinuous_fibreInclusion`: `i_n` is a continuous and
  cocontinuous functor of sites, with no hypothesis on `C`. Both are read off the fact that `i_n`
  is a 1-morphism of fibred categories from `𝟭 C` to `π`
  (`Stacks.SimplicialModules.isFibredOneMorphism_prodSectionSnd`).
* `Stacks.SimplicialModules.preservesFiniteLimits_fibreExtension`: **`(i_n)_!` is exact.**
* `Stacks.SimplicialModules.fibreRestrictionCompProjectionRestrictionIso`: evaluation in degree
  `n` undoes restriction along `π`.
* `Stacks.SimplicialModules.extensionByZeroUnitAbFibreIso`: `j_{(n,U)!}ℤ ≅ (i_n)_!(j_{U!}ℤ_U)`.
* `Stacks.SimplicialModules.abelianLowerShriekAcyclic_projection` and
  `Stacks.SimplicialModules.simplicialSituation_abelianLowerShriekAcyclic`: **the acyclicity
  statement of Stacks 07AC holds for `π`**, in the two shapes its consumers ask for.

## Implementation notes

Every universe is the universe `u` of the objects and of the morphisms of the site, and the
abelian coefficients are `AddCommGrpCat.{u}`, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AcyclicityUnconditional.lean`. The
constraint is the pointwise description of the left Kan extension used by the exactness
criterion, which holds for coefficients whose morphisms live in the universe of the two sites;
`Δ` contributes nothing, `SimplexCategory` being a `Type` with `Type`-valued homs.

`Stacks.SimplicialModules.isoOfCorepresentation` is the Yoneda argument in the only form needed
here: a natural bijection of the hom-sets out of two objects produces an isomorphism between
them. It is stated by hand rather than through `CategoryTheory.coyoneda`, because the two
hom-functors are assembled out of two different adjunctions and never appear as `coyoneda.obj`.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek

namespace Stacks.SimplicialModules

universe u

/-! ### A Yoneda argument -/

section Corepresentation

universe w' v' u'

variable {A : Type u'} [Category.{v'} A]

/-- **Two objects with naturally bijective hom-sets out of them are isomorphic.** The bijections
are precomposition with a single morphism `Y ⟶ X`, by naturality applied to the identity of `X`,
and that morphism is an isomorphism because the bijections are. -/
def isoOfCorepresentation {X Y : A} (e : ∀ Z : A, (X ⟶ Z) ≃ (Y ⟶ Z))
    (he : ∀ {Z Z' : A} (a : X ⟶ Z) (k : Z ⟶ Z'), e Z' (a ≫ k) = e Z a ≫ k) :
    X ≅ Y := by
  have hkey : ∀ {Z : A} (a : X ⟶ Z), e Z a = e X (𝟙 X) ≫ a := by
    intro Z a
    have h := he (𝟙 X) a
    simpa using h
  have h1 : e X (𝟙 X) ≫ (e Y).symm (𝟙 Y) = 𝟙 Y := by
    have h := hkey ((e Y).symm (𝟙 Y))
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have h2 : e X ((e Y).symm (𝟙 Y) ≫ e X (𝟙 X)) = e X (𝟙 X) := by
    rw [hkey ((e Y).symm (𝟙 Y) ≫ e X (𝟙 X)), ← Category.assoc, h1, Category.id_comp]
  exact ⟨(e Y).symm (𝟙 Y), e X (𝟙 X), (e X).injective h2, h1⟩

/-- **Two objects corepresenting the same functor are isomorphic**, in the form in which the
corepresentation is given: a family of bijections of the hom-sets out of each of them with a
family of types `T`, each compatible with one and the same action `m` of the morphisms of the
ambient category on `T`. Composing one family with the inverse of the other gives the natural
bijection that `Stacks.SimplicialModules.isoOfCorepresentation` consumes. -/
def isoOfHomEquivs {A : Type u'} [Category.{v'} A] {X Y : A} {T : A → Type w'}
    (φ : ∀ Z : A, (X ⟶ Z) ≃ T Z) (ψ : ∀ Z : A, (Y ⟶ Z) ≃ T Z)
    (m : ∀ {Z Z' : A}, (Z ⟶ Z') → T Z → T Z')
    (hφ : ∀ {Z Z' : A} (a : X ⟶ Z) (k : Z ⟶ Z'), φ Z' (a ≫ k) = m k (φ Z a))
    (hψ : ∀ {Z Z' : A} (b : Y ⟶ Z) (k : Z ⟶ Z'), ψ Z' (b ≫ k) = m k (ψ Z b)) :
    X ≅ Y :=
  isoOfCorepresentation (fun Z => (φ Z).trans (ψ Z).symm) (by
    intro Z Z' a k
    refine (ψ Z').injective ?_
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, hφ, hψ])

end Corepresentation

/-! ### The fibre inclusion as a 1-morphism of fibred categories -/

section OneMorphism

universe v₁ u₁ v₂ u₂

variable {D : Type u₁} [Category.{v₁} D] {C : Type u₂} [Category.{v₂} C]

attribute [local implicit_reducible] CategoryTheory.Functor.prodSectionSnd

/-- **The coordinate section `U ↦ (d, U)` is a 1-morphism of fibred categories** from `𝟭 C` to
the second projection: it is strictly over `C`, since `i_d ⋙ π = 𝟭 C`, and it carries every
morphism of `C` to one whose first component is the identity, which is strongly cartesian for
the second projection by `CategoryTheory.Prod.snd_isStronglyCartesian_id`. -/
lemma isFibredOneMorphism_prodSectionSnd (d : D) :
    (𝟭 C).IsFibredOneMorphism (CategoryTheory.Prod.snd D C)
      (Functor.prodSectionSnd d) where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro R T f a b φ hφ
    have := hφ
    obtain rfl := IsHomLift.domain_eq (𝟭 C) f φ
    obtain rfl := IsHomLift.codomain_eq (𝟭 C) f φ
    obtain rfl := IsHomLift.eq_of_isHomLift (𝟭 C) f φ
    exact CategoryTheory.Prod.snd_isStronglyCartesian_id ((d, b) : D × C) _

/-- Below every object of the comma category of the coordinate section `U ↦ (d, U)` over an
object `V` of `D × C` there is an object which maps to everything mapping to it and admits at
most one morphism to any object: the object `V.2` with the structure morphism
`(x.hom.1, 𝟙 V.2)`, which is initial in the summand of the comma category indexed by the first
component of `x.hom`.

A morphism of structured arrows is the identity in the `D` coordinate, so it cannot change that
first component; and a morphism out of the displayed object is determined by its structure
equation in the `C` coordinate. -/
theorem weaklyInitial_structuredArrow_prodSectionSnd (d : D) (V : D × C)
    (x : StructuredArrow V (Functor.prodSectionSnd d)) :
    ∃ W : StructuredArrow V (Functor.prodSectionSnd (C := C) d),
      (∀ {y : StructuredArrow V (Functor.prodSectionSnd (C := C) d)}, (y ⟶ x) →
          Nonempty (W ⟶ y)) ∧
        ∀ {y : StructuredArrow V (Functor.prodSectionSnd (C := C) d)} (q q' : W ⟶ y), q = q' := by
  refine ⟨StructuredArrow.mk (Y := V.2)
    (CategoryTheory.Prod.mkHom x.hom.1 (𝟙 V.2)), ?_, ?_⟩
  · intro y g
    have hfst : y.hom.1 = x.hom.1 := by
      simpa using congrArg (fun u => u.1) (StructuredArrow.w g)
    refine ⟨StructuredArrow.homMk y.hom.2 (CategoryTheory.Prod.hom_ext ?_ ?_)⟩
    · simp [hfst]
    · simp
  · intro y q q'
    have e : ∀ r : type_of% q, StructuredArrow.Hom.right r = y.hom.2 := fun r => by
      simpa using congrArg (fun u => u.2) (StructuredArrow.w r)
    exact StructuredArrow.hom_ext _ _ ((e q).trans (e q').symm)

end OneMorphism

/-! ### Continuity and cocontinuity -/

section Continuity

variable (C : Type u) [SmallCategory C] (J : GrothendieckTopology C)

/-- The fibre inclusion `i_n : C ⥤ Δ × C`, `U ↦ (n, U)`, of the simplicial site of
Stacks 09D0: the coordinate section of the projection `π` in degree `n`. -/
abbrev fibreInclusion (n : SimplexCategory) : C ⥤ SimplexCategory × C :=
  Functor.prodSectionSnd n

/-- The composite of the fibre inclusion with the projection is the identity. -/
theorem fibreInclusion_comp_projection (n : SimplexCategory) :
    fibreInclusion C n ⋙ projection C = 𝟭 C :=
  rfl

/-- **Stacks 06NW for the projection, continuity.** The projection `π : Δ × C ⥤ C` is continuous
for the topology `Δ × C` inherits from `(C, J)`, with no hypothesis on `C`: it is a 1-morphism of
fibred categories from itself to `𝟭 C`, and `C` inherits its own topology along `𝟭 C`. -/
instance isContinuous_projection :
    (projection C).IsContinuous (projectionTopology C J) J := by
  have hid : (𝟭 C).IsFibered := CategoryTheory.Functor.isFiberedInGroupoids_id.isFibered
  have h := (CategoryTheory.Functor.isFibredOneMorphism_id
    (projection C)).isContinuous_inheritedTopology J
  rwa [CategoryTheory.Functor.inheritedTopology_id] at h

/-- **Stacks 06NW for the projection, cocontinuity.** -/
instance isCocontinuous_projection :
    (projection C).IsCocontinuous (projectionTopology C J) J := by
  have hid : (𝟭 C).IsFibered := CategoryTheory.Functor.isFiberedInGroupoids_id.isFibered
  have h := (CategoryTheory.Functor.isFibredOneMorphism_id
    (projection C)).isCocontinuous_inheritedTopology J
  rwa [CategoryTheory.Functor.inheritedTopology_id] at h

/-- **The fibre inclusion is a continuous functor of sites.** `i_n` is a 1-morphism of fibred
categories from `𝟭 C` to `π`, so it is continuous from the topology `C` inherits along `𝟭 C` —
which is `J` — to the topology `Δ × C` inherits along `π`. No hypothesis on `C` is used. -/
instance isContinuous_fibreInclusion (n : SimplexCategory) :
    (fibreInclusion C n).IsContinuous J (projectionTopology C J) := by
  have hid : (𝟭 C).IsFibered := CategoryTheory.Functor.isFiberedInGroupoids_id.isFibered
  have h := (isFibredOneMorphism_prodSectionSnd
    (C := C) n).isContinuous_inheritedTopology J
  rwa [CategoryTheory.Functor.inheritedTopology_id] at h

/-- **The fibre inclusion is a cocontinuous functor of sites.** -/
instance isCocontinuous_fibreInclusion (n : SimplexCategory) :
    (fibreInclusion C n).IsCocontinuous J (projectionTopology C J) := by
  have hid : (𝟭 C).IsFibered := CategoryTheory.Functor.isFiberedInGroupoids_id.isFibered
  have h := (isFibredOneMorphism_prodSectionSnd
    (C := C) n).isCocontinuous_inheritedTopology J
  rwa [CategoryTheory.Functor.inheritedTopology_id] at h

-- The statement that each slice restriction of an inherited-topology sheaf on `Δ × C` is a
-- `J`-sheaf lives at its natural generality, for an arbitrary product category, as
-- `CategoryTheory.Presheaf.isSheaf_prodSectionSnd_of_isSheaf_inheritedTopology`. Since
-- `fibreInclusion C n` and `projectionTopology C J` are abbreviations for
-- `Functor.prodSectionSnd n` and `(Prod.snd SimplexCategory C).inheritedTopology J`, that
-- declaration applies here verbatim.

end Continuity

/-! ### The adjoint pair on abelian sheaves -/

section Abelian

variable (C : Type u) [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{u}]

/-- Restriction of abelian sheaves along the fibre inclusion: **evaluation in degree `n`**. -/
abbrev fibreRestriction (n : SimplexCategory) :
    Sheaf (projectionTopology C J) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  abelianRestriction.{u} J (projectionTopology C J) (fibreInclusion C n)

/-- `(i_n)_!`, the lower-shriek functor of the fibre inclusion on abelian sheaves: the left
adjoint of evaluation in degree `n`. -/
abbrev fibreExtension (n : SimplexCategory) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf (projectionTopology C J) AddCommGrpCat.{u} :=
  abelianLowerShriek.{u} J (projectionTopology C J) (fibreInclusion C n)

/-- The adjunction `(i_n)_! ⊣ (i_n)⁻¹` on abelian sheaves. -/
abbrev fibreAdjunction (n : SimplexCategory) :
    fibreExtension C J n ⊣ fibreRestriction C J n :=
  abelianAdjunction.{u} J (projectionTopology C J) (fibreInclusion C n)

omit [HasSheafify J AddCommGrpCat] in
/-- **`(i_n)_!` is exact.** Lower shriek is always right exact, being a left adjoint; it is left
exact here by the pseudofilteredness criterion of
`StacksFrontier/CategoryTheory/Sites/AbelianPullbackExact/LanCriterion.lean`, whose hypothesis is
`Stacks.SimplicialModules.weaklyInitial_structuredArrow_prodSectionSnd`: the comma category of
`i_n` over `(m, V)` is the disjoint union over `φ : m ⟶ n` of the objects of `C` under `V`, and
each summand has an initial object. Nothing is asked of `C`; in particular the fibre products
and equalizers of Stacks 04BH are not needed. -/
theorem preservesFiniteLimits_fibreExtension (n : SimplexCategory) :
    PreservesFiniteLimits (fibreExtension C J n) :=
  Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_span_and_coequalizer
    (fibreInclusion C n) AddCommGrpCat.{u} J (projectionTopology C J)
    (by
      have h := fun V : SimplexCategory × C =>
        Stacks.Sites.AbelianPullback.span_and_coequalizer_op_of_weaklyInitial
          (fun x => weaklyInitial_structuredArrow_prodSectionSnd n V x)
      exact ⟨fun V => (h V).1, fun V => (h V).2⟩)

/-- `(i_n)_!` preserves monomorphisms, being exact. -/
theorem preservesMonomorphisms_fibreExtension (n : SimplexCategory) :
    (fibreExtension C J n).PreservesMonomorphisms :=
  have := preservesFiniteLimits_fibreExtension C J n
  inferInstance

/-- **Evaluation in degree `n` carries injectives to injectives**, being the right adjoint of an
exact functor. -/
theorem preservesInjectiveObjects_fibreRestriction (n : SimplexCategory) :
    (fibreRestriction C J n).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_fibreExtension C J n
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (fibreAdjunction C J n)

/-- **Evaluation in degree `n` undoes restriction along the projection.** Restriction is
precomposition with the opposite functor and `i_n ⋙ π = 𝟭 C`, so the composite is the identity
on the nose. -/
def fibreRestrictionCompProjectionRestrictionIso (n : SimplexCategory) :
    abelianRestriction.{u} (projectionTopology C J) J (projection C) ⋙
        fibreRestriction C J n ≅
      𝟭 (Sheaf J AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Abelian

/-! ### The generators of the simplicial site come from the fibres -/

section Generators

/- The `HasSheafify` hypotheses are binders of each declaration rather than section variables:
Lean 4.35 lets instance search see a section variable even under `omit`, which would make the
two naturality lemmas below depend on the variable they leave out. -/
variable (C : Type u) [SmallCategory C] (J : GrothendieckTopology C)

/-- **Morphisms out of `(i_n)_!(j_{U!}ℤ_U)` are sections over `(n, U)`.** The adjunction
`(i_n)_! ⊣ (i_n)⁻¹` followed by the corepresentation of sections by `j_{U!}ℤ_U`; the sections of
the restriction over `U` are the sections over `(n, U)`. -/
def fibreExtensionHomEquiv [HasSheafify J AddCommGrpCat.{u}]
    [HasSheafify (projectionTopology C J) AddCommGrpCat.{u}] (n : SimplexCategory) (U : C)
    (Z : Sheaf (projectionTopology C J) AddCommGrpCat.{u}) :
    ((fibreExtension C J n).obj (extensionByZeroUnitAb.{u} J U) ⟶ Z) ≃
      ((fibreRestriction C J n).obj Z).obj.obj (op U) :=
  ((fibreAdjunction C J n).homEquiv _ _).trans
    (extensionByZeroUnitAbHomEquiv.{u} J U ((fibreRestriction C J n).obj Z))

/-- `fibreExtensionHomEquiv` is natural in the target: postcomposing with `k : Z ⟶ Z'`
corresponds to applying the restriction of `k` to the section over `U`. -/
lemma fibreExtensionHomEquiv_naturality [HasSheafify J AddCommGrpCat.{u}]
    (n : SimplexCategory) (U : C)
    {Z Z' : Sheaf (projectionTopology C J) AddCommGrpCat.{u}}
    (a : (fibreExtension C J n).obj (extensionByZeroUnitAb.{u} J U) ⟶ Z) (k : Z ⟶ Z') :
    fibreExtensionHomEquiv C J n U Z' (a ≫ k) =
      ((fibreRestriction C J n).map k).hom.app (op U)
        (fibreExtensionHomEquiv C J n U Z a) := by
  show extensionByZeroUnitAbHomEquiv.{u} J U ((fibreRestriction C J n).obj Z')
      ((fibreAdjunction C J n).homEquiv _ _ (a ≫ k)) = _
  rw [(fibreAdjunction C J n).homEquiv_naturality_right]
  exact extensionByZeroUnitAbHomEquiv_naturality.{u} J (U := U) _ _

/-- **Morphisms out of `j_{(n,U)!}ℤ` are sections over `(n, U)`**, read as sections of the degree
`n` evaluation over `U`: the two are the same group, restriction along `i_n` being precomposition
with `i_nᵒᵖ`. -/
def projExtensionByZeroUnitAbHomEquiv [HasSheafify J AddCommGrpCat.{u}]
    [HasSheafify (projectionTopology C J) AddCommGrpCat.{u}] (n : SimplexCategory) (U : C)
    (Z : Sheaf (projectionTopology C J) AddCommGrpCat.{u}) :
    (extensionByZeroUnitAb.{u} (projectionTopology C J)
        ((n, U) : SimplexCategory × C) ⟶ Z) ≃
      ((fibreRestriction C J n).obj Z).obj.obj (op U) :=
  extensionByZeroUnitAbHomEquiv.{u} (projectionTopology C J)
    ((n, U) : SimplexCategory × C) Z

/-- `projExtensionByZeroUnitAbHomEquiv` is natural in the target: postcomposing with
`k : Z ⟶ Z'` corresponds to applying the restriction of `k` to the section over `U`. -/
lemma projExtensionByZeroUnitAbHomEquiv_naturality
    [HasSheafify (projectionTopology C J) AddCommGrpCat.{u}] (n : SimplexCategory) (U : C)
    {Z Z' : Sheaf (projectionTopology C J) AddCommGrpCat.{u}}
    (a : extensionByZeroUnitAb.{u} (projectionTopology C J)
      ((n, U) : SimplexCategory × C) ⟶ Z) (k : Z ⟶ Z') :
    projExtensionByZeroUnitAbHomEquiv C J n U Z' (a ≫ k) =
      ((fibreRestriction C J n).map k).hom.app (op U)
        (projExtensionByZeroUnitAbHomEquiv C J n U Z a) :=
  extensionByZeroUnitAbHomEquiv_naturality.{u} (projectionTopology C J)
    (U := ((n, U) : SimplexCategory × C)) a k

/-- **The free abelian sheaf on a representable of the simplicial site comes from the fibre.**
`j_{(n,U)!}ℤ ≅ (i_n)_!(j_{U!}ℤ_U)`: both corepresent the sections over `(n, U)`, the first by
`Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAbHomEquiv` on `Δ × C` and the second
by `Stacks.SimplicialModules.fibreExtensionHomEquiv`. -/
def extensionByZeroUnitAbFibreIso [HasSheafify J AddCommGrpCat.{u}]
    [HasSheafify (projectionTopology C J) AddCommGrpCat.{u}] (n : SimplexCategory) (U : C) :
    extensionByZeroUnitAb.{u} (projectionTopology C J) ((n, U) : SimplexCategory × C) ≅
      (fibreExtension C J n).obj (extensionByZeroUnitAb.{u} J U) :=
  isoOfHomEquivs (projExtensionByZeroUnitAbHomEquiv C J n U)
    (fibreExtensionHomEquiv C J n U)
    (fun k x => ((fibreRestriction C J n).map k).hom.app (op U) x)
    (fun a k => projExtensionByZeroUnitAbHomEquiv_naturality C J n U a k)
    (fun b k => fibreExtensionHomEquiv_naturality C J n U b k)

end Generators

/-! ### The acyclicity of `Lπ_!` -/

section Acyclicity

variable (C : Type u) [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (projectionTopology C J) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (projectionTopology C J) AddCommGrpCat.{u})]

/-- **The vanishing that Stacks 0D6X supplies for a general functor of sites, proved directly
for the projection.** For every object `W` of `Δ × C`, every injective abelian sheaf `I` on `C`
and every `k ≥ 1`,

`Ext^k(j_{W!}ℤ_W, π⁻¹I) = 0`.

Write `W = (n, U)`. Then `j_{W!}ℤ_W` is `(i_n)_!(j_{U!}ℤ_U)`, so `Ext` out of it against a sheaf
`Z` on `Δ × C` is `Ext` out of `j_{U!}ℤ_U` against the degree `n` evaluation of `Z`: that is the
`Ext`-comparison along the adjunction `(i_n)_! ⊣ (i_n)⁻¹`, available because `(i_n)_!` is exact
and therefore `(i_n)⁻¹` preserves injectives. At `Z = π⁻¹I` the degree `n` evaluation is `I`
itself, and `Ext` of positive degree into an injective object vanishes. -/
theorem subsingleton_ext_extensionByZeroUnitAb_projection (W : SimplexCategory × C)
    (I : Sheaf J AddCommGrpCat.{u}) (hI : Injective I) (k : ℕ) (hk : 1 ≤ k) :
    Subsingleton (Abelian.Ext.{u}
      (extensionByZeroUnitAb.{u} (projectionTopology C J) W)
      ((abelianRestriction.{u} (projectionTopology C J) J (projection C)).obj I) k) := by
  obtain ⟨n, U⟩ := W
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have := preservesInjectiveObjects_fibreRestriction C J n
  set Z : Sheaf (projectionTopology C J) AddCommGrpCat.{u} :=
    (abelianRestriction.{u} (projectionTopology C J) J (projection C)).obj I
  have hinj : Injective ((fibreRestriction C J n).obj Z) :=
    Injective.of_iso ((fibreRestrictionCompProjectionRestrictionIso C J n).app I).symm hI
  have hzero2 : IsZero ((Abelian.extFunctorObj.{u} (extensionByZeroUnitAb.{u} J U)
      (k + 1)).obj ((fibreRestriction C J n).obj Z)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (Abelian.Ext.subsingleton_of_injective _ _ k)
  have hiso := Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (fibreAdjunction C J n) (extensionByZeroUnitAbFibreIso C J n U).symm (k + 1)
  have hzero : IsZero ((Abelian.extFunctorObj.{u}
      (extensionByZeroUnitAb.{u} (projectionTopology C J)
        ((n, U) : SimplexCategory × C)) (k + 1)).obj Z) :=
    IsZero.of_iso hzero2 (hiso.app Z)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hzero

/-- **The acyclicity statement of Stacks 07AC holds for the projection `π : Δ × C ⥤ C`.** Lower
shriek along `π` carries every bounded above acyclic complex of abelian sheaves on `Δ × C` whose
terms are direct sums of the free abelian sheaves `j_{W!}ℤ_W` to an acyclic complex.

This is `Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing` fed
with `Stacks.SimplicialModules.subsingleton_ext_extensionByZeroUnitAb_projection`. It is the
hypothesis `h` of
`Stacks.SimplicialModules.isIso_derivedLowerShriekHomology_map_of_fibrewise`, and it carries no
hypothesis on `C` beyond smallness and the standing sheafification and injectivity ones. -/
theorem abelianLowerShriekAcyclic_projection :
    AbelianLowerShriekAcyclic.{u} (projectionTopology C J) J (projection C) :=
  abelianLowerShriekAcyclic_of_ext_vanishing.{u, u} (projectionTopology C J) J (projection C)
    fun W I hI k hk => subsingleton_ext_extensionByZeroUnitAb_projection C J W I hI k hk

end Acyclicity

/-! ### The acyclicity in the shape the fibred-category situation asks for -/

section Situation

variable (B : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify B.J AddCommGrpCat.{u}]
  [HasSheafify ((CategoryTheory.Prod.snd SimplexCategory B.C).inheritedTopology B.J)
    AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf B.J AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf ((CategoryTheory.Prod.snd SimplexCategory B.C).inheritedTopology B.J)
    AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf B.J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf ((CategoryTheory.Prod.snd SimplexCategory B.C).inheritedTopology B.J)
    AddCommGrpCat.{u})]

/-- **The acyclicity statement of Stacks 07AC for the simplicial situation.** The same statement
as `Stacks.SimplicialModules.abelianLowerShriekAcyclic_projection`, phrased for
`Stacks.SimplicialModules.simplicialSituation`, which is the shape in which
`Stacks.SimplicialModules.isIso_derivedLowerShriekHomology_map_of_fibrewise` asks for it. So that
reduction of Stacks 09D2 no longer carries the acyclicity hypothesis. -/
theorem simplicialSituation_abelianLowerShriekAcyclic :
    (simplicialSituation B).AbelianLowerShriekAcyclic :=
  abelianLowerShriekAcyclic_projection B.C B.J

end Situation

end Stacks.SimplicialModules

end
