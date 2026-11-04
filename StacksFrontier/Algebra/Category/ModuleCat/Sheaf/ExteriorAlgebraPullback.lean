module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback and the exterior algebra of a sheaf of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F` be a sheaf of `O_Y`-modules.
Stacks 01CI asserts `f^* ⋀(F) = ⋀(f^*F)`. This file builds the canonical comparison
morphism, in the only direction that the pullback adjunction supplies it, and shows that the
three compatibilities of the source — with multiplication, with the unit, and with the
degree-one generators — determine it uniquely.

The exterior algebra is used here only through its universal property: a sheaf of graded
algebras `A` with a degree-one generator `ι : F ⟶ A.piece 1` that is initial among graded
algebras with a square-zero degree-one generator. Everything below takes that universal
property as a hypothesis rather than a construction, so nothing here depends on an
unconstructed exterior algebra.

The comparison is produced as an adjoint transpose. The pushforward `f_*B` of a graded
algebra on `X` is again a graded algebra (`GradedAlgebra.pushforward`): multiplication in a
sheaf of graded algebras is sectionwise bilinear, so pushing it forward is just reindexing
the opens, and no tensor product of sheaves of modules is involved. A square-zero generator
`κ : f^*F ⟶ B.piece 1` transposes to a square-zero generator `F ⟶ (f_*B).piece 1`, so the
universal property of `A` yields a unique unital homomorphism `A ⟶ f_*B`, whose degreewise
adjoint transposes are the comparison morphisms `f^*(A.piece n) ⟶ B.piece n`.

## Main definitions

* `SheafOfModules.GradedAlgebra.UnitalHom` is a homomorphism of sheaves of graded algebras
  that also preserves the degree-zero unit.
* `SheafOfModules.GradedAlgebra.SquareZero` says every local section of `M` has square zero
  under a degree-one generator `M ⟶ A.piece 1`.
* `SheafOfModules.GradedAlgebra.IsUniversal` is the common shape of the universal properties
  that cut out the tensor, exterior and symmetric algebras of a sheaf of modules: a degree-one
  generator with a given property `P` of generators, initial among those with `P`.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra` is the universal property of the exterior
  algebra: the `P = SquareZero` instance of `IsUniversal`.
* `SheafOfModules.GradedAlgebra.pushforward` is the pushforward of a sheaf of graded algebras
  along a continuous functor and a morphism of sheaves of rings.
* `SheafOfModules.GradedAlgebra.pullbackComparison` is the canonical comparison
  `f^*(A.piece n) ⟶ B.piece n`, and `pullbackComparisonSigma` its direct-sum form.

## Main results

* `IsUniversal.desc`, `desc_extends`, `desc_unique`, `hom_ext` and `eq_id` are the
  universal-property API, proved once for every property `P`.
* `IsUniversal.descIsIso`: the comparison homomorphism between two algebras universal for the
  same property has a two-sided inverse unital homomorphism, so `IsUniversal.pieceIso` is an
  isomorphism *of graded algebras*, not merely a degreewise isomorphism of sheaves of modules.
* `IsExteriorAlgebra.pieceIso`: two exterior algebras of the same sheaf of modules are
  isomorphic in every degree, canonically.
* `squareZero_pushforwardGenerator`: a square-zero degree-one generator of a graded algebra
  on `X` pushes forward to one on `Y`.
* `pullbackComparison_mul`, `pullbackComparison_one`, `pullbackComparison_generator`: the
  comparison is multiplicative and unital on pulled-back sections and matches the degree-one
  generators.
* `pullbackComparison_unique`: those three compatibilities determine the comparison.
* `pullbackComparisonSigma_ι`, `pullbackComparisonSigma_unique`,
  `isIso_pullbackComparisonSigma`: the direct-sum comparison restricts to the degreewise ones,
  is determined by that, and is invertible as soon as every degreewise comparison is.
* `isIso_pullbackComparison_of_isZero`: in a degree where both algebras vanish — for the
  exterior algebra, every negative degree — the comparison is invertible.

## Implementation notes

The comparison is a morphism, not yet an isomorphism, and that is the state of the
mathematics rather than a choice. Invertibility is proved in the source by producing a map
back out of the universal property of `⋀(f^*F)`, and that requires `f^*(⋀ F)` to carry a
graded algebra structure, i.e. a multiplication `f^*(A.piece i) × f^*(A.piece j) ⟶
f^*(A.piece (i + j))`. The pullback functor available here, `modulePullback`, is defined
abstractly as `(modulePushforward f).leftAdjoint`: it has no description of its sections, so
such a multiplication can only come from pullback commuting with tensor products, Stacks
01CD, which is not yet available. `isIso_pullbackComparisonSigma` and
`isIso_pullbackComparison_of_isZero` are stated so that supplying invertibility degreewise is
all that remains.

The pushforward is stated for an arbitrary continuous functor and morphism of sheaves of
rings, matching `SheafOfModules.pushforward`, and specializes to ringed spaces through
`RingedSpaceModuleAdjunction.structureSheafHom`. The universes of the site, the sheaf of
rings and the homogeneous pieces stay independent, as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits`; the ringed-space section
collapses them to one universe only because `modulePullback` itself does.

`IsUniversal` takes its property as `P : ∀ B, (M ⟶ B.piece 1) → Prop`, quantified over the
algebra, because `SquareZero` and the commutation condition cutting out the symmetric algebra
are conditions on a generator of a *varying* algebra: the test objects `B` of the universal
property each carry their own copy. `IsExteriorAlgebra` is its instance at `P = SquareZero`,
by definition rather than up to an equivalence, so the two APIs are the same API.

`SquareZero` quantifies over *all* local sections of `M`, not only over the sections of a
generating family. That is what the source says and it is what the universal property needs;
note that for a pullback `f^*F` it is strictly stronger than the condition on pulled-back
sections alone, unless one knows that pulled-back sections generate locally.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a v₁ v₂ u₁ u₂

namespace SheafOfModules.GradedAlgebra

section Defs

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{t}}

/-- A unital homomorphism of sheaves of graded algebras. -/
@[stacks 0FQW "unital homomorphisms of sheaves of graded algebras"]
structure UnitalHom (A B : GradedAlgebra.{t, a} R) where
  /-- The morphism of sheaves of modules in each degree. -/
  app (n : ℤ) : A.piece n ⟶ B.piece n
  /-- Products of homogeneous local sections are preserved. -/
  map_mul (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (app (i + j)).val.app U ((A.mul i j).app U x y) =
      (B.mul i j).app U ((app i).val.app U x) ((app j).val.app U y)
  /-- The degree-zero unit is preserved. -/
  map_one (U : Cᵒᵖ) : (app 0).val.app U (A.one.eval U) = B.one.eval U

namespace UnitalHom

variable {A B D : GradedAlgebra.{t, a} R}

/-- Two unital homomorphisms agree as soon as all their homogeneous components do. -/
@[ext]
theorem ext {g h : UnitalHom A B} (hgh : ∀ n, g.app n = h.app n) : g = h := by
  cases g; cases h; congr; funext n; exact hgh n

/-- The identity unital homomorphism. -/
def id (A : GradedAlgebra.{t, a} R) : UnitalHom A A where
  app _ := 𝟙 _
  map_mul _ _ _ _ _ := rfl
  map_one _ := rfl

/-- Composition of unital homomorphisms. -/
def comp (g : UnitalHom A B) (h : UnitalHom B D) : UnitalHom A D where
  app n := g.app n ≫ h.app n
  map_mul i j U x y := by
    change (h.app (i + j)).val.app U ((g.app (i + j)).val.app U _) = _
    rw [g.map_mul, h.map_mul]
    rfl
  map_one U := by
    change (h.app 0).val.app U ((g.app 0).val.app U _) = _
    rw [g.map_one, h.map_one]

/-- Each homogeneous component of the identity unital homomorphism is the identity. -/
@[simp] theorem id_app (A : GradedAlgebra.{t, a} R) (n : ℤ) : (id A).app n = 𝟙 _ := rfl

/-- Each homogeneous component of a composite is the composite of the components. -/
@[simp] theorem comp_app (g : UnitalHom A B) (h : UnitalHom B D) (n : ℤ) :
    (g.comp h).app n = g.app n ≫ h.app n := rfl

end UnitalHom

variable {M : SheafOfModules.{a} R}

/-- A degree-one generator has square zero if every local section of `M` has square zero
in the algebra. -/
def SquareZero {A : GradedAlgebra.{t, a} R} (ι : M ⟶ A.piece 1) : Prop :=
  ∀ (U : Cᵒᵖ) (s : M.val.obj U),
    (A.mul 1 1).app U (ι.val.app U s) (ι.val.app U s) = 0

/-- `A` with the degree-one generator `ι` is universal for the property `P` of degree-one
generators: `ι` has `P`, and every generator with `P` is obtained from `ι` by a unique unital
homomorphism.

The three universal properties of Section 17.21 are the instances `P = fun _ _ => True`
(the tensor algebra), `P = SquareZero` (the exterior algebra, which is `IsExteriorAlgebra`)
and `P = PairwiseCommutes` (the symmetric algebra). -/
def IsUniversal (P : ∀ B : GradedAlgebra.{t, a} R, (M ⟶ B.piece 1) → Prop)
    (A : GradedAlgebra.{t, a} R) (ι : M ⟶ A.piece 1) : Prop :=
  P A ι ∧
    ∀ (B : GradedAlgebra.{t, a} R) (κ : M ⟶ B.piece 1), P B κ →
      ∃! g : UnitalHom A B, ι ≫ g.app 1 = κ

namespace IsUniversal

variable {P : ∀ B : GradedAlgebra.{t, a} R, (M ⟶ B.piece 1) → Prop}
  {A B : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1} {κ : M ⟶ B.piece 1}

/-- The unique unital homomorphism out of a universal graded algebra extending a given
generator. -/
noncomputable def desc (hA : IsUniversal P A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) (hκ : P B κ) : UnitalHom A B :=
  (hA.2 B κ hκ).choose

/-- The homomorphism `desc` out of a universal graded algebra extends the given generator. -/
theorem desc_extends (hA : IsUniversal P A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) (hκ : P B κ) : ι ≫ (hA.desc B κ hκ).app 1 = κ :=
  (hA.2 B κ hκ).choose_spec.1

/-- A unital homomorphism out of a universal graded algebra extending a given generator is
`desc`. -/
theorem desc_unique (hA : IsUniversal P A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) (hκ : P B κ) {g : UnitalHom A B} (hg : ι ≫ g.app 1 = κ) :
    g = hA.desc B κ hκ :=
  (hA.2 B κ hκ).choose_spec.2 g hg

/-- Any two unital homomorphisms out of a universal graded algebra that agree on the generator
are equal. -/
theorem hom_ext (hA : IsUniversal P A ι) {g h : UnitalHom A B} (hκ : P B κ)
    (hg : ι ≫ g.app 1 = κ) (hh : ι ≫ h.app 1 = κ) : g = h :=
  (hA.desc_unique B κ hκ hg).trans (hA.desc_unique B κ hκ hh).symm

/-- A unital endomorphism of a universal graded algebra fixing the generator is the identity. -/
theorem eq_id (hA : IsUniversal P A ι) {g : UnitalHom A A} (hg : ι ≫ g.app 1 = ι) :
    g = UnitalHom.id A :=
  (hA.2 A ι hA.1).unique hg (by simp)

/-- The comparison homomorphism between two graded algebras universal for the same property is
a two-sided inverse to the comparison the other way: the two algebras are isomorphic *as
sheaves of graded algebras*, by a unital isomorphism. -/
theorem descIsIso (hA : IsUniversal P A ι) (hB : IsUniversal P B κ) :
    (hA.desc B κ hB.1).comp (hB.desc A ι hA.1) = UnitalHom.id A ∧
      (hB.desc A ι hA.1).comp (hA.desc B κ hB.1) = UnitalHom.id B := by
  refine ⟨hA.eq_id ?_, hB.eq_id ?_⟩
  · rw [UnitalHom.comp_app, ← Category.assoc, hA.desc_extends, hB.desc_extends]
  · rw [UnitalHom.comp_app, ← Category.assoc, hB.desc_extends, hA.desc_extends]

/-- Two graded algebras universal for the same property are canonically isomorphic in every
degree. -/
noncomputable def pieceIso (hA : IsUniversal P A ι) (hB : IsUniversal P B κ) (n : ℤ) :
    A.piece n ≅ B.piece n where
  hom := (hA.desc B κ hB.1).app n
  inv := (hB.desc A ι hA.1).app n
  hom_inv_id := by
    simpa using congrArg (fun g : UnitalHom A A => g.app n) (hA.descIsIso hB).1
  inv_hom_id := by
    simpa using congrArg (fun g : UnitalHom B B => g.app n) (hA.descIsIso hB).2

/-- The forward map of `pieceIso` is the comparison homomorphism in that degree. -/
@[simp] theorem pieceIso_hom (hA : IsUniversal P A ι) (hB : IsUniversal P B κ) (n : ℤ) :
    (hA.pieceIso hB n).hom = (hA.desc B κ hB.1).app n := rfl

/-- The inverse of `pieceIso` is the comparison homomorphism the other way in that degree. -/
@[simp] theorem pieceIso_inv (hA : IsUniversal P A ι) (hB : IsUniversal P B κ) (n : ℤ) :
    (hA.pieceIso hB n).inv = (hB.desc A ι hA.1).app n := rfl

/-- The canonical isomorphism between two graded algebras universal for the same property
carries one generator to the other. -/
theorem pieceIso_generator (hA : IsUniversal P A ι) (hB : IsUniversal P B κ) :
    ι ≫ (hA.pieceIso hB 1).hom = κ :=
  hA.desc_extends B κ hB.1

/-- The canonical isomorphism is multiplicative on homogeneous local sections. -/
theorem pieceIso_mul (hA : IsUniversal P A ι) (hB : IsUniversal P B κ) (i j : ℤ) (U : Cᵒᵖ)
    (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    ((hA.pieceIso hB (i + j)).hom).val.app U ((A.mul i j).app U x y) =
      (B.mul i j).app U (((hA.pieceIso hB i).hom).val.app U x)
        (((hA.pieceIso hB j).hom).val.app U y) :=
  (hA.desc B κ hB.1).map_mul i j U x y

/-- The canonical isomorphism carries the unit to the unit. -/
theorem pieceIso_one (hA : IsUniversal P A ι) (hB : IsUniversal P B κ) (U : Cᵒᵖ) :
    ((hA.pieceIso hB 0).hom).val.app U (A.one.eval U) = B.one.eval U :=
  (hA.desc B κ hB.1).map_one U

end IsUniversal

/-- `A` with its degree-one generator `ι` is *the* exterior algebra of `M`: the generator has
square zero, and `A` is initial among graded algebras equipped with a square-zero degree-one
generator. This is the `P = SquareZero` instance of `IsUniversal`. -/
def IsExteriorAlgebra (A : GradedAlgebra.{t, a} R) (ι : M ⟶ A.piece 1) : Prop :=
  IsUniversal (fun _ κ => SquareZero κ) A ι

namespace IsExteriorAlgebra

variable {A B : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1} {κ : M ⟶ B.piece 1}

/-- The unique unital homomorphism out of an exterior algebra extending its generator. -/
noncomputable def desc (hA : IsExteriorAlgebra A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) (hκ : SquareZero κ) : UnitalHom A B :=
  IsUniversal.desc hA B κ hκ

/-- The homomorphism `desc` out of an exterior algebra extends the given generator. -/
theorem desc_extends (hA : IsExteriorAlgebra A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) (hκ : SquareZero κ) : ι ≫ (hA.desc B κ hκ).app 1 = κ :=
  IsUniversal.desc_extends hA B κ hκ

/-- A unital homomorphism out of an exterior algebra extending a square-zero generator is
`desc`. -/
theorem desc_unique (hA : IsExteriorAlgebra A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) (hκ : SquareZero κ) {g : UnitalHom A B} (hg : ι ≫ g.app 1 = κ) :
    g = hA.desc B κ hκ :=
  IsUniversal.desc_unique hA B κ hκ hg

/-- A unital endomorphism of an exterior algebra that fixes the generator is the identity. -/
theorem eq_id (hA : IsExteriorAlgebra A ι) {g : UnitalHom A A} (hg : ι ≫ g.app 1 = ι) :
    g = UnitalHom.id A :=
  IsUniversal.eq_id hA hg

/-- Any two exterior algebras of the same sheaf of modules are isomorphic in every degree,
by the comparison homomorphism determined by the generators. -/
noncomputable def pieceIso (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (n : ℤ) :
    A.piece n ≅ B.piece n :=
  IsUniversal.pieceIso hA hB n

/-- The forward map of `pieceIso` is the comparison homomorphism in that degree. -/
@[simp] theorem pieceIso_hom (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (n : ℤ) :
    (hA.pieceIso hB n).hom = (hA.desc B κ hB.1).app n := rfl

/-- The canonical isomorphism between two exterior algebras carries one generator to the
other. -/
theorem pieceIso_generator (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) :
    ι ≫ (hA.pieceIso hB 1).hom = κ :=
  IsUniversal.pieceIso_generator hA hB

end IsExteriorAlgebra

end Defs

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : C ⥤ D}
  [G.IsContinuous J K] {S : Sheaf J RingCat.{t}} {R : Sheaf K RingCat.{t}}
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{t} J K).obj R)

/-- The pushforward of a sheaf of graded algebras along a continuous functor and a morphism
of sheaves of rings: the degreewise pushforward, with multiplication and unit taken over the
image opens. -/
noncomputable def pushforward (A : GradedAlgebra.{t, a} R) : GradedAlgebra.{t, a} S where
  piece n := (SheafOfModules.pushforward.{a} φ).obj (A.piece n)
  mul i j :=
    { app U := (A.mul i j).app (G.op.obj U)
      map_smul_left U r x y := (A.mul i j).map_smul_left (G.op.obj U) (φ.hom.app U r) x y
      map_smul_right U r x y := (A.mul i j).map_smul_right (G.op.obj U) (φ.hom.app U r) x y
      naturality f x y := (A.mul i j).naturality (G.op.map f) x y }
  one := PresheafOfModules.sectionsMk (fun U => A.one.eval (G.op.obj U))
    (by intro _ _ f; exact PresheafOfModules.sections_property A.one (G.op.map f))
  mul_assoc i j k U x y z := A.mul_assoc i j k (G.op.obj U) x y z
  one_mul i U x := A.one_mul i (G.op.obj U) x
  mul_one i U x := A.mul_one i (G.op.obj U) x

/-- The homogeneous pieces of the pushforward are the pushforwards of the pieces. -/
@[simp] theorem pushforward_piece (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    (pushforward φ A).piece n = (SheafOfModules.pushforward.{a} φ).obj (A.piece n) := rfl

/-- Multiplication in the pushforward is multiplication over the image open. -/
@[simp] theorem pushforward_mul_app (A : GradedAlgebra.{t, a} R) (i j : ℤ) (U : Cᵒᵖ) :
    ((pushforward φ A).mul i j).app U = (A.mul i j).app (G.op.obj U) := rfl

/-- The unit of the pushforward is the unit over the image open. -/
@[simp] theorem pushforward_one_eval (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    (pushforward φ A).one.eval U = A.one.eval (G.op.obj U) := rfl

end Pushforward

section RingedSpace

open AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

universe u

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Pullback of sheaves of modules along a morphism of ringed spaces is a left adjoint. -/
instance modulePullback_isLeftAdjoint : (modulePullback f).IsLeftAdjoint :=
  (modulePullbackPushforwardAdjunction f).isLeftAdjoint

/-- The adjoint transpose of a morphism out of a pullback is the composite of the
pullback-adjunction unit with the pushforward of that morphism, on local sections. -/
theorem homEquiv_val_app {M : SheafOfModules.{u} (structureSheafRing Y)}
    {N : SheafOfModules.{u} (structureSheafRing X)} (h : (modulePullback f).obj M ⟶ N)
    (U : (Opens Y.carrier)ᵒᵖ) (x : M.val.obj U) :
    (((modulePullbackPushforwardAdjunction f).homEquiv M N) h).val.app U x =
      h.val.app ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app M).val.app U x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The adjoint transpose of a morphism out of a pullback, evaluated on the pullback-unit
image of a local section. -/
theorem homEquiv_symm_val_app_unit {M : SheafOfModules.{u} (structureSheafRing Y)}
    {N : SheafOfModules.{u} (structureSheafRing X)} (h : M ⟶ (modulePushforward f).obj N)
    (U : (Opens Y.carrier)ᵒᵖ) (x : M.val.obj U) :
    (((modulePullbackPushforwardAdjunction f).homEquiv M N).symm h).val.app
        ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app M).val.app U x) =
      h.val.app U x := by
  conv_rhs => rw [← ((modulePullbackPushforwardAdjunction f).homEquiv M N).apply_symm_apply h]
  rw [Adjunction.homEquiv_unit]
  rfl

variable {F : SheafOfModules.{u} (structureSheafRing Y)}
  {A : GradedAlgebra.{u, u} (structureSheafRing Y)} {ι : F ⟶ A.piece 1}
  {B : GradedAlgebra.{u, u} (structureSheafRing X)}
  {κ : (modulePullback f).obj F ⟶ B.piece 1}

/-- The pushforward of a sheaf of graded algebras along a morphism of ringed spaces. -/
noncomputable abbrev pushforwardRingedSpace (B : GradedAlgebra.{u, u} (structureSheafRing X)) :
    GradedAlgebra.{u, u} (structureSheafRing Y) :=
  pushforward (structureSheafHom f) B

/-- The degree-one generator of the pushforward algebra obtained from a degree-one generator
of a pullback, by adjunction. -/
noncomputable def pushforwardGenerator (κ : (modulePullback f).obj F ⟶ B.piece 1) :
    F ⟶ (pushforwardRingedSpace f B).piece 1 :=
  (modulePullbackPushforwardAdjunction f).homEquiv F (B.piece 1) κ

/-- On local sections, the pushed-forward generator is the generator applied to the image of
the section under the pullback-adjunction unit. -/
theorem pushforwardGenerator_val_app (κ : (modulePullback f).obj F ⟶ B.piece 1)
    (U : (Opens Y.carrier)ᵒᵖ) (x : F.val.obj U) :
    (pushforwardGenerator f κ).val.app U x =
      κ.val.app ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app F).val.app U x) :=
  homEquiv_val_app f κ U x

/-- A square-zero degree-one generator of a graded algebra on `X` pushes forward to a
square-zero degree-one generator of the pushforward algebra on `Y`. -/
theorem squareZero_pushforwardGenerator (hκ : SquareZero κ) :
    SquareZero (pushforwardGenerator f κ) := by
  intro U x
  rw [pushforwardGenerator_val_app]
  exact hκ ((opensMap f).op.obj U) _

variable (hA : IsExteriorAlgebra A ι) (hκ : SquareZero κ)

/-- The unique unital homomorphism from the exterior algebra of `F` on `Y` to the pushforward
of a graded algebra on `X` with a square-zero generator of `f⁻¹F`. -/
noncomputable def pushforwardDesc : UnitalHom A (pushforwardRingedSpace f B) :=
  hA.desc _ (pushforwardGenerator f κ) (squareZero_pushforwardGenerator f hκ)

/-- The canonical comparison morphism from the pullback of the exterior algebra of `F` to the
exterior algebra of the pullback of `F`, in each degree. It is the adjoint transpose of the
unique unital homomorphism `A ⟶ f_*B` extending the pushed-forward generator. -/
noncomputable def pullbackComparison (n : ℤ) :
    (modulePullback f).obj (A.piece n) ⟶ B.piece n :=
  ((modulePullbackPushforwardAdjunction f).homEquiv (A.piece n) (B.piece n)).symm
    ((pushforwardDesc f hA hκ).app n)

/-- The comparison morphism computes the chosen unital homomorphism on pulled-back sections. -/
theorem pullbackComparison_unit (n : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (x : (A.piece n).val.obj U) :
    (pullbackComparison f hA hκ n).val.app ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app (A.piece n)).val.app U x) =
      ((pushforwardDesc f hA hκ).app n).val.app U x :=
  homEquiv_symm_val_app_unit f _ U x

/-- The comparison morphism is multiplicative on pulled-back sections. -/
theorem pullbackComparison_mul (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (a : (A.piece i).val.obj U) (b : (A.piece j).val.obj U) :
    (pullbackComparison f hA hκ (i + j)).val.app ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app (A.piece (i + j))).val.app U
          ((A.mul i j).app U a b)) =
      (B.mul i j).app ((opensMap f).op.obj U)
        ((pullbackComparison f hA hκ i).val.app ((opensMap f).op.obj U)
          (((modulePullbackPushforwardAdjunction f).unit.app (A.piece i)).val.app U a))
        ((pullbackComparison f hA hκ j).val.app ((opensMap f).op.obj U)
          (((modulePullbackPushforwardAdjunction f).unit.app (A.piece j)).val.app U b)) := by
  rw [pullbackComparison_unit, pullbackComparison_unit, pullbackComparison_unit]
  exact (pushforwardDesc f hA hκ).map_mul i j U a b

/-- The comparison morphism carries the pulled-back unit to the unit. -/
theorem pullbackComparison_one (U : (Opens Y.carrier)ᵒᵖ) :
    (pullbackComparison f hA hκ 0).val.app ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app (A.piece 0)).val.app U
          (A.one.eval U)) =
      B.one.eval ((opensMap f).op.obj U) := by
  rw [pullbackComparison_unit]
  exact (pushforwardDesc f hA hκ).map_one U

/-- The comparison morphism carries the pulled-back degree-one generator to the degree-one
generator of the pullback. -/
theorem pullbackComparison_generator (U : (Opens Y.carrier)ᵒᵖ) (s : F.val.obj U) :
    (pullbackComparison f hA hκ 1).val.app ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app (A.piece 1)).val.app U
          (ι.val.app U s)) =
      κ.val.app ((opensMap f).op.obj U)
        (((modulePullbackPushforwardAdjunction f).unit.app F).val.app U s) := by
  rw [pullbackComparison_unit, ← pushforwardGenerator_val_app]
  exact congrArg (fun h : F ⟶ (pushforwardRingedSpace f B).piece 1 => h.val.app U s)
    (hA.desc_extends _ (pushforwardGenerator f κ) (squareZero_pushforwardGenerator f hκ))

/-- The three compatibilities pin the comparison down: a degreewise family of morphisms out of
the pullback that is multiplicative, unital and compatible with the degree-one generators on
pulled-back sections is the canonical comparison. -/
theorem pullbackComparison_unique
    (e : ∀ n : ℤ, (modulePullback f).obj (A.piece n) ⟶ B.piece n)
    (emul : ∀ (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj U)
      (b : (A.piece j).val.obj U),
      (e (i + j)).val.app ((opensMap f).op.obj U)
          (((modulePullbackPushforwardAdjunction f).unit.app (A.piece (i + j))).val.app U
            ((A.mul i j).app U a b)) =
        (B.mul i j).app ((opensMap f).op.obj U)
          ((e i).val.app ((opensMap f).op.obj U)
            (((modulePullbackPushforwardAdjunction f).unit.app (A.piece i)).val.app U a))
          ((e j).val.app ((opensMap f).op.obj U)
            (((modulePullbackPushforwardAdjunction f).unit.app (A.piece j)).val.app U b)))
    (eone : ∀ U : (Opens Y.carrier)ᵒᵖ,
      (e 0).val.app ((opensMap f).op.obj U)
          (((modulePullbackPushforwardAdjunction f).unit.app (A.piece 0)).val.app U
            (A.one.eval U)) =
        B.one.eval ((opensMap f).op.obj U))
    (egen : ∀ (U : (Opens Y.carrier)ᵒᵖ) (s : F.val.obj U),
      (e 1).val.app ((opensMap f).op.obj U)
          (((modulePullbackPushforwardAdjunction f).unit.app (A.piece 1)).val.app U
            (ι.val.app U s)) =
        κ.val.app ((opensMap f).op.obj U)
          (((modulePullbackPushforwardAdjunction f).unit.app F).val.app U s))
    (n : ℤ) : e n = pullbackComparison f hA hκ n := by
  set adj := modulePullbackPushforwardAdjunction f with hadj
  let key := fun (m : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece m).val.obj U) =>
    homEquiv_val_app f (e m) U x
  refine ((adj.homEquiv (A.piece n) (B.piece n)).symm_apply_apply (e n)).symm.trans
    (congrArg (fun h : UnitalHom A (pushforwardRingedSpace f B) =>
        (adj.homEquiv (A.piece n) (B.piece n)).symm (h.app n))
      (hA.desc_unique _ (pushforwardGenerator f κ) (squareZero_pushforwardGenerator f hκ)
        (g := { app := fun m => (adj.homEquiv (A.piece m) (B.piece m)) (e m)
                map_mul := fun i j U a b =>
                  ((key (i + j) U _).trans (emul i j U a b)).trans
                    (congrArg₂ (fun p q => ((B.mul i j).app ((opensMap f).op.obj U) p) q)
                      (key i U a).symm (key j U b).symm)
                map_one := fun U => (key 0 U _).trans (eone U) }) ?_))
  ext U s
  exact (key 1 U (ι.val.app U s)).trans
    ((egen U s).trans (pushforwardGenerator_val_app f κ U s).symm)

/-- The comparison on the underlying direct-sum sheaves: the pullback of the direct sum of the
homogeneous pieces maps to the direct sum of the homogeneous pieces of the pullback. -/
noncomputable def pullbackComparisonSigma :
    (modulePullback f).obj (∐ fun n : ℕ => A.piece (n : ℤ)) ⟶ ∐ fun n : ℕ => B.piece (n : ℤ) :=
  (PreservesCoproduct.iso (modulePullback f) fun n : ℕ => A.piece (n : ℤ)).hom ≫
    Limits.Sigma.map fun n : ℕ => pullbackComparison f hA hκ (n : ℤ)

/-- The direct-sum comparison restricts on each homogeneous summand to the degreewise
comparison. -/
theorem pullbackComparisonSigma_ι (n : ℕ) :
    (modulePullback f).map (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n) ≫
        pullbackComparisonSigma f hA hκ =
      pullbackComparison f hA hκ (n : ℤ) ≫ Sigma.ι (fun m : ℕ => B.piece (m : ℤ)) n := by
  have h : (modulePullback f).map (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n) ≫
        (PreservesCoproduct.iso (modulePullback f) fun m : ℕ => A.piece (m : ℤ)).hom =
      Sigma.ι (fun m : ℕ => (modulePullback f).obj (A.piece (m : ℤ))) n :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit (modulePullback f) fun m : ℕ => A.piece (m : ℤ))
      (colimit.isColimit _) (Discrete.mk n)
  rw [pullbackComparisonSigma, ← Category.assoc, h, Limits.Sigma.ι_map]

/-- The direct-sum comparison is the unique morphism restricting to the degreewise
comparisons. -/
theorem pullbackComparisonSigma_unique
    {s : (modulePullback f).obj (∐ fun n : ℕ => A.piece (n : ℤ)) ⟶ ∐ fun n : ℕ => B.piece (n : ℤ)}
    (hs : ∀ n : ℕ, (modulePullback f).map (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n) ≫ s =
      pullbackComparison f hA hκ (n : ℤ) ≫ Sigma.ι (fun m : ℕ => B.piece (m : ℤ)) n) :
    s = pullbackComparisonSigma f hA hκ :=
  (isColimitOfHasCoproductOfPreservesColimit (modulePullback f)
      fun n : ℕ => A.piece (n : ℤ)).hom_ext fun n => by
    rw [Cofan.mk_ι_app, hs, ← pullbackComparisonSigma_ι]

/-- If the comparison is invertible in every nonnegative degree, so is the comparison of the
underlying direct-sum sheaves. -/
theorem isIso_pullbackComparisonSigma
    (h : ∀ n : ℕ, IsIso (pullbackComparison f hA hκ (n : ℤ))) :
    IsIso (pullbackComparisonSigma f hA hκ) := by
  rw [pullbackComparisonSigma]
  have := h
  infer_instance

/-- A sheaf of modules all of whose sections vanish is a zero object. -/
theorem isZero_of_forall_eq_zero {M : SheafOfModules.{u} (structureSheafRing Y)}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (x : M.val.obj U), x = 0) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact h U x

/-- In a degree where both graded algebras vanish, the comparison is automatically
invertible. -/
theorem isIso_pullbackComparison_of_isZero (n : ℤ) (hAn : IsZero (A.piece n))
    (hBn : IsZero (B.piece n)) : IsIso (pullbackComparison f hA hκ n) :=
  ((modulePullback f).map_isZero hAn).isIso hBn _

end RingedSpace

end SheafOfModules.GradedAlgebra
