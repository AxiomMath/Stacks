module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderAlgebraExtension
public import StacksFrontier.Deformation.ToposThickening.AlgebraExtensionBaseProblem
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutAlgebraExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Flat deformations of an algebraic space across a first-order thickening of its base

Let `S` be a scheme, `Y ⊂ Y'` a first order thickening of algebraic spaces over `S` and
`f : X ⟶ Y` a flat morphism. This file sets up the objects of [Stacks Project, Tag 0D17]:

* the pairs `(f' : X' ⟶ Y', a)` of the source, with `f'` flat and `a : X ≅ X' ×_{Y'} Y` over `Y`;
* their isomorphisms and isomorphism classes;
* the square-zero extension problem of [Stacks Project, Tag 08UF] on the small étale site of `X`
  to which the source's proof reduces them: the lower row is the inverse image along `f` of the
  extension `0 → 𝒞_{Y/Y'} → t⁻¹𝒪_{Y'} → 𝒪_Y → 0` of the thickening, the prescribed module is
  `f^*𝒞_{Y/Y'}`, and the prescribed map `f⁻¹𝒞_{Y/Y'} ⟶ f^*𝒞_{Y/Y'}` is the canonical one, the
  unit of extension of scalars along `f^♯`.

## Main definitions

* `AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation`: a flat deformation, recorded as
  a flat `f' : X' ⟶ Y'` and `i : X ⟶ X'` making the square over `Y ⊂ Y'` cartesian;
  `Deformation.ofPair` and `Deformation.pairIso` pass between this and the pair `(f', a)`.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation.Iso`, `Classes`: isomorphisms of
  deformations and their isomorphism classes.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.problem`: the extension problem.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS Y'.1)

variable {Z} {X : AlgebraicSpaces B S hS} (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S
    hS))

/-- **A flat deformation of `f : X ⟶ Y` over `Y'`**: a flat morphism `f' : X' ⟶ Y'` of algebraic
spaces together with `i : X ⟶ X'` such that
```
X --i--> X'
|        |
f        f'
v        v
Y --t--> Y'
```
is cartesian. This is the pair `(f', a)` of [Stacks Project, Tag 0D17] with `i = pr₁ ∘ a`: an
isomorphism `a : X ≅ X' ×_{Y'} Y` over `Y` is the same thing as such a cartesian square
(`Deformation.ofPair`, `Deformation.pairIso`). -/
structure Deformation where
  /-- The deformed space `X'`. -/
  X' : AlgebraicSpaces B S hS
  /-- The flat morphism `f' : X' ⟶ Y'`. -/
  f' : X' ⟶ Y'
  /-- `f'` is flat. -/
  flat : IsFlat B S hS f'.hom
  /-- The inclusion `X ⟶ X'` of the special fibre. -/
  i : X ⟶ X'
  /-- The square is cartesian. -/
  isPullback : IsPullback i f f' (subspaceInclusion B S hS Y' Z)

variable {f}

namespace Deformation

/-- The deformation attached to a pair `(f', a)` of the source: a flat `f' : X' ⟶ Y'` and an
isomorphism `a : X ≅ X' ×_{Y'} Y` over `Y`. -/
def ofPair {X' : AlgebraicSpaces B S hS} (f' : X' ⟶ Y') (hf' : IsFlat B S hS f'.hom)
    (a : X ≅ pullback f' (subspaceInclusion B S hS Y' Z)) (ha : a.hom ≫ pullback.snd f'
        (subspaceInclusion B S hS Y' Z) = f) :
    Deformation f where
  X' := X'
  f' := f'
  flat := hf'
  i := a.hom ≫ pullback.fst f' (subspaceInclusion B S hS Y' Z)
  isPullback := by
    subst ha
    exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ a (by simp) (by simp)

/-- The isomorphism `a : X ≅ X' ×_{Y'} Y` over `Y` of a deformation. -/
def pairIso (D : Deformation f) : X ≅ pullback D.f' (subspaceInclusion B S hS Y' Z) :=
  D.isPullback.isoPullback

/-- The composite of `pairIso` with the second projection `X' ×_{Y'} Y ⟶ Y` is `f`. -/
@[reassoc (attr := simp)]
theorem pairIso_hom_snd (D : Deformation f) :
    D.pairIso.hom ≫ pullback.snd D.f' (subspaceInclusion B S hS Y' Z) = f :=
  D.isPullback.isoPullback_hom_snd

/-- The composite of `pairIso` with the first projection `X' ×_{Y'} Y ⟶ X'` is `i`. -/
@[reassoc (attr := simp)]
theorem pairIso_hom_fst (D : Deformation f) :
    D.pairIso.hom ≫ pullback.fst D.f' (subspaceInclusion B S hS Y' Z) = D.i :=
  D.isPullback.isoPullback_hom_fst

/-- An isomorphism of deformations: an isomorphism `X'₁ ≅ X'₂` over `Y'` compatible with the
identifications of `X` with the special fibres. Since the pullback component over `Y` of both
identifications is `f`, compatibility with `a₁` and `a₂` is the single equation
`i₁ ≫ e = i₂` (`Deformation.Iso.pairIso_comm`). -/
structure Iso (D E : Deformation f) where
  /-- The isomorphism of the deformed spaces. -/
  hom : D.X' ≅ E.X'
  /-- It lies over `Y'`. -/
  hom_f' : hom.hom ≫ E.f' = D.f'
  /-- It is compatible with the identifications of the special fibre. -/
  compat : D.i ≫ hom.hom = E.i

namespace Iso

/-- The identity. -/
def refl (D : Deformation f) : Iso D D where
  hom := CategoryTheory.Iso.refl _
  hom_f' := Category.id_comp _
  compat := Category.comp_id _

/-- The inverse. -/
def symm {D E : Deformation f} (e : Iso D E) : Iso E D where
  hom := e.hom.symm
  hom_f' := by rw [CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.inv_comp_eq, e.hom_f']
  compat := by rw [CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.comp_inv_eq, e.compat]

/-- The composite. -/
def trans {D E F : Deformation f} (e : Iso D E) (g : Iso E F) : Iso D F where
  hom := e.hom ≪≫ g.hom
  hom_f' := by rw [CategoryTheory.Iso.trans_hom, Category.assoc, g.hom_f', e.hom_f']
  compat := by rw [CategoryTheory.Iso.trans_hom, ← Category.assoc, e.compat, g.compat]

/-- Two isomorphisms of deformations are equal if their underlying isomorphisms are. -/
@[ext]
theorem ext {D E : Deformation f} {e e' : Iso D E} (h : e.hom = e'.hom) : e = e' := by
  cases e; cases e'; cases h; rfl

/-- An isomorphism of deformations is compatible with the identifications `a` of `X` with the
special fibres, through the base change of the isomorphism. -/
theorem pairIso_comm {D E : Deformation f} (e : Iso D E) :
    D.pairIso.hom ≫ pullback.map D.f' (subspaceInclusion B S hS Y' Z) E.f' (subspaceInclusion B S hS
        Y' Z) e.hom.hom (𝟙 _) (𝟙 _)
        (by rw [e.hom_f', Category.comp_id]) (by simp) = E.pairIso.hom := by
  apply pullback.hom_ext
  · simp [e.compat]
  · simp

end Iso

/-- Deformations and their isomorphisms form a groupoid. -/
instance : Groupoid (Deformation f) where
  Hom := Iso
  id := Iso.refl
  comp e g := e.trans g
  id_comp _ := Iso.ext (CategoryTheory.Iso.refl_trans _)
  comp_id _ := Iso.ext (CategoryTheory.Iso.trans_refl _)
  assoc _ _ _ := Iso.ext (CategoryTheory.Iso.trans_assoc _ _ _)
  inv e := e.symm
  inv_comp _ := Iso.ext (CategoryTheory.Iso.symm_self_id _)
  comp_inv _ := Iso.ext (CategoryTheory.Iso.self_symm_id _)

end Deformation

variable (f) in
/-- Isomorphism of deformations, as a setoid. -/
def setoid : Setoid (Deformation f) where
  r D E := Nonempty (D ⟶ E)
  iseqv := ⟨fun D => ⟨𝟙 D⟩, fun ⟨e⟩ => ⟨inv e⟩, fun ⟨e⟩ ⟨g⟩ => ⟨e ≫ g⟩⟩

variable (f) in
/-- **The set of isomorphism classes of pairs `(f' : X' ⟶ Y', a)`.** -/
abbrev Classes := Quotient (setoid f)

/-! ### The extension problem -/

variable (hZ : IsFirstOrderThickening B S hS Y' Z.1)

include hZ in
/-- The extension `0 → 𝒞_{Y/Y'} → t⁻¹𝒪_{Y'} → 𝒪_Y → 0` of the thickening `Y ⊂ Y'`. -/
abbrev baseExtension :=
  firstOrderAlgebraExtension B S hS Z hZ (𝟙 Y')

variable (f) in
/-- `f^*𝒞_{Y/Y'}`, the prescribed module of the problem. -/
abbrev pulledBackConormal : Modules.{u, u} B S hS X.1 X.2 :=
  (modulePullback B S hS f).obj (conormalModule B S hS Y' Z)

variable (f) in
/-- **The extension problem of [Stacks Project, Tag 08UF] attached to `f` and `Y ⊂ Y'`**, on the
small étale ringed topos of `X`: the lower row is the inverse image along `f` of the extension
`0 → 𝒞_{Y/Y'} → t⁻¹𝒪_{Y'} → 𝒪_Y → 0` of the thickening, the prescribed module is
`f^*𝒞_{Y/Y'}`, and the prescribed map `c : f⁻¹𝒞_{Y/Y'} ⟶ f^*𝒞_{Y/Y'}` is the unit of extension
of scalars along `f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`. This is the diagram displayed in the proof of
[Stacks Project, Tag 0D17]. -/
def problem :
    Deformation.ToposThickening.RingedToposExtensionProblem (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :=
  Deformation.ToposThickening.RingedToposExtensionProblem.ofBaseAlgebraExtension
    (X := smallEtaleRingedTopos B S hS X) (D := smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩
        : AlgebraicSpaces B S hS))
    (smallEtaleRingedToposHom B S hS f) (baseExtension hZ)
    (pulledBackConormal f) ((extendScalarsFSharpAdjunction B S hS f).unit.app _)

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
