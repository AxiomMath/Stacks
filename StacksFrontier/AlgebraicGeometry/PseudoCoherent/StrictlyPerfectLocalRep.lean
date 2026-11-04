module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectCone
import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived morphisms out of a strictly perfect complex are locally morphisms of complexes

Let `X` be a ringed space and let `ℰ`, `ℱ` be complexes of `𝒪_X`-modules with `ℰ` strictly
perfect. Stacks 08C9 says that (1) every morphism `ℰ ⟶ ℱ` in the derived category is, on an open
neighbourhood of each point of `X`, induced by a morphism of complexes, and (2) a morphism of
complexes whose image in the derived category vanishes is null-homotopic on an open neighbourhood
of each point.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_local_homotopy_zero_of_derived_eq_zero` is Stacks 08C9
  part (2).
* `AlgebraicGeometry.RingedSpace.exists_local_complex_map` is Stacks 08C9 part (1).
* `AlgebraicGeometry.RingedSpace.exists_local_lift_homotopy_restrictModules` is Stacks 08C8 in
  the `restrictModules` idiom, obtained from the slice-idiom form by transport along
  `AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`, which identifies
  `AlgebraicGeometry.RingedSpace.restrictModules` with restriction to the slice `Over U` of the
  site of opens of `X` followed by the equivalence
  `AlgebraicGeometry.RingedSpace.overToRestricted`.
* `AlgebraicGeometry.RingedSpace.overToRestricted_preservesFiniteLimits` and
  `AlgebraicGeometry.RingedSpace.overToRestricted_preservesFiniteColimits`: that equivalence is
  exact.
* `CochainComplex.nonempty_homotopy_zero_of_lift_homotopy_id`: an additive functor sends a
  morphism to a null-homotopic one as soon as the morphism is killed by a map which the functor
  makes split up to homotopy.
* `CochainComplex.exists_homotopy_lift_of_comp_natIso` transports a lift up to homotopy along an
  identification `Φ ⋙ T ≅ Ψ` of additive functors.
* `CategoryTheory.Functor.mapDerivedCategory_map_eq_of_lift`: for an exact functor `R`, a lift up
  to homotopy of `R(γ)` through `R(f)` represents the image under `R` of the left fraction
  `Q(γ) ≫ Q(f)⁻¹`.

Part (1) is assembled from `AlgebraicGeometry.RingedSpace.exists_local_lift_of_left_fac`, which
is its geometric half, and `AlgebraicGeometry.RingedSpace.exists_local_complex_map_of_instances`,
which is the statement with the exactness of restriction taken from the ambient instances rather
than bundled into the conclusion. The split is not cosmetic: the statement of part (1) mentions
`CategoryTheory.Functor.mapDerivedCategory` under a binder for the open subset, and elaborating
it consumes most of a declaration's heartbeat budget, so the work has to happen in declarations
whose own statements are cheap.

## Implementation notes

The two parts of Stacks 08C9 are stated in the two idioms in which restriction to an open subset
appears in this development, each matching the way the part is used.

Part (2) is stated in the *slice* idiom `SheafOfModules.overFunctor`, like Stacks 08C6, 08C7 and
08C8, because a null homotopy is all it asserts and no abelian structure on the restricted
category is involved.

Part (1) is stated in the `restrictModules` idiom — the pushforward to the ringed space
`X.restrict U.isOpenEmbedding`, in which Stacks 08CB phrases pseudo-coherence — because it speaks
of the derived category of the open subspace, through `CategoryTheory.Functor.mapDerivedCategory`
and `CategoryTheory.Functor.mapDerivedCategoryFactors`. That needs the restricted category to be
abelian with a chosen derived category, which is available for the ringed space
`X.restrict U.isOpenEmbedding` and not for the slice `Over U` of the site of opens of `X`.

The bridge between the two idioms is paid exactly once, in
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`: restriction to the open
subspace *is* restriction to the slice followed by Mathlib's equivalence
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, and the identification is `Iso.refl`, because
`StrictlyPerfect.structureSheafOfRings (X.restrict U.isOpenEmbedding)` is
`U.sheafRestrict.obj (StrictlyPerfect.structureSheafOfRings X)` and the morphism of sheaves of
rings that `AlgebraicGeometry.RingedSpace.restrictModules` pushes forward along is the identity.
Mathlib has this compatibility only at the level of schemes, and proves it under a backward
compatibility flag; here it is a reflexivity isomorphism, and
`CategoryTheory.Functor.mapHomologicalComplexCompIso` propagates it to complexes. The
corresponding *equality* of the two functors on complexes is not usable: deciding it exhausts
the heartbeat budget, so the isomorphism is what gets used.

The one point needing care is that the two descriptions of the restricted category — the
`𝒪`-modules of the ringed space `X.restrict U.isOpenEmbedding` and the sheaves of modules over
`U.sheafRestrict.obj 𝒪_X` — are definitionally equal but not syntactically so, and typeclass
resolution unfolds only at reducible transparency. That is why the equivalence is given a name,
`AlgebraicGeometry.RingedSpace.overToRestricted`, whose type is written with the
first description: every instance below is then stated and found in one and the same spelling,
and the passage to the other one happens only inside `exact`, at default transparency.

Exactness of restriction follows from the identification: restriction to the slice preserves
finite limits (`SheafOfModules.overFunctor_preservesFiniteLimits`) and, being the pushforward
along the identity morphism of sheaves of rings, has a left adjoint, so it preserves finite
colimits; an equivalence preserves both.

Universes: the statements are at `AlgebraicGeometry.RingedSpace.{u, u}` with `𝒪_X`-modules in
universe `u`, which is the generality in which `StrictlyPerfect.OXMod` and
`StrictlyPerfect.IsStrictlyPerfect` are defined. The derived category of `X` and the derived
categories of its open subspaces are hypotheses with independent universes.

`AlgebraicGeometry.RingedSpace.restrictModules` is polymorphic in the module universe, and that
universe is not determined by its two explicit arguments, so every occurrence of it in a
statement starts out carrying a universe metavariable. In the two statements that mention
`CategoryTheory.Functor.mapDerivedCategory` the module universe is therefore written out,
`restrictModules.{u, u} X U`: the surrounding statement forces it to be `u` anyway, but the
instances that `CategoryTheory.Functor.mapDerivedCategory` needs — additivity and the two halves
of exactness — are found before the unification that would fix it, and some of them are stated
at `restrictModules.{u, u}` and some polymorphically, so instance search runs on a goal with an
unsolved universe and exhausts its heartbeats instead of resolving the coercions in the
statement.

## References

* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 08C8](https://stacks.math.columbia.edu/tag/08C8)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace CochainComplex

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Let `Φ` be an additive functor, let `α : ℰ ⟶ ℱ` and `t : 𝒵 ⟶ ℰ` be morphisms of cochain
complexes with `t ≫ α` null-homotopic, and suppose `Φ(t)` has a left inverse `β` up to homotopy.
Then `Φ(α)` is null-homotopic.

Indeed `Φ(α)` is homotopic to `β ≫ Φ(t) ≫ Φ(α) = β ≫ Φ(t ≫ α)`, which is null-homotopic because
`t ≫ α` is. -/
public theorem nonempty_homotopy_zero_of_lift_homotopy_id {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D] (Φ : C ⥤ D) [Φ.Additive]
    {E F Z : CochainComplex C ℤ} (α : E ⟶ F) (t : Z ⟶ E)
    (β : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
    (hβ : Nonempty (Homotopy (β ≫ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map t)
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (𝟙 E))))
    (hnull : Nonempty (Homotopy (t ≫ α) 0)) :
    Nonempty (Homotopy ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0) := by
  obtain ⟨hβ⟩ := hβ
  obtain ⟨hnull⟩ := hnull
  have h₁ : Homotopy ((β ≫ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map t) ≫
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α)
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
    have hh := hβ.compRight ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α)
    rwa [← Functor.map_comp, Category.id_comp] at hh
  have h₂ : Homotopy ((β ≫ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map t) ≫
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0 := by
    have hh := (Φ.mapHomotopy (c := ComplexShape.up ℤ) hnull).compLeft β
    rwa [Functor.map_comp, Functor.map_zero, comp_zero, ← Category.assoc] at hh
  exact ⟨h₁.symm.trans h₂⟩

/-- Transport of a lift up to homotopy along an identification `Φ ⋙ T ≅ Ψ` of additive functors:
if `β` is a lift of `Φ(α)` through `Φ(f)` up to homotopy, then conjugating `T(β)` by the induced
isomorphism of the functors on complexes gives a lift of `Ψ(α)` through `Ψ(f)` up to homotopy.

This is how a statement proved for restriction to the slice `Over U` of the site of opens of a
ringed space is turned into the same statement for restriction to the open subspace; see
`AlgebraicGeometry.RingedSpace.exists_local_lift_homotopy_restrictModules`. The hypothesis is
taken in existential form so that the functors on complexes can be abbreviated before the lift
is named. -/
public theorem exists_homotopy_lift_of_comp_natIso {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D] {D' : Type u₃}
    [Category.{v₃} D'] [Preadditive D'] (Φ : C ⥤ D) (T : D ⥤ D') (Ψ : C ⥤ D') [Φ.Additive]
    [T.Additive] [Ψ.Additive] (ε : Φ ⋙ T ≅ Ψ) {E F G : CochainComplex C ℤ} (α : E ⟶ F)
    (f : G ⟶ F)
    (h : ∃ β : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
        (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj G,
      Nonempty (Homotopy (β ≫ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α))) :
    ∃ β : (Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
        (Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj G,
      Nonempty (Homotopy (β ≫ (Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
        ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  obtain ⟨β, ⟨h⟩⟩ := h
  have e : Φ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      T.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        Ψ.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso ε (ComplexShape.up ℤ)
  have hnatf := e.hom.naturality f
  have hnatα := e.hom.naturality α
  simp only [Functor.comp_map] at hnatf hnatα
  have h₁ : e.inv.app E ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (β ≫ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫ e.hom.app F =
      (e.inv.app E ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫ e.hom.app G) ≫
        (Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map f := by
    rw [Functor.map_comp, Category.assoc, hnatf]
    simp only [Category.assoc]
  have h₂ : e.inv.app E ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α) ≫ e.hom.app F =
      (Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map α := by
    rw [hnatα, Iso.inv_hom_id_app_assoc]
  refine ⟨e.inv.app E ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫ e.hom.app G, ?_⟩
  rw [← h₁, ← h₂]
  exact ⟨((T.mapHomotopy h).compRight (e.hom.app F)).compLeft (e.inv.app E)⟩

end CochainComplex

namespace CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- Let `R` be an exact functor between abelian categories with chosen derived categories, let
`α = Q(γ) ≫ Q(f)⁻¹` be a morphism of the derived category of the source written as a left
fraction, and let `β` be a lift of `R(γ)` through `R(f)` up to homotopy. Then `β` represents the
image of `α` under `R`, compared through `CategoryTheory.Functor.mapDerivedCategoryFactors`.

`R(f)` is again a quasi-isomorphism because `R` is exact, so `Q(R(f))` is invertible, and the
claim follows from naturality of `mapDerivedCategoryFactors` at `γ` and at `f` together with
`Q(β ≫ R(f)) = Q(R(γ))`, which holds because the two are homotopic. -/
public theorem Functor.mapDerivedCategory_map_eq_of_lift {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₂} B] (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {E F G : CochainComplex A ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (γ : E ⟶ G) (f : F ⟶ G)
    (hf : IsIso (DerivedCategory.Q.map f))
    (hαfac : α = DerivedCategory.Q.map γ ≫ CategoryTheory.inv (DerivedCategory.Q.map f))
    (β : (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (h : Nonempty (Homotopy (β ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ))) :
    R.mapDerivedCategory.map α ≫ R.mapDerivedCategoryFactors.hom.app F =
      R.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β := by
  have hfq : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso (C := A) f).mp hf
  have hiso : IsIso (DerivedCategory.Q.map
      ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := B) _).2 inferInstance
  have hisoD : IsIso (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) := inferInstance
  have hnatf := R.mapDerivedCategoryFactors_hom_naturality f
  have hnatγ := R.mapDerivedCategoryFactors_hom_naturality γ
  have hβ : DerivedCategory.Q.map (β ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ) :=
    DerivedCategory.Q_map_eq_of_homotopy (C := B) h.some
  have hinv : CategoryTheory.inv (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) ≫
      R.mapDerivedCategoryFactors.hom.app F =
        R.mapDerivedCategoryFactors.hom.app G ≫
          CategoryTheory.inv (DerivedCategory.Q.map
            ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hnatf, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  calc R.mapDerivedCategory.map α ≫ R.mapDerivedCategoryFactors.hom.app F
      = R.mapDerivedCategory.map (DerivedCategory.Q.map γ) ≫
          CategoryTheory.inv (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) ≫
            R.mapDerivedCategoryFactors.hom.app F := by
        rw [hαfac, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
          Category.assoc]
    _ = R.mapDerivedCategory.map (DerivedCategory.Q.map γ) ≫
          R.mapDerivedCategoryFactors.hom.app G ≫
            CategoryTheory.inv (DerivedCategory.Q.map
              ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by rw [hinv]
    _ = (R.mapDerivedCategoryFactors.hom.app E ≫
          DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ)) ≫
            CategoryTheory.inv (DerivedCategory.Q.map
              ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
        rw [← Category.assoc, hnatγ]
    _ = R.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β := by
        rw [Category.assoc, ← hβ, CategoryTheory.Functor.map_comp, Category.assoc,
          IsIso.hom_inv_id, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

universe u d d'

variable {X : RingedSpace.{u, u}}

-- The additivity of the equivalence `AlgebraicGeometry.RingedSpace.overToRestricted` between
-- modules on the slice site `Over U` and modules on the restricted ringed space is the theorem
-- `AlgebraicGeometry.RingedSpace.overToRestricted_additive`, which carries only a
-- `local instance` attribute, so it is registered globally here.
attribute [instance] overToRestricted_additive

/-- An equivalence preserves finite limits. -/
public instance overToRestricted_preservesFiniteLimits (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteLimits (overToRestricted X U) :=
  inferInstanceAs (PreservesFiniteLimits
    (U.sheafOfModulesEquivOver (structureSheafOfRings X)).functor)

/-- An equivalence preserves finite colimits. -/
public instance overToRestricted_preservesFiniteColimits (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteColimits (overToRestricted X U) :=
  inferInstanceAs (PreservesFiniteColimits
    (U.sheafOfModulesEquivOver (structureSheafOfRings X)).functor)

-- The statements below mention `CategoryTheory.Functor.mapDerivedCategory` of a restriction to
-- an open subspace, so they need both halves of the exactness of restriction as instances rather
-- than as plain theorems.
attribute [instance] restrictModules_preservesFiniteLimits
attribute [instance] restrictModules_preservesFiniteColimits

/-- **Stacks 08C8 in the `restrictModules` idiom.** Let `α : ℰ ⟶ ℱ` be a morphism of complexes of
`𝒪_X`-modules with `ℰ` strictly perfect and `ℰ^j = 0` for `j < a`, and let `f : 𝒢 ⟶ ℱ` be an
isomorphism on cohomology above `a` and an epimorphism on cohomology in degree `a`. Then every
point of `X` has an open neighbourhood `U` carrying `β : ℰ|_U ⟶ 𝒢|_U`, with the restriction taken
to the ringed space `X.restrict U.isOpenEmbedding`, such that `β ≫ f|_U` is homotopic to `α|_U`.

This is `AlgebraicGeometry.RingedSpace.exists_local_lift_homotopy` transported along
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`: the slice-idiom lift is pushed
through the equivalence and conjugated by the induced isomorphism of the functors on complexes,
and the homotopy is carried along because the equivalence is additive. -/
public theorem exists_local_lift_homotopy_restrictModules
    {E F G : CochainComplex (OXMod.{u, u} X) ℤ} (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : IsStrictlyPerfect E) (hEa : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
          ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj G,
        Nonempty (Homotopy
          (β ≫ ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          (((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  intro x
  obtain ⟨U, hx, hlift⟩ := exists_local_lift_homotopy α f a hE hEa hf_gt hf_a x
  exact ⟨U, hx, CochainComplex.exists_homotopy_lift_of_comp_natIso
    (SheafOfModules.overFunctor (structureSheafOfRings X) U) (overToRestricted X U)
    (restrictModules X U) (restrictModulesIsoOverComp X U) α f hlift⟩

/-- A quasi-isomorphism is an isomorphism on homology in every degree and, in particular, an
epimorphism on homology in any given degree `a`. -/
private theorem isIso_homologyMap_and_epi_of_quasiIso {G F : CochainComplex (OXMod.{u, u} X) ℤ}
    (f : G ⟶ F) (hf : QuasiIso f) (a : ℤ) :
    (∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j)) ∧
      Epi (HomologicalComplex.homologyMap f a) := by
  have h : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap f j) :=
    fun j => (quasiIsoAt_iff_isIso_homologyMap f j).1 (hf.quasiIsoAt j)
  exact ⟨fun j _ => h j, have := h a; inferInstance⟩

/-- **Stacks 08C9, part (2).** Let `α : ℰ ⟶ ℱ` be a morphism of complexes of `𝒪_X`-modules with
`ℰ` strictly perfect whose image in the derived category of `X` is zero. Then every point of `X`
has an open neighbourhood over which `α` is homotopic to zero.

The image of `α` in the derived category vanishes, so its image in the homotopy category is
killed by a quasi-isomorphism `t : 𝒵 ⟶ ℰ`; that is, `t ≫ α` is null-homotopic. Stacks 08C8,
applied to the identity of `ℰ` and to `t`, produces over some open neighbourhood `U` a map
`β : ℰ|_U ⟶ 𝒵|_U` with `β ≫ t|_U` homotopic to the identity, and
`CochainComplex.nonempty_homotopy_zero_of_lift_homotopy_id` concludes. -/
@[stacks 08C9 "local_null_homotopy", sga "6 I 4.1" "special case"]
public theorem exists_local_homotopy_zero_of_derived_eq_zero
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] {E F : CochainComplex (OXMod.{u, u} X) ℤ}
    (α : E ⟶ F) (hE : IsStrictlyPerfect E) (hα : DerivedCategory.Q.map α = 0) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (Homotopy
        (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) 0) := by
  intro x
  obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hE
  have hQh : DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (OXMod.{u, u} X) (ComplexShape.up ℤ)).map α) = 0 := by
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso (OXMod.{u, u} X)).hom.app F)).1
    simpa only [Functor.comp_map, hα, comp_zero, zero_comp] using
      (DerivedCategory.quotientCompQhIso (OXMod.{u, u} X)).hom.naturality α
  obtain ⟨Zbar, sbar, hsbar, hcomp⟩ :=
    (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
      (HomotopyCategory.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient (OXMod.{u, u} X) (ComplexShape.up ℤ)).map α) 0).1
      (by simpa only [Functor.map_zero] using hQh)
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Zbar
  obtain ⟨t, rfl⟩ :=
    (HomotopyCategory.quotient (OXMod.{u, u} X) (ComplexShape.up ℤ)).map_surjective sbar
  have ht : QuasiIso t := (HomotopyCategory.quotient_map_mem_quasiIso_iff t).1 hsbar
  rw [comp_zero, ← Functor.map_comp] at hcomp
  have hnull : Nonempty (Homotopy (t ≫ α) 0) :=
    (HomotopyCategory.quotient_map_eq_zero_iff _).1 (by simpa using hcomp)
  obtain ⟨U, hxU, β, h⟩ := exists_local_lift_homotopy (𝟙 E) t a hE ha
    (isIso_homologyMap_and_epi_of_quasiIso t ht a).1
    (isIso_homologyMap_and_epi_of_quasiIso t ht a).2 x
  exact ⟨U, hxU, CochainComplex.nonempty_homotopy_zero_of_lift_homotopy_id
    (SheafOfModules.overFunctor (structureSheafOfRings X) U) α t β h hnull⟩

/-- The geometric half of Stacks 08C9 part (1), stated without the derived functor induced by
restriction so that it can be proved separately: a morphism `α` of the derived category of `X`
out of a strictly perfect complex is written as a left fraction `Q(γ) ≫ Q(f)⁻¹`, and `γ` is
lifted through `f` up to homotopy over an open neighbourhood of the given point.

The left fraction is `DerivedCategory.left_fac` and the lift is Stacks 08C8 in the
`restrictModules` idiom. -/
public theorem exists_local_lift_of_left_fac [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {E F : CochainComplex (OXMod.{u, u} X) ℤ} (hE : IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (x : X.carrier) :
    ∃ (G : CochainComplex (OXMod.{u, u} X) ℤ) (γ : E ⟶ G) (f : F ⟶ G)
      (_ : IsIso (DerivedCategory.Q.map f)),
      α = DerivedCategory.Q.map γ ≫ CategoryTheory.inv (DerivedCategory.Q.map f) ∧
        ∃ U : Opens X.carrier, x ∈ U ∧
          ∃ β : ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
              ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
            Nonempty (Homotopy
              (β ≫ ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
              (((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).map γ)) := by
  obtain ⟨G, γ, f, hf, hαfac⟩ := DerivedCategory.left_fac α
  obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hE
  have hfq : QuasiIso f :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := OXMod.{u, u} X) f).mp hf
  exact ⟨G, γ, f, hf, hαfac, exists_local_lift_homotopy_restrictModules γ f a hE ha
    (isIso_homologyMap_and_epi_of_quasiIso f hfq a).1
    (isIso_homologyMap_and_epi_of_quasiIso f hfq a).2 x⟩

/-- Stacks 08C9 part (1) with the exactness of restriction supplied by the ambient instances
rather than bundled into the statement; see
`AlgebraicGeometry.RingedSpace.exists_local_complex_map`.

`AlgebraicGeometry.RingedSpace.exists_local_lift_of_left_fac` provides the left fraction and the
local lift, and `CategoryTheory.Functor.mapDerivedCategory_map_eq_of_lift` turns the lift into
the required identity. -/
public theorem exists_local_complex_map_of_instances [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    {E F : CochainComplex (OXMod.{u, u} X) ℤ} (hE : IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : ((restrictModules.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
          ((restrictModules.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
        (restrictModules.{u, u} X U).mapDerivedCategory.map α ≫
            (restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app F =
          (restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app E ≫
            DerivedCategory.Q.map β := by
  obtain ⟨G, γ, f, hf, hαfac, U, hx, β, h⟩ := exists_local_lift_of_left_fac hE α x
  exact ⟨U, hx, β, Functor.mapDerivedCategory_map_eq_of_lift
    (restrictModules.{u, u} X U) α γ f hf hαfac β h⟩

/-- **Stacks 08C9, part (1).** Let `ℰ`, `ℱ` be complexes of `𝒪_X`-modules with `ℰ` strictly
perfect and let `α : ℰ ⟶ ℱ` be a morphism in the derived category of `X`. Then every point of `X`
has an open neighbourhood `U` over which `α` is induced by a morphism of complexes
`β : ℰ|_U ⟶ ℱ|_U`, the comparison being made through the canonical isomorphism
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the exact functor `restrictModules X U`.

The exactness of restriction, which is what makes that comparison available, is part of the
assertion; the witnesses are the instances
`AlgebraicGeometry.RingedSpace.restrictModules_additive`,
`AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits` and
`AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits`, and the content is
`AlgebraicGeometry.RingedSpace.exists_local_complex_map_of_instances`. -/
@[stacks 08C9 "local_representation"]
public theorem exists_local_complex_map [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    {E F : CochainComplex (OXMod.{u, u} X) ℤ} (hE : IsStrictlyPerfect E)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (hadd : (restrictModules.{u, u} X U).Additive)
        (hlim : PreservesFiniteLimits (restrictModules.{u, u} X U))
        (hcolim : PreservesFiniteColimits (restrictModules.{u, u} X U)),
        letI := hadd
        letI := hlim
        letI := hcolim
        ∃ β : ((restrictModules.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
            ((restrictModules.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
          (restrictModules.{u, u} X U).mapDerivedCategory.map α ≫
              (restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app F =
            (restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app E ≫
              DerivedCategory.Q.map β :=
  fun x => (exists_local_complex_map_of_instances hE α x).imp fun _ h =>
    ⟨h.1, inferInstance, inferInstance, inferInstance, h.2⟩

end AlgebraicGeometry.RingedSpace

end
