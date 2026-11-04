module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerArbitraryIndex

/-!
# A free sheaf of modules is the sheafification of the free presheaf of modules

Let `(C, J)` be a site, let `R` be a sheaf of rings on it and let `L` be a type in the module
universe.  Mathlib's `SheafOfModules.free L` is the coproduct, taken in *sheaves* of
`R`-modules, of `L` copies of the unit module, so its sections over an object are in general
strictly larger than the finitely supported families `L →₀ R(X)`: a section is only *locally* a
finite sum of the tautological sections.  The free *presheaf* of modules
`Stacks.PresheafOfModules.freeConst L` has exactly those families as its sections.

This file writes down the canonical morphism of presheaves of modules between the two and proves
it **locally bijective**: `SheafOfModules.free L` is the sheafification of
`Stacks.PresheafOfModules.freeConst L`, with the canonical morphism as the sheafification unit.
The consequence drawn here is the criterion the comparison maps with a free source are checked
by: a morphism out of a free sheaf of modules prescribed by a family of global sections of the
target is an isomorphism as soon as the corresponding morphism out of the free *presheaf* is
locally bijective, a condition which speaks only of finitely supported families and so is
checkable from a geometric computation over the objects where the target is understood.

## Main definitions

* `Stacks.PresheafOfModules.freeConstToFree`: **the canonical morphism
  `freeConst L ⟶ (SheafOfModules.free L).val`**, carrying the `l`-th standard basis vector of the
  sections to the `l`-th tautological section of the free sheaf of modules.
* `Stacks.SheafOfModules.sheafifyFreeConstToFree`: its adjoint transpose, from the
  sheafification of `freeConst L` to `SheafOfModules.free L`.

## Main results

* `Stacks.PresheafOfModules.bijective_freeConstDesc`: a morphism out of `freeConst L` is the
  same thing as an `L`-indexed family of global sections of the target.  This is the presheaf
  analogue of `SheafOfModules.freeHomEquiv`.
* `Stacks.SheafOfModules.isIso_sheafifyFreeConstToFree`: **the sheafification of the free
  presheaf of modules on `L` is the free sheaf of modules on `L`**, by the canonical morphism.
* `Stacks.PresheafOfModules.isLocallySurjective_freeConstToFree` and
  `Stacks.PresheafOfModules.isLocallyInjective_freeConstToFree`: **a section of a free sheaf of
  modules is locally a finite sum of tautological sections, uniquely so.**
* `Stacks.SheafOfModules.isIso_sheafificationHomEquiv_symm_of_isLocallyBijective`: **the
  criterion, in general.**  A locally bijective morphism from a presheaf of modules to a sheaf of
  modules exhibits the target as the sheafification of the source: its adjoint transpose is an
  isomorphism.
* `Stacks.SheafOfModules.isIso_freeHomEquiv_symm_of_isLocallyBijective`: **the criterion at a
  free source.**  The morphism `free L ⟶ N` prescribed by a family `σ` of global sections of `N`
  is an isomorphism as soon as `Stacks.PresheafOfModules.freeConstDesc σ` is locally injective
  and locally surjective on underlying abelian presheaves.

* `Stacks.SheafOfModules.epi_sheafificationHomEquiv_symm_forget_map` and
  `Stacks.SheafOfModules.sheafificationHomEquiv_symm_comp`: the two properties of the transpose
  of the sheafification adjunction which a comparison morphism out of a sheaf *cokernel* is
  checked by, the sections of such a cokernel being a sheafification just as the sections of a
  free sheaf of modules are.

## Implementation notes

The criterion is proved for an arbitrary presheaf of modules in place of `freeConst L` — that
is `Stacks.SheafOfModules.isIso_sheafificationHomEquiv_symm_of_isLocallyBijective` — and the
free case is read off it, because the same criterion is what the second comparison of Tag 03OJ
needs, at the presheaf cokernel rather than at the free presheaf.  The free case carries, on top
of the general one, only the identification of the sheafification of `freeConst L` with
`SheafOfModules.free L`.

The route is the sheafification adjunction for presheaves of modules,
`PresheafOfModules.sheafificationAdjunction`, and the fact that both `freeConst L` and
`SheafOfModules.free L` corepresent the functor "`L`-indexed families of global sections".  That
`Stacks.SheafOfModules.sheafifyFreeConstToFree` is an isomorphism is therefore
`CategoryTheory.isIso_iff_coyoneda_map_bijective` applied to a composite of three bijections —
`SheafOfModules.freeHomEquiv`, `Stacks.PresheafOfModules.bijective_freeConstDesc` and the
adjunction — and no coproduct comparison and no section of a sheafification is computed.

`Stacks.SheafOfModules.sheafifyFreeConstIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerArbitraryIndex` already identifies those
two objects, and is **not** what is used here, for two reasons.  It is stated for a sheaf of
*commutative* rings, through `Stacks.CategoryTheory.Sites.toRingCat`, because the file it lives
in is about symmetric and exterior powers; and, being assembled from
`CategoryTheory.Limits.PreservesCoproduct.iso` and
`Stacks.SheafOfModules.sheafifyUnitPresheafIso`, it carries no formula on the standard basis of
the sections of `freeConst L`.  Both of those are needed below: the base is a sheaf of rings
which this repository does not present as commutative, and the whole point of the criterion is
the formula `Stacks.PresheafOfModules.freeConstDesc_app_basis`, which is what lets the local
condition be checked against a geometric computation.  The two isomorphisms agree wherever both
are defined, both being inverses of comparison maps out of a coproduct, but nothing below needs
that and it is not proved.

Local bijectivity of the sheafification unit is **not** Mathlib's
`CategoryTheory.Presheaf.isLocallySurjective_toSheafify'`, whose `ConcreteCategory.{max u v}`
hypothesis pins the sections to the universe of the site and fails for a site with objects one
universe above its morphisms; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse`.  It is instead read off
`CategoryTheory.GrothendieckTopology.W_toSheafify` through
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, which is a hypothesis here and
carries no universe side condition; that is also how the composite with an isomorphism is
handled, `CategoryTheory.GrothendieckTopology.W` being closed under composition while the
instance for a composite of locally surjective morphisms did not fire at this shape.

No `@[stacks]` attribute is claimed.  Tag 0935 is the statement that the sections of a coproduct
of sheaves of modules over a quasi-compact object are the direct sum of the sections, which is
`Stacks.Sites.bijective_freeSectionsMap`; what is here is the local statement, true over every
object, which the source does not isolate.

## References

* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 00WI](https://stacks.math.columbia.edu/tag/00WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u₁ u

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A morphism out of the free presheaf of modules on `L` is an `L`-indexed family of global
sections of the target.**  This is `Stacks.PresheafOfModules.freeConstDesc`, read as a bijection;
it is the presheaf analogue of `SheafOfModules.freeHomEquiv`, and like it it is injective because
the tautological sections are recovered by `Stacks.PresheafOfModules.sectionsMap_freeConstDesc`
and surjective because a morphism out of `freeConst L` is determined by its values on the
standard basis. -/
public theorem bijective_freeConstDesc (L : Type u) (M : _root_.PresheafOfModules.{u} R.obj) :
    Function.Bijective (freeConstDesc (R := R.obj) (γ := L) (M := M)) := by
  constructor
  · intro s t h
    funext l
    rw [← sectionsMap_freeConstDesc s l, ← sectionsMap_freeConstDesc t l, h]
  · intro f
    refine ⟨fun l => _root_.PresheafOfModules.sectionsMap f (freeConstSection l), ?_⟩
    refine freeConst_hom_ext fun V l => ?_
    rw [freeConstDesc_app_basis]
    rfl

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The canonical morphism from the free presheaf of modules on `L` to the free sheaf of
modules on `L`**, prescribed by the tautological global sections `SheafOfModules.freeSection`.

Over an object of the site it is the comparison map `L →₀ R(X) ⟶ (free L)(X)`, which is bijective
over a quasi-compact object (`Stacks.Sites.bijective_freeSectionsMap`) but only locally bijective
in general (`Stacks.PresheafOfModules.isLocallySurjective_freeConstToFree`). -/
public noncomputable def freeConstToFree (L : Type u) :
    freeConst (R := R.obj) L ⟶ (_root_.SheafOfModules.free (R := R) L).val :=
  freeConstDesc fun l => _root_.SheafOfModules.freeSection (R := R) l

/-- Composing the canonical morphism with a morphism out of the free sheaf of modules gives the
morphism prescribed by the family of global sections which `SheafOfModules.freeHomEquiv`
attaches to it. -/
public theorem freeConstToFree_comp {L : Type u} {N : _root_.SheafOfModules.{u} R}
    (φ : _root_.SheafOfModules.free (R := R) L ⟶ N) :
    freeConstToFree L ≫ φ.val = freeConstDesc (_root_.SheafOfModules.freeHomEquiv N φ) := by
  rw [freeConstToFree, freeConstDesc_comp]
  rfl

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

open Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The adjoint transpose of `Stacks.PresheafOfModules.freeConstToFree`: a morphism from the
sheafification of the free presheaf of modules on `L` to the free sheaf of modules on `L`.  It is
an isomorphism, by `Stacks.SheafOfModules.isIso_sheafifyFreeConstToFree`. -/
public noncomputable def sheafifyFreeConstToFree (L : Type u) :
    (_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj (freeConst (R := R.obj) L) ⟶
      _root_.SheafOfModules.free (R := R) L :=
  (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm (freeConstToFree L)

/-- The transpose of `Stacks.SheafOfModules.sheafifyFreeConstToFree` is the canonical morphism
out of the free presheaf of modules. -/
public theorem sheafificationHomEquiv_sheafifyFreeConstToFree (L : Type u) :
    (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj))
        (sheafifyFreeConstToFree (R := R) L) = freeConstToFree L :=
  Equiv.apply_symm_apply _ _

/-- Precomposition with `Stacks.SheafOfModules.sheafifyFreeConstToFree` carries a morphism out of
the free sheaf of modules to the transpose of the morphism out of the free presheaf of modules
prescribed by the same family of global sections. -/
public theorem sheafifyFreeConstToFree_comp (L : Type u) (N : _root_.SheafOfModules.{u} R)
    (φ : _root_.SheafOfModules.free (R := R) L ⟶ N) :
    sheafifyFreeConstToFree L ≫ φ =
      (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        (freeConstDesc (_root_.SheafOfModules.freeHomEquiv N φ)) := by
  refine (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective ?_
  rw [Equiv.apply_symm_apply,
    ← _root_.PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    Adjunction.homEquiv_naturality_right,
    _root_.PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    sheafificationHomEquiv_sheafifyFreeConstToFree]
  exact freeConstToFree_comp φ

/-- **The sheafification of the free presheaf of modules on `L` is the free sheaf of modules on
`L`.**  Both objects corepresent the functor sending a sheaf of modules to the `L`-indexed
families of its global sections — the first by the sheafification adjunction followed by
`Stacks.PresheafOfModules.bijective_freeConstDesc`, the second by
`SheafOfModules.freeHomEquiv` — and the canonical morphism between them induces the identity of
that functor. -/
public instance isIso_sheafifyFreeConstToFree (L : Type u) :
    IsIso (sheafifyFreeConstToFree (R := R) L) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro N
  have h : (fun φ : _root_.SheafOfModules.free (R := R) L ⟶ N =>
        sheafifyFreeConstToFree L ≫ φ) =
      (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ∘ freeConstDesc ∘
        (_root_.SheafOfModules.freeHomEquiv N) :=
    funext fun φ => sheafifyFreeConstToFree_comp L N φ
  rw [h]
  exact (((_root_.PresheafOfModules.sheafificationHomEquiv
      (𝟙 R.obj)).symm.bijective).comp (bijective_freeConstDesc L _)).comp
    (_root_.SheafOfModules.freeHomEquiv N).bijective

end Stacks.SheafOfModules

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheafification unit of a presheaf of modules, **ascribed** at the spelling
`(toPresheaf R.obj).obj ((sheafification (𝟙 R.obj)).obj A).val` of its target rather
than at `sheafify J A.presheaf`.  The two are equal by `rfl` and not syntactically
equal, so a composite written at the second spelling is type-correct only up to defeq and
`Functor.map_comp` refuses it; the crossing is done here, once, by a `def` with an ascribed
type. -/
public noncomputable def sheafificationUnit (A : _root_.PresheafOfModules.{u} R.obj) :
    (_root_.PresheafOfModules.toPresheaf R.obj).obj A ⟶
      (_root_.PresheafOfModules.toPresheaf R.obj).obj
        ((_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj A).val :=
  CategoryTheory.toSheafify J A.presheaf

public theorem w_sheafificationUnit (A : _root_.PresheafOfModules.{u} R.obj) :
    J.W (sheafificationUnit (R := R) A) :=
  J.W_toSheafify _

/-- **A morphism out of a sheafification is the sheafification unit followed by its
transpose.**  This is `PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def` with the
target of the unit ascribed by `Stacks.PresheafOfModules.sheafificationUnit`. -/
public theorem sheafificationUnit_comp {A : _root_.PresheafOfModules.{u} R.obj}
    {N : _root_.SheafOfModules.{u} R}
    (φ : (_root_.PresheafOfModules.sheafification (𝟙 R.obj)).obj A ⟶ N) :
    sheafificationUnit (R := R) A ≫
        (_root_.PresheafOfModules.toPresheaf R.obj).map φ.val =
      (_root_.PresheafOfModules.toPresheaf R.obj).map
        (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) φ) :=
  (_root_.PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def (𝟙 R.obj) φ).symm

/-- The sheafification unit followed by a transpose is the morphism that was transposed. -/
private theorem sheafificationUnit_comp_symm {A : _root_.PresheafOfModules.{u} R.obj}
    {N : _root_.SheafOfModules.{u} R}
    (ψ : A ⟶ (_root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
      ((_root_.SheafOfModules.forget R).obj N)) :
    sheafificationUnit (R := R) A ≫
        (_root_.PresheafOfModules.toPresheaf R.obj).map
          ((_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ψ).val =
      (_root_.PresheafOfModules.toPresheaf R.obj).map ψ :=
  (sheafificationUnit_comp _).trans
    (congrArg ((_root_.PresheafOfModules.toPresheaf R.obj).map) (Equiv.apply_symm_apply _ _))

/-- The canonical morphism out of the free presheaf of modules is the sheafification unit of that
presheaf followed by `Stacks.SheafOfModules.sheafifyFreeConstToFree`.  This is
`Stacks.PresheafOfModules.sheafificationUnit_comp` at the transpose. -/
public theorem toSheafify_comp_sheafifyFreeConstToFree (L : Type u) :
    sheafificationUnit (R := R) (freeConst (R := R.obj) L) ≫
        (_root_.PresheafOfModules.toPresheaf R.obj).map
          (Stacks.SheafOfModules.sheafifyFreeConstToFree (R := R) L).val =
      (_root_.PresheafOfModules.toPresheaf R.obj).map (freeConstToFree (R := R) L) :=
  sheafificationUnit_comp_symm (freeConstToFree (R := R) L)

/-- The canonical morphism out of the free presheaf of modules becomes an isomorphism after
sheafification: it is the sheafification unit followed by an isomorphism. -/
public theorem w_freeConstToFree (L : Type u) :
    J.W ((_root_.PresheafOfModules.toPresheaf R.obj).map (freeConstToFree (R := R) L)) := by
  have : IsIso (Stacks.SheafOfModules.sheafifyFreeConstToFree (R := R) L).val :=
    inferInstanceAs (IsIso ((_root_.SheafOfModules.forget R).map
      (Stacks.SheafOfModules.sheafifyFreeConstToFree (R := R) L)))
  rw [← toSheafify_comp_sheafifyFreeConstToFree]
  refine (GrothendieckTopology.W_iff J _).2 ?_
  rw [Functor.map_comp]
  have : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (sheafificationUnit (R := R) (freeConst (R := R.obj) L))) :=
    (GrothendieckTopology.W_iff J _).1 (w_sheafificationUnit _)
  infer_instance

/-- **A section of a free sheaf of modules is locally a finite sum of tautological sections.**
The canonical morphism from the free presheaf of modules is locally surjective. -/
public instance isLocallySurjective_freeConstToFree (L : Type u) :
    Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf R.obj).map (freeConstToFree (R := R) L)) :=
  (w_freeConstToFree L).isLocallySurjective

/-- **A finitely supported family of sections whose sum of tautological multiples vanishes
vanishes locally.**  The canonical morphism from the free presheaf of modules is locally
injective. -/
public instance isLocallyInjective_freeConstToFree (L : Type u) :
    Presheaf.IsLocallyInjective J
      ((_root_.PresheafOfModules.toPresheaf R.obj).map (freeConstToFree (R := R) L)) :=
  (w_freeConstToFree L).isLocallyInjective

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

open Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The transpose of the sheafification adjunction for presheaves of modules is
`PresheafOfModules.sheafificationHomEquiv`.  Mathlib records this for the forward direction only
(`PresheafOfModules.sheafificationAdjunction_homEquiv_apply`, which is `rfl`); the inverse
directions therefore agree as well, which is what lets the general naturality lemmas for an
adjunction be used on `PresheafOfModules.sheafificationHomEquiv`. -/
public theorem sheafificationHomEquiv_symm_eq {A : _root_.PresheafOfModules.{u} R.obj}
    {N : _root_.SheafOfModules.{u} R}
    (ψ : A ⟶ (_root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
      ((_root_.SheafOfModules.forget R).obj N)) :
    (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ψ =
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv A N).symm ψ := by
  refine (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective ?_
  rw [Equiv.apply_symm_apply,
    ← _root_.PresheafOfModules.sheafificationAdjunction_homEquiv_apply, Equiv.apply_symm_apply]

/-- The transpose of the underlying morphism of presheaves of modules of a morphism of sheaves of
modules is the counit of the sheafification adjunction followed by that morphism. -/
public theorem sheafificationHomEquiv_symm_forget_map {M N : _root_.SheafOfModules.{u} R}
    (k : M ⟶ N) :
    (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        ((_root_.SheafOfModules.forget R ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).map k) =
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M ≫ k := by
  rw [sheafificationHomEquiv_symm_eq, Adjunction.homEquiv_counit]
  exact (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.naturality k

/-- **The transpose of an epimorphism of sheaves of modules is an epimorphism.**  The counit of
the sheafification adjunction for presheaves of modules is an isomorphism, so the transpose of
the underlying morphism of presheaves of modules of `k` is `k` up to that isomorphism. -/
public theorem epi_sheafificationHomEquiv_symm_forget_map {M N : _root_.SheafOfModules.{u} R}
    (k : M ⟶ N) [Epi k] :
    Epi ((_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
      ((_root_.SheafOfModules.forget R ⋙
        _root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).map k)) := by
  rw [sheafificationHomEquiv_symm_forget_map]
  infer_instance

/-- The transpose of the sheafification adjunction is natural in the sheaf of modules. -/
public theorem sheafificationHomEquiv_symm_comp_right
    {A : _root_.PresheafOfModules.{u} R.obj} {M N : _root_.SheafOfModules.{u} R}
    (ψ : A ⟶ (_root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
      ((_root_.SheafOfModules.forget R).obj M)) (k : M ⟶ N) :
    (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        (ψ ≫ (_root_.SheafOfModules.forget R ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).map k) =
      (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ψ ≫ k := by
  rw [sheafificationHomEquiv_symm_eq, sheafificationHomEquiv_symm_eq,
    Adjunction.homEquiv_naturality_right_symm]

/-- The transpose of the sheafification adjunction is natural in the presheaf of modules. -/
public theorem sheafificationHomEquiv_symm_comp
    {A B : _root_.PresheafOfModules.{u} R.obj} {N : _root_.SheafOfModules.{u} R}
    (g : A ⟶ B)
    (ψ : B ⟶ (_root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
      ((_root_.SheafOfModules.forget R).obj N)) :
    (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm (g ≫ ψ) =
      (_root_.PresheafOfModules.sheafification (𝟙 R.obj)).map g ≫
        (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ψ := by
  rw [sheafificationHomEquiv_symm_eq, sheafificationHomEquiv_symm_eq,
    Adjunction.homEquiv_naturality_left_symm]

/-- **A locally bijective morphism out of a presheaf of modules into a sheaf of modules exhibits
the target as the sheafification of the source.**  If a morphism `ψ : A ⟶ N` from a presheaf of
modules to (the underlying presheaf of modules of) a sheaf of modules is locally injective and
locally surjective on underlying abelian presheaves, then its adjoint transpose
`(sheafification (𝟙 R.obj)).obj A ⟶ N` is an isomorphism.

This is the general form of the criterion by which the comparison morphisms whose source is only
*locally* the presheaf one can compute with are shown to be invertible: the transpose is the
sheafification unit of `A` followed by `ψ`, the unit is locally bijective by
`CategoryTheory.GrothendieckTopology.W_toSheafify`, and a locally bijective morphism of sheaves
is invertible.  `Stacks.SheafOfModules.isIso_freeHomEquiv_symm_of_isLocallyBijective` below is
the case `A = freeConst L`. -/
public theorem isIso_sheafificationHomEquiv_symm_of_isLocallyBijective
    {A : _root_.PresheafOfModules.{u} R.obj} {N : _root_.SheafOfModules.{u} R}
    (ψ : A ⟶ (_root_.PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
      ((_root_.SheafOfModules.forget R).obj N))
    (hinj : Presheaf.IsLocallyInjective J ((_root_.PresheafOfModules.toPresheaf R.obj).map ψ))
    (hsurj : Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf R.obj).map ψ)) :
    IsIso ((_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ψ) := by
  set φ := (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm ψ with hφ
  have hcomp := sheafificationUnit_comp_symm (R := R) ψ
  have := (w_sheafificationUnit (R := R) A).isLocallyInjective
  have := (w_sheafificationUnit (R := R) A).isLocallySurjective
  have h1 : Presheaf.IsLocallyInjective J
      ((_root_.PresheafOfModules.toPresheaf R.obj).map φ.val) :=
    (Presheaf.comp_isLocallyInjective_iff J _
      ((_root_.PresheafOfModules.toPresheaf R.obj).map φ.val)).1 (hcomp ▸ hinj)
  have h2 : Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf R.obj).map φ.val) :=
    (Presheaf.comp_isLocallySurjective_iff J _
      ((_root_.PresheafOfModules.toPresheaf R.obj).map φ.val)).1 (hcomp ▸ hsurj)
  have := (Sheaf.isLocallyBijective_iff_isIso ((_root_.SheafOfModules.toSheaf R).map φ)).1
    ⟨⟨h1.1⟩, ⟨h2.1⟩⟩
  exact isIso_of_reflects_iso φ (_root_.SheafOfModules.toSheaf R)

/-- **The criterion for a comparison morphism with a free source to be an isomorphism.**  Let
`N` be a sheaf of modules and `σ` an `L`-indexed family of global sections of `N`.  The morphism
`free L ⟶ N` prescribed by `σ` is an isomorphism as soon as the morphism of presheaves of
modules `Stacks.PresheafOfModules.freeConstDesc σ` out of the *free presheaf* of modules is
locally injective and locally surjective.

This is the form in which such a comparison is checked: the sections of `freeConst L` over an
object are the finitely supported families `L →₀ R(X)`, and
`Stacks.PresheafOfModules.freeConstDesc_app_basis` evaluates the morphism on the standard basis,
so the two local conditions are statements about finite sums of multiples of the `σ l` and are
checkable wherever the sections of `N` are understood.  Local bijectivity of
`Stacks.PresheafOfModules.freeConstToFree` is what removes the sheafification: the sections of
`free L` itself are not finitely supported families. -/
public theorem isIso_freeHomEquiv_symm_of_isLocallyBijective {L : Type u}
    {N : _root_.SheafOfModules.{u} R} (σ : L → N.sections)
    (hinj : Presheaf.IsLocallyInjective J
      ((_root_.PresheafOfModules.toPresheaf R.obj).map (freeConstDesc σ)))
    (hsurj : Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf R.obj).map (freeConstDesc σ))) :
    IsIso ((_root_.SheafOfModules.freeHomEquiv N).symm σ) := by
  have hiso := isIso_sheafificationHomEquiv_symm_of_isLocallyBijective
    (R := R) (freeConstDesc σ) hinj hsurj
  have hfac := sheafifyFreeConstToFree_comp (R := R) L N
    ((_root_.SheafOfModules.freeHomEquiv N).symm σ)
  rw [Equiv.apply_symm_apply] at hfac
  have : IsIso (sheafifyFreeConstToFree (R := R) L ≫
      (_root_.SheafOfModules.freeHomEquiv N).symm σ) := by rwa [hfac]
  exact IsIso.of_isIso_comp_left (sheafifyFreeConstToFree (R := R) L) _

end Stacks.SheafOfModules

end
