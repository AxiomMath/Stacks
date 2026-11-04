module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.Topology.Sheaves.Modules.Generators.CoherentMonoNeighbourhood
public import StacksCore.Tactic.StacksAttribute

/-!
# Local surjectivity and local vanishing for sheaves of modules of finite type

Let `R` be a sheaf of rings on a topological space `X` and let `φ : G ⟶ F` be a morphism of
`R`-modules with `F` of finite type. If `φ` is surjective on the stalk at a point `x`, then
its restriction to some open neighbourhood of `x` is an epimorphism; taking `φ = 0` turns this
into the statement that a module of finite type whose stalk at `x` vanishes already vanishes
on a neighbourhood of `x`.

## Main results

* `AlgebraicGeometry.exists_epi_over_of_stalk_surjective`: surjectivity on one stalk gives an
  epimorphism after restriction to a neighbourhood.
* `AlgebraicGeometry.exists_isZero_over_of_stalk_isZero`: a vanishing stalk gives vanishing on
  a neighbourhood.
* `AlgebraicGeometry.exists_isIso_over_of_stalk_isIso`: bijectivity on one stalk, for a morphism
  from a finite-type module to a coherent module, gives an isomorphism after restriction to a
  neighbourhood.

## Implementation notes

Restriction to an open `U` is `SheafOfModules.over` on objects and `SheafOfModules.Hom.over`
on morphisms, so "epimorphism after restriction" is `Epi (φ.over U)` with no further choices.
Surjectivity on the stalks over a neighbourhood is upgraded to an epimorphism of restricted
modules through the characterisation of epimorphisms of sheaves of modules as the locally
surjective morphisms: a sieve of the over-category of an open `W` is covering exactly when its
image sieve on `W` is, so the neighbourhood-restricted local surjectivity supplied by Tag 01B8
is exactly local surjectivity for the topology induced on `Over W`.

A sheaf of rings on a bare topological space is turned into a ringed space by equipping `X`
with the constant sheaf of rings on the one-element ring; the structure sheaf plays no part in
either statement, so this loses nothing.

The isomorphism statement intersects two neighbourhoods, one on which the morphism is injective
and one on which it is locally surjective, and uses that both conditions descend to a smaller
open: injectivity because being a monomorphism of modules on a slice site is injectivity on
sections, which is a reindexing, and local surjectivity because `LocallySurjOn` only constrains
the points of its open. A monomorphism which is also an epimorphism of modules on a site is an
isomorphism, the category being abelian.

## References

* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
* [Stacks Project, Tag 01B8](https://stacks.math.columbia.edu/tag/01B8)
* [Stacks Project, Tag 01C0](https://stacks.math.columbia.edu/tag/01C0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A topological space made into a ringed space by the constant sheaf of rings on the
one-element ring. It carries no information beyond the space itself, and serves only to let
results stated for a ringed space be applied to a sheaf of rings on a bare space. -/
private def auxiliaryRingedSpace (X : TopCat.{u}) : RingedSpace.{u + 1, u} where
  carrier := X
  presheaf := (Functor.const (Opens X)ᵒᵖ).obj (CommRingCat.of PUnit.{u + 2})
  IsSheaf := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι U sf _
    refine ⟨PUnit.unit.{u + 2}, fun i => ?_, fun s _ => ?_⟩ <;>
      · dsimp only [Functor.const_obj_obj] at *
        exact Subsingleton.elim _ _

/-- A morphism of modules on a ringed space which is locally surjective over an open `W`
becomes an epimorphism after restriction to `W`. For a section of the target over an open of
`Over W`, the opens on which it lifts cover that open, which is local surjectivity for the
topology induced on `Over W`. -/
private lemma epi_over_of_locallySurjOn {Y : RingedSpace.{u + 1, u}}
    {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {F G : SheafOfModules.{u} R} (φ : G ⟶ F) (W : Opens Y)
    (h : Stacks.SheafOfModules.LocallySurjective.LocallySurjOn (X := Y) φ W) :
    Epi (φ.over W) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {V} s => ?_⟩
  intro y hy
  obtain ⟨V', hV'V, ⟨t, ht⟩, hyV'⟩ := h V.left s y hy (V.hom.le hy)
  exact ⟨V', homOfLE hV'V, (Sieve.overEquiv_iff _ _).2 ⟨t, ht⟩, hyV'⟩

variable {X : TopCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A morphism with finite-type target which is surjective on one stalk is an epimorphism after
restriction to every open inside some neighbourhood of that point. -/
private lemma exists_nbhd_forall_le_epi_over {F G : SheafOfModules.{u} R}
    [F.IsFiniteType] (φ : G ⟶ F) (x : X)
    (hx : Function.Surjective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    ∃ V : Opens X, x ∈ V ∧ ∀ W ≤ V, Epi (φ.over W) := by
  obtain ⟨V, hxV, hV⟩ := Stacks.SheafOfModules.LocallySurjective.exists_nbhd_locallySurjOn
    (X := auxiliaryRingedSpace X) φ (inferInstance : SheafOfModules.IsFiniteType.{u, u, u} F) x hx
  exact ⟨V, hxV, fun W hW => epi_over_of_locallySurjOn (Y := auxiliaryRingedSpace X) φ W
    fun U t y hyU hyW => hV U t y hyU (hW hyW)⟩

/-- **Stacks Project, Tag 01Y3.** A morphism with finite-type target which is surjective on one
stalk is an epimorphism after restriction to a neighbourhood of that point. -/
@[stacks 01Y3 "part (3)"]
public theorem exists_epi_over_of_stalk_surjective {F G : SheafOfModules.{u} R}
    [F.IsFiniteType] (φ : G ⟶ F) (x : X)
    (hx : Function.Surjective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    ∃ U : Opens X, x ∈ U ∧ Epi (φ.over U) := by
  obtain ⟨W, hxW, hW⟩ := exists_nbhd_forall_le_epi_over φ x hx
  exact ⟨W, hxW, hW W le_rfl⟩

/-- **Stacks Project, Tag 01Y3.** A finite-type sheaf whose stalk vanishes at a point vanishes
on a neighbourhood of that point. -/
@[stacks 01Y3 "part (1)", stacks 01B9, ega "0 5.2.2" "support closed"]
public theorem exists_isZero_over_of_stalk_isZero (F : SheafOfModules.{u} R)
    [F.IsFiniteType] (x : X)
    (hx : IsZero (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    ∃ U : Opens X, x ∈ U ∧ IsZero (F.over U) := by
  let φ : F ⟶ F := 0
  have hsurj : Function.Surjective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val))) := by
    intro z
    have : Subsingleton ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
        ((PresheafOfModules.toPresheaf R.obj).obj F.val)) :=
      AddCommGrpCat.subsingleton_of_isZero hx
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨U, hxU, hU⟩ := exists_epi_over_of_stalk_surjective φ x hsurj
  refine ⟨U, hxU, (IsZero.iff_id_eq_zero _).2 <| (cancel_epi (φ.over U)).1 ?_⟩
  change (SheafOfModules.overFunctor R U).map (0 : F ⟶ F) = 0
  rfl

/-- A morphism which is a monomorphism after restriction to an open is one after restriction to
any smaller open: on sections both are the same family of maps, reindexed. -/
@[sga "4 IV 8.5.1" "partial"]
private lemma mono_over_of_le {F G : SheafOfModules.{u} R} (φ : G ⟶ F) {U W : Opens X}
    (h : W ≤ U) (hU : Mono (φ.over U)) : Mono (φ.over W) := by
  refine (SheafOfModules.forget (R.over W)).mono_of_mono_map (f := φ.over W) ?_
  refine PresheafOfModules.mono_of_injective (fun {V} => ?_)
  exact PresheafOfModules.injective_of_mono
    ((SheafOfModules.forget (R.over U)).map (φ.over U))
    (op (Over.mk (V.unop.hom ≫ homOfLE h)))

/-- **Stacks Project, Tag 01Y3.** A morphism from a module of finite type to a coherent module
which is bijective on the stalk at a point is an isomorphism after restriction to a
neighbourhood of that point. -/
@[stacks 01Y3 "part (4)"]
public theorem exists_isIso_over_of_stalk_isIso {F G : SheafOfModules.{u} R}
    [F.IsCoherent] [G.IsFiniteType] (φ : G ⟶ F) (x : X)
    (hx : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf R.obj).map φ.val))) :
    ∃ U : Opens X, x ∈ U ∧ IsIso (φ.over U) := by
  have hbij : Function.Bijective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val))) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hx
  obtain ⟨U, hxU, hmono⟩ :=
    Stacks.SheafOfModules.exists_isMono_over_of_stalk_injective φ x hbij.1
  have := SheafOfModules.IsCoherent.isFiniteType (M := F)
  obtain ⟨V, hxV, hV⟩ := exists_nbhd_forall_le_epi_over φ x hbij.2
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
  have := mono_over_of_le φ (inf_le_left : U ⊓ V ≤ U) hmono
  have := hV _ (inf_le_right : U ⊓ V ≤ V)
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry
