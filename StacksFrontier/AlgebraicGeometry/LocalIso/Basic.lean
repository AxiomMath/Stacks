module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Local injectivity and local isomorphy of morphisms of coherent modules

Let `R` be a sheaf of rings on a topological space and `φ : G ⟶ F` a morphism of `R`-modules
with `G` of finite type and `F` coherent. If `φ` is injective on the stalk at a point, its
restriction to some open neighbourhood of that point is a monomorphism; if it is bijective on
that stalk, the restriction is an isomorphism.

These are [Stacks, Tag 01C0] and part (4) of [Stacks, Tag 01Y3], deduced from the
*downward closed* form of the two neighbourhood statements.

## Main results

* The two neighbourhood statements in *downward closed* form:
  * `exists_mono_over_le_of_stalk_injective`: a neighbourhood `U` of `x` such that `φ.over W` is
    a monomorphism for **every** `W ≤ U`;
  * `exists_epi_over_le_of_stalk_surjective`: a neighbourhood `U` of `x` such that `φ.over W` is
    an epimorphism for **every** `W ≤ U`.
* `exists_forall_stalk_isZero_of_stalk_isZero`: part (1) of [Stacks, Tag 01Y3] read pointwise.
* `exists_isMono_over_of_stalk_injective`: [Stacks, Tag 01C0], i.e. part (2) of
  [Stacks, Tag 01Y3]; a second proof of
  `AlgebraicGeometry.exists_isMono_over_of_stalk_injective`.
* `exists_isIso_over_of_stalk_isIso`: part (4) of [Stacks, Tag 01Y3]; a second proof of
  `AlgebraicGeometry.exists_isIso_over_of_stalk_isIso`, whose statement it repeats verbatim.

## Implementation notes

**Why the downward-closed form.** Part (4) intersects the neighbourhood on which `φ` is injective
with the one on which it is surjective, and then needs both properties on the intersection. Neither
`Mono (φ.over U)` nor `Epi (φ.over U)` is visibly stable under shrinking `U`: restriction along
`W ≤ U` is a *pushforward* between over-sites, which preserves monomorphisms but not epimorphisms,
and transporting a property across `SheafOfModules.overMap` costs a naturality square each time.
Both halves of the construction are, however, produced from data that *is* downward closed —
pointwise vanishing of the stalks of `kernel φ` in the first case,
`Stacks.SheafOfModules.LocallySurjective.LocallySurjOn` in the second — so the neighbourhood
statements are proved in the downward-closed form directly and part (4) needs no transport at all.
`locallySurjOn_of_le` is that monotonicity for `LocallySurjOn`; it holds because the predicate
quantifies over points *of* its open.

**The auxiliary ringed space.** `Stacks01B8` is stated for a `RingedSpace`, whereas 01Y3 is stated
for a bare sheaf of rings on a space; `auxRingedSpace` passes between them, and
`epi_over_of_locallySurjOn` turns `LocallySurjOn` into `Epi`. Both restate the `private`
`AlgebraicGeometry.auxiliaryRingedSpace` and `AlgebraicGeometry.epi_over_of_locallySurjOn` of
`StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalSurjectivity`.

**Every step touching the auxiliary ringed space is confined to a lemma whose space is a
variable.** A morphism being zero, or a stalk functor preserving zero morphisms, is an instance
goal, and instance search does not unfold the auxiliary space's carrier: the goal is then stated
at `↑X` while the instance is registered at `↑↑Y.toPresheafedSpace`, and the error reads as a
missing `PreservesZeroMorphisms`. Keeping those steps inside `surjOnStalk_zero_of_isZero` and
`isZero_of_surjOnStalk_zero`, where the space is a bound variable, removes the mismatch.

The kernel-stalk route to injectivity is [Stacks, Tag 01AG]'s stalkwise exactness criterion
applied to `ShortComplex.kernelSequence φ`.

## References

* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
* [Stacks Project, Tag 01C0](https://stacks.math.columbia.edu/tag/01C0)
* [Stacks Project, Tag 01B8](https://stacks.math.columbia.edu/tag/01B8)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01Y3LocalIso

/-! ### An abelian-group lemma for the kernel sequence -/

/-- A short complex of abelian groups which is exact and has vanishing first term has injective
second map. -/
theorem injective_of_exact_of_isZero {T : ShortComplex AddCommGrpCat.{u}}
    (hT : T.Exact) (h1 : IsZero T.X₁) : Function.Injective T.g.hom := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨c, rfl⟩ := (ShortComplex.ab_exact_iff_ker_le_range).mp hT ha
  obtain rfl : c = 0 := (AddCommGrpCat.subsingleton_of_isZero h1).elim _ _
  exact map_zero _

/-! ### The passage from a sheaf of rings on a space to a ringed space -/

/-- A topological space made into a ringed space by the constant sheaf on the one-element ring. -/
private def auxRingedSpace (X : TopCat.{u}) : RingedSpace.{u + 1, u} where
  carrier := X
  presheaf := (Functor.const (Opens X)ᵒᵖ).obj (CommRingCat.of PUnit.{u + 2})
  IsSheaf := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι U sf _
    refine ⟨PUnit.unit.{u + 2}, fun i => ?_, fun s _ => ?_⟩ <;>
      · dsimp only [Functor.const_obj_obj] at *
        exact Subsingleton.elim _ _

/-! ### The zero endomorphism and vanishing stalks, with the space a variable -/

section RingedSpace

variable {Y : RingedSpace.{u + 1, u}}
  {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-- The underlying map of abelian-group presheaves of the zero endomorphism is zero. -/
theorem underlyingAb_zero (M : SheafOfModules.{u} S) :
    Stacks.SheafOfModules.LocallySurjective.underlyingAb (0 : M ⟶ M) = 0 := by
  show (PresheafOfModules.toPresheaf S.obj).map
    ((SheafOfModules.forget S).map (0 : M ⟶ M)) = 0
  rw [Functor.map_zero, Functor.map_zero]

/-- A vanishing stalk makes the zero endomorphism surjective on that stalk. -/
theorem surjOnStalk_zero_of_isZero (M : SheafOfModules.{u} S) (y : Y)
    (h : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} y).obj M.val.presheaf)) :
    Stacks.SheafOfModules.LocallySurjective.SurjOnStalk (0 : M ⟶ M) y :=
  fun _ => ⟨0, (AddCommGrpCat.subsingleton_of_isZero h).elim _ _⟩

/-- Conversely, if the zero endomorphism is surjective on the stalk at `y`, that stalk vanishes:
the zero map is surjective only onto a zero group. -/
theorem isZero_of_surjOnStalk_zero (M : SheafOfModules.{u} S) (y : Y)
    (h : Stacks.SheafOfModules.LocallySurjective.SurjOnStalk (0 : M ⟶ M) y) :
    IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} y).obj M.val.presheaf) := by
  have hzero : ∀ a : (TopCat.Presheaf.stalkFunctor Ab.{u} y).obj M.val.presheaf, a = 0 := by
    intro a
    obtain ⟨c, hc⟩ := h a
    refine hc.symm.trans ?_
    rw [underlyingAb_zero M, Functor.map_zero]
    rfl
  exact @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- `Stacks.SheafOfModules.LocallySurjective.LocallySurjOn` is downward closed in its open: the
predicate asks something of the points *of* that open, so shrinking it asks for less. -/
theorem locallySurjOn_of_le {F G : SheafOfModules.{u} S} (φ : G ⟶ F) {V W : Opens Y}
    (h : Stacks.SheafOfModules.LocallySurjective.LocallySurjOn φ V) (hWV : W ≤ V) :
    Stacks.SheafOfModules.LocallySurjective.LocallySurjOn φ W :=
  fun U t y hyU hyW => h U t y hyU (hWV hyW)

/-- A morphism of modules on a ringed space which is locally surjective over an open `W` becomes
an epimorphism after restriction to `W`. -/
private lemma epi_over_of_locallySurjOn {F G : SheafOfModules.{u} S}
    (φ : G ⟶ F) (W : Opens Y) (h : Stacks.SheafOfModules.LocallySurjective.LocallySurjOn φ W) :
    Epi (φ.over W) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {V} s => ?_⟩
  intro y hy
  obtain ⟨V', hV'V, ⟨t, ht⟩, hyV'⟩ := h V.left s y hy (V.hom.le hy)
  exact ⟨V', homOfLE hV'V, (Sieve.overEquiv_iff _ _).2 ⟨t, ht⟩, hyV'⟩

end RingedSpace

/-! ### The two neighbourhood statements, in downward-closed form -/

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **Part (3) of [Stacks, Tag 01Y3] in downward-closed form.** A morphism with finite-type
target which is surjective on the stalk at `x` has a neighbourhood `U` of `x` such that its
restriction to **every** open `W ≤ U` is an epimorphism. -/
theorem exists_epi_over_le_of_stalk_surjective {F G : SheafOfModules.{u} R}
    [F.IsFiniteType] (φ : G ⟶ F) (x : X)
    (hx : Function.Surjective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    ∃ U : Opens X, x ∈ U ∧ ∀ W : Opens X, W ≤ U → Epi (φ.over W) := by
  let Y := auxRingedSpace X
  obtain ⟨V, hxV, hV⟩ := Stacks.SheafOfModules.LocallySurjective.exists_nbhd_locallySurjOn (X := Y)
    φ (show SheafOfModules.IsFiniteType.{u, u, u} F from inferInstance) x hx
  exact ⟨V, hxV, fun W hWV => epi_over_of_locallySurjOn (Y := Y) φ W
    (locallySurjOn_of_le (Y := Y) φ hV hWV)⟩

/-- A finite-type module whose stalk at `x` vanishes has all of its stalks vanishing on a
neighbourhood of `x`. This is part (1) of [Stacks, Tag 01Y3] read pointwise rather than as a
vanishing of the restricted module. -/
theorem exists_forall_stalk_isZero_of_stalk_isZero (M : SheafOfModules.{u} R)
    [M.IsFiniteType] (x : X)
    (hx : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj M.val.presheaf)) :
    ∃ U : Opens X, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} y).obj M.val.presheaf) := by
  let Y := auxRingedSpace X
  obtain ⟨U, hxU, hU⟩ := Stacks.SheafOfModules.LocallySurjective.main_theorem (X := Y) (R := R)
    (0 : M ⟶ M) (show SheafOfModules.IsFiniteType.{u, u, u} M from inferInstance) x
    (surjOnStalk_zero_of_isZero (Y := Y) M x hx)
  exact ⟨U, hxU, fun y hy => isZero_of_surjOnStalk_zero (Y := Y) M y (hU y hy)⟩

/-- If the stalk of `kernel φ` at `y` vanishes then `φ` is injective on the stalk at `y`.
This is [Stacks, Tag 01AG]'s stalkwise exactness criterion applied to the kernel sequence. -/
theorem stalk_injective_of_kernel_stalk_isZero {F G : SheafOfModules.{u} R}
    (φ : G ⟶ F) (y : X)
    (hK : IsZero ((SheafOfModules.stalkAddCommGroupFunctor R y).obj (kernel φ))) :
    Function.Injective
      (ConcreteCategory.hom ((SheafOfModules.stalkAddCommGroupFunctor R y).map φ)) :=
  injective_of_exact_of_isZero
    ((SheafOfModules.exact_iff_stalkShortComplex_exact R
      (ShortComplex.kernelSequence φ)).mp (ShortComplex.kernelSequence_exact φ) y) hK

/-- **[Stacks, Tag 01C0] in downward-closed form.** A morphism from a finite-type module to a
coherent module which is injective on the stalk at `x` has a neighbourhood `U` of `x` such that
its restriction to **every** open `W ≤ U` is a monomorphism. -/
theorem exists_mono_over_le_of_stalk_injective {F G : SheafOfModules.{u} R}
    [G.IsFiniteType] [F.IsCoherent] (φ : G ⟶ F) (x : X)
    (hx : Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    ∃ U : Opens X, x ∈ U ∧ ∀ W : Opens X, W ≤ U → Mono (φ.over W) := by
  have hKft : (kernel φ).IsFiniteType :=
    AlgebraicGeometry.CoherentAbelian.isFiniteType_kernel_of_isCoherent φ
  have hKx : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj (kernel φ).val.presheaf) := by
    have hmono : Mono ((SheafOfModules.toSheaf R).map (kernel.ι φ)) := by
      rw [Sheaf.Hom.mono_iff_presheaf_mono, NatTrans.mono_iff_mono_app]
      intro U
      show Mono ((forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat).map
        ((SheafOfModules.evaluation R U).map (kernel.ι φ)))
      exact Functor.map_mono (forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat)
        ((SheafOfModules.evaluation R U).map (kernel.ι φ))
    have hkinj : Function.Injective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((SheafOfModules.toSheaf R).map (kernel.ι φ)).hom))) :=
      (AddCommGrpCat.mono_iff_injective _).1
        (@TopCat.Presheaf.stalk_mono_of_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _
          ((SheafOfModules.toSheaf R).map (kernel.ι φ)) hmono x)
    have hsub : Subsingleton
        ((SheafOfModules.stalkAddCommGroupFunctor R x).obj (kernel φ)) := by
      refine ⟨fun a b => hkinj (hx ?_)⟩
      have hk : ∀ z : (SheafOfModules.stalkAddCommGroupFunctor R x).obj (kernel φ),
          (ConcreteCategory.hom ((SheafOfModules.stalkAddCommGroupFunctor R x).map φ))
            ((ConcreteCategory.hom
              ((SheafOfModules.stalkAddCommGroupFunctor R x).map (kernel.ι φ))) z) = 0 := by
        intro z
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, kernel.condition,
          Functor.map_zero]
        rfl
      exact (hk a).trans (hk b).symm
    exact @AddCommGrpCat.isZero_of_subsingleton _ hsub
  obtain ⟨U, hxU, hU⟩ := exists_forall_stalk_isZero_of_stalk_isZero (kernel φ) x hKx
  refine ⟨U, hxU, fun W hWU => ?_⟩
  apply (SheafOfModules.forget (R.over W)).mono_of_mono_map
  apply (PresheafOfModules.toPresheaf (R.over W).obj).mono_of_mono_map
  apply (NatTrans.mono_iff_mono_app _).2
  intro V
  have hVU : V.unop.left ≤ U := le_trans V.unop.hom.le hWU
  have hApp := TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (C := AddCommGrpCat.{u}) (((SheafOfModules.toSheaf R).map φ).hom) V.unop.left
      (fun y hy => by
        show Function.Injective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            (((SheafOfModules.toSheaf R).map φ).hom)))
        exact stalk_injective_of_kernel_stalk_isZero φ y (hU y (hVU hy)))
  have hGroup : Mono ((forget₂ (ModuleCat (R.obj.obj (op V.unop.left))) AddCommGrpCat).map
      ((SheafOfModules.evaluation R (op V.unop.left)).map φ)) :=
    (AddCommGrpCat.mono_iff_injective _).2 fun _ _ hab => hApp hab
  have heq : (((PresheafOfModules.toPresheaf (R.over W).obj).map
        ((SheafOfModules.forget (R.over W)).map (φ.over W))).app V) =
      (forget₂ (ModuleCat (R.obj.obj (op V.unop.left))) AddCommGrpCat).map
        ((SheafOfModules.evaluation R (op V.unop.left)).map φ) := by
    ext a
    rfl
  exact heq ▸ hGroup

/-! ### The two tagged statements -/

/-- **[Stacks, Tag 01C0]**, which is also part (2) of [Stacks, Tag 01Y3]. A morphism from a
finite-type module sheaf to a coherent module sheaf which is injective on one stalk is injective
after restriction to a neighbourhood of that point. -/
@[stacks 01C0]
theorem exists_isMono_over_of_stalk_injective {F G : SheafOfModules.{u} R}
    [G.IsFiniteType] [F.IsCoherent] (φ : G ⟶ F) (x : X)
    (hx : Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    ∃ U : Opens X, x ∈ U ∧ Mono (φ.over U) := by
  obtain ⟨U, hxU, hU⟩ := exists_mono_over_le_of_stalk_injective φ x hx
  exact ⟨U, hxU, hU U le_rfl⟩

add_to_stacks 01Y3 "part (2)"
  Stacks.AlgebraicGeometry.Tag01Y3LocalIso.exists_isMono_over_of_stalk_injective

/-- **Part (4) of [Stacks, Tag 01Y3].** A map from a finite-type module sheaf to a coherent
module sheaf which is an isomorphism on one stalk is an isomorphism after restriction to a
neighbourhood of that point. -/
@[stacks 01Y3 "part (4)"]
theorem exists_isIso_over_of_stalk_isIso {F G : SheafOfModules.{u} R}
    [F.IsCoherent] [G.IsFiniteType] (φ : G ⟶ F) (x : X)
    (hx : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf R.obj).map φ.val))) :
    ∃ U : Opens X, x ∈ U ∧ IsIso (φ.over U) := by
  have hbij : Function.Bijective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val))) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hx
  have hFft : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  obtain ⟨U, hxU, hU⟩ := exists_mono_over_le_of_stalk_injective φ x hbij.1
  obtain ⟨V, hxV, hV⟩ := exists_epi_over_le_of_stalk_surjective φ x hbij.2
  have := hU (U ⊓ V) inf_le_left
  have := hV (U ⊓ V) inf_le_right
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩, isIso_of_mono_of_epi _⟩

end Stacks.AlgebraicGeometry.Tag01Y3LocalIso

end
