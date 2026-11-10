module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceExact
public import StacksFrontier.AlgebraicGeometry.Thickenings.SummandSubscheme

/-!
# The conormal sheaf of the subscheme cut out by a summand of the conormal sheaf

Let `i : Z ⟶ W` be a first-order thickening of schemes and let `𝒞_{Z/W} = A ⊕ C` be a direct sum
decomposition of its conormal sheaf.
`StacksFrontier.AlgebraicGeometry.Thickenings.SummandSubscheme`
cuts the summand `C ⊆ 𝒞_{Z/W} = ℐ ⊆ 𝒪_W` out of `W`, producing a factorization
`Z --a--> Y --b--> W` of `i` into first-order thickenings with `𝒞_{Y/W} = C`.  This file identifies
the conormal sheaf of the *new* thickening `a : Z ⟶ Y` with the complementary summand `A`,
compatibly with the canonical map of [Stacks Project, Tag 01R4].

That identification is the second half of the paragraph of [Stacks Project, Tag 06D8] which reads

> Let `Z' ⊂ Z''` be the closed subscheme cut out by `𝒞_{Z/X} ⊂ ℐ` […].  Note that by construction
> `𝒞_{Z/Z'} = i^* 𝒞_{X/X'}`

## Main results

* `Stacks.Thickenings.pushforwardConormalLeftMap_comp_firstOrderImmersionConormalSheafι`: for a
  chain `Z --a--> Y --b--> W` of closed immersions with `(a ≫ b)` of first order, the left-hand map
  `a^* 𝒞_{Y/W} ⟶ 𝒞_{Z/W}` of the conormal sequence of [Stacks Project, Tag 062S], pushed forward
  to `W` and followed by the inclusion `𝒞_{Z/W} ⊆ 𝒪_W`, is the inclusion `𝒞_{Y/W} ⊆ 𝒪_W`.  In
  other words the left-hand map *is* the inclusion `𝒥 ⊆ ℐ` of defining ideals.
* `Stacks.Thickenings.exists_iso_comp_eq_conormalLeftMap`: consequently, if `𝒞_{Y/W}` is
  identified with a module `C` on `Z` compatibly with those inclusions — which is what
  `Stacks.Thickenings.conormalSheafIsoOfMono` provides for the subscheme cut out by a summand —
  then the left-hand map of the conormal sequence is, up to a unique isomorphism, the given
  monomorphism `C ⟶ 𝒞_{Z/W}`.
* `Stacks.Thickenings.isIso_comp_conormalSequenceRightMap_of_splitting`: if `𝒞_{Z/W} = A ⊕ C` with
  `C` the summand that was cut out, then `A ⟶ 𝒞_{Z/W} ⟶ 𝒞_{Z/Y}` is an isomorphism.
* `Stacks.Thickenings.isIso_immersionConormalSheafMap_of_splitting`: the same conclusion
  transported along the functoriality of [Stacks Project, Tag 01R4] to the canonical map
  `f^* 𝒞_{X/X'} ⟶ 𝒞_{Z/Y}` of the square `(Z ⊆ Y) → (X ⊆ X')`.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.Immersion Stacks.ClosedImmersion

universe u

namespace Stacks.Thickenings

variable {Z Y W : Scheme.{u}} (a : Z ⟶ Y) (b : Y ⟶ W)
  [IsClosedImmersion a] [IsClosedImmersion b]

omit [IsClosedImmersion a] [IsClosedImmersion b] in
/-- The square with horizontal maps `a ≫ b` and `b` and vertical maps `a` and `𝟙_W`. -/
theorem comp_id_square : (a ≫ b) ≫ (𝟙 W : W ⟶ W) = a ≫ b := Category.comp_id _

omit [IsClosedImmersion a] [IsClosedImmersion b] in
/-- The pushforward comparison of the square with right edge `𝟙_W` is the identity. -/
theorem modulePushforwardSquareIso_hom_app_comp_id
    (N : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) :
    (modulePushforwardSquareIso a.toLRSHom.toShHom (𝟙 W : W ⟶ W).toLRSHom.toShHom
        (a ≫ b).toLRSHom.toShHom b.toLRSHom.toShHom
        (toShHom_square (comp_id_square a b))).hom.app N = 𝟙 _ :=
  rfl

/-- **The left-hand map of the conormal sequence of [Stacks Project, Tag 062S] for a chain
`Z ⟶ Y ⟶ W` of closed immersions, transposed along `a^* ⊣ a_*` and read on `W`.**

Its target is written `(a ≫ b)_* 𝒞_{Z/W}`, which agrees on the nose with `b_* a_* 𝒞_{Z/W}`. -/
def pushforwardConormalLeftMap :
    (modulePushforward b.toLRSHom.toShHom).obj (immersionConormalSheaf b) ⟶
      (modulePushforward (a ≫ b).toLRSHom.toShHom).obj (immersionConormalSheaf (a ≫ b)) :=
  (modulePushforward b.toLRSHom.toShHom).map
    ((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv _ _ (conormalLeftMap a b))

/-- The unit of `(𝟙_W)^* ⊣ (𝟙_W)_*` at the defining ideal sheaf of `b`, with its target written
`(𝟙_W)^* ℐ_b` rather than `(𝟙_W)_* (𝟙_W)^* ℐ_b`; the two agree on the nose, pushforward along the
identity being the identity functor. -/
def unitIdIdealSheaf : idealSheaf b.toLRSHom.toShHom ⟶
    (modulePullback (𝟙 W : W ⟶ W).toLRSHom.toShHom).obj (idealSheaf b.toLRSHom.toShHom) :=
  (modulePullbackPushforwardAdjunction (𝟙 W : W ⟶ W).toLRSHom.toShHom).unit.app
    (idealSheaf b.toLRSHom.toShHom)

/-- The identity of `Stacks.Immersion.canonicalConormalQuotientMap_comp_pushforward_homEquiv` at
the square whose right edge is `𝟙_W`, with the identity pushforward and the pushforward
comparison of the square collapsed. -/
theorem canonicalConormalQuotientMap_comp_pushforwardConormalLeftMap :
    canonicalConormalQuotientMap b ≫ pushforwardConormalLeftMap a b =
      unitIdIdealSheaf b ≫
        idealSheafMap (toShHom_square (comp_id_square a b)) ≫
          canonicalConormalQuotientMap (a ≫ b) :=
  canonicalConormalQuotientMap_comp_pushforward_homEquiv (a ≫ b) b a (𝟙 W)
    (toShHom_square (comp_id_square a b))

omit [IsClosedImmersion a] [IsClosedImmersion b] in
/-- `Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι` at the same square. -/
theorem unitIdIdealSheaf_comp_idealSheafMap_comp_ι :
    unitIdIdealSheaf b ≫
      idealSheafMap (toShHom_square (comp_id_square a b)) ≫
        idealSheafι (a ≫ b).toLRSHom.toShHom =
      idealSheafι b.toLRSHom.toShHom :=
  unit_comp_pushforward_idealSheafMap_comp_ι (toShHom_square (comp_id_square a b))

/-- **The left-hand map of the conormal sequence of a chain of first-order thickenings is the
inclusion of defining ideals.**  For closed immersions `a : Z ⟶ Y` and `b : Y ⟶ W` with
`(a ≫ b).ker² = 0`, the left-hand map `a^* 𝒞_{Y/W} ⟶ 𝒞_{Z/W}` of [Stacks Project, Tag 062S],
transposed along `a^* ⊣ a_*` and pushed forward to `W`, followed by the inclusion
`𝒞_{Z/W} ⊆ 𝒪_W` of `Stacks.Thickenings.firstOrderImmersionConormalSheafι`, is the inclusion
`𝒞_{Y/W} ⊆ 𝒪_W`.

Both conormal sheaves of a first-order thickening *are* the defining ideal sheaves, so this says
that the canonical map of [Stacks Project, Tag 01R4] for the square with vertical maps `a` and
`𝟙_W` is the containment `ℐ_b ⊆ ℐ_{a ≫ b}`. -/
theorem pushforwardConormalLeftMap_comp_firstOrderImmersionConormalSheafι
    (hsq : (a ≫ b).ker ^ 2 = ⊥) (hsqb : b.ker ^ 2 = ⊥) :
    pushforwardConormalLeftMap a b ≫ firstOrderImmersionConormalSheafι (a ≫ b) hsq =
      firstOrderImmersionConormalSheafι b hsqb := by
  have := isIso_canonicalConormalQuotientMap b hsqb
  refine (cancel_epi (canonicalConormalQuotientMap b)).mp ?_
  rw [canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι b hsqb,
    ← Category.assoc, canonicalConormalQuotientMap_comp_pushforwardConormalLeftMap a b,
    Category.assoc, Category.assoc,
    canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι (a ≫ b) hsq,
    unitIdIdealSheaf_comp_idealSheafMap_comp_ι a b]

section Summand

variable {M : SheafOfModules.{u} (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace)}
  {N : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}

/-- The unit of `a^* ⊣ a_*` pushed forward along `b`, with its target written
`(a ≫ b)_* a^* M` rather than `b_* a_* a^* M`. -/
def pushforwardChainUnit (M : SheafOfModules.{u}
    (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace)) :
    (modulePushforward b.toLRSHom.toShHom).obj M ⟶
      (modulePushforward (a ≫ b).toLRSHom.toShHom).obj
        ((modulePullback a.toLRSHom.toShHom).obj M) :=
  (modulePushforward b.toLRSHom.toShHom).map
    ((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).unit.app M)

omit [IsClosedImmersion a] [IsClosedImmersion b] in
/-- `Stacks.Thickenings.pushforwardChainUnit` is invertible whenever the unit it is the pushforward
of is. -/
theorem isIso_pushforwardChainUnit
    (h : IsIso ((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).unit.app M)) :
    IsIso (pushforwardChainUnit a b M) :=
  have := h
  inferInstanceAs (IsIso ((modulePushforward b.toLRSHom.toShHom).map
    ((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).unit.app M)))

omit [IsClosedImmersion a] [IsClosedImmersion b] in
/-- `b_*` of a transpose along `a^* ⊣ a_*` splits into the unit and the pushforward along the
composite. -/
theorem pushforward_homEquiv_eq (φ : (modulePullback a.toLRSHom.toShHom).obj M ⟶ N) :
    (modulePushforward b.toLRSHom.toShHom).map
        ((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv _ _ φ) =
      pushforwardChainUnit a b M ≫ (modulePushforward (a ≫ b).toLRSHom.toShHom).map φ := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

/-- `Stacks.Thickenings.pushforwardConormalLeftMap` split into the unit of `a^* ⊣ a_*` and the
pushforward of the left-hand map of the conormal sequence. -/
theorem pushforwardConormalLeftMap_eq :
    pushforwardConormalLeftMap a b =
      pushforwardChainUnit a b (immersionConormalSheaf b) ≫
        (modulePushforward (a ≫ b).toLRSHom.toShHom).map (conormalLeftMap a b) :=
  pushforward_homEquiv_eq a b (conormalLeftMap a b)

/-- **The left-hand map of the conormal sequence is the given summand.**  Let
`Z --a--> Y --b--> W` be closed immersions with `(a ≫ b).ker² = 0`, let `β : C ⟶ 𝒞_{Z/W}` be a
morphism of `𝒪_Z`-modules, and suppose the pushforward of `C` to `W` is identified with
`𝒞_{Y/W}` compatibly with the two inclusions into `𝒪_W` — that is, with `β` on one side and the
inclusion `𝒞_{Y/W} ⊆ 𝒪_W` on the other.  Then `β` is the left-hand map
`a^* 𝒞_{Y/W} ⟶ 𝒞_{Z/W}` of [Stacks Project, Tag 062S] up to an isomorphism of its source. -/
theorem exists_iso_comp_eq_conormalLeftMap (hsq : (a ≫ b).ker ^ 2 = ⊥) (hsqb : b.ker ^ 2 = ⊥)
    (β : N ⟶ immersionConormalSheaf (a ≫ b))
    (lam : (modulePushforward (a ≫ b).toLRSHom.toShHom).obj N ≅
      (modulePushforward b.toLRSHom.toShHom).obj (immersionConormalSheaf b))
    (hlam : lam.hom ≫ firstOrderImmersionConormalSheafι b hsqb =
      (modulePushforward (a ≫ b).toLRSHom.toShHom).map β ≫
        firstOrderImmersionConormalSheafι (a ≫ b) hsq) :
    ∃ ρ : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf b) ≅ N,
      ρ.hom ≫ β = conormalLeftMap a b := by
  have : (modulePushforward b.toLRSHom.toShHom).Full := full_pushforward b
  have : (modulePushforward b.toLRSHom.toShHom).Faithful := faithful_pushforward b
  have : (modulePushforward a.toLRSHom.toShHom).Full := full_pushforward a
  have : (modulePushforward a.toLRSHom.toShHom).Faithful := faithful_pushforward a
  have : (modulePushforward (a ≫ b).toLRSHom.toShHom).Faithful := faithful_pushforward (a ≫ b)
  obtain ⟨g, hg⟩ : ∃ g : immersionConormalSheaf b ≅
      (modulePushforward a.toLRSHom.toShHom).obj N,
      (modulePushforward b.toLRSHom.toShHom).map g.hom = lam.inv :=
    ⟨(modulePushforward b.toLRSHom.toShHom).preimageIso lam.symm, Functor.map_preimage _ _⟩
  have hunit : IsIso ((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).unit.app
      (immersionConormalSheaf b)) := Adjunction.isIso_unit_app_of_iso _ g
  have : IsIso (((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv
      (immersionConormalSheaf b) N).symm g.hom) := by
    rw [Adjunction.homEquiv_counit]
    exact IsIso.comp_isIso
  refine ⟨asIso (((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv
    (immersionConormalSheaf b) N).symm g.hom), ?_⟩
  refine (modulePushforward (a ≫ b).toLRSHom.toShHom).map_injective ?_
  have := isIso_pushforwardChainUnit a b (M := immersionConormalSheaf b) hunit
  refine (cancel_epi (pushforwardChainUnit a b (immersionConormalSheaf b))).mp ?_
  rw [Functor.map_comp, ← Category.assoc, ← pushforward_homEquiv_eq a b,
    ← pushforwardConormalLeftMap_eq a b, asIso_hom, Equiv.apply_symm_apply, hg]
  have := mono_firstOrderImmersionConormalSheafι (a ≫ b) hsq
  refine (cancel_mono (firstOrderImmersionConormalSheafι (a ≫ b) hsq)).mp ?_
  rw [Category.assoc, ← hlam, Iso.inv_hom_id_assoc]
  exact (pushforwardConormalLeftMap_comp_firstOrderImmersionConormalSheafι a b hsq hsqb).symm

/-- **A summand complementary to the one that was cut out is the conormal sheaf of the new
thickening.**  Let `Z --a--> Y --b--> W` be closed immersions with `(a ≫ b).ker² = 0` and let
`𝒞_{Z/W} = A ⊕ C` be a split short exact sequence with `C` identified, as in
`Stacks.Thickenings.exists_iso_comp_eq_conormalLeftMap`, with the conormal sheaf of `Y` in `W`.
Then the complementary summand `A ⟶ 𝒞_{Z/W}`, followed by the right-hand map
`𝒞_{Z/W} ⟶ 𝒞_{Z/Y}` of the conormal sequence of [Stacks Project, Tag 062S], is an isomorphism. -/
theorem isIso_comp_conormalSequenceRightMap_of_splitting
    (hsq : (a ≫ b).ker ^ 2 = ⊥) (hsqb : b.ker ^ 2 = ⊥)
    {A C : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    (α : A ⟶ immersionConormalSheaf (a ≫ b)) (γ : immersionConormalSheaf (a ≫ b) ⟶ C)
    (hzero : α ≫ γ = 0) (σ : (ShortComplex.mk α γ hzero).Splitting)
    (lam : (modulePushforward (a ≫ b).toLRSHom.toShHom).obj C ≅
      (modulePushforward b.toLRSHom.toShHom).obj (immersionConormalSheaf b))
    (hlam : lam.hom ≫ firstOrderImmersionConormalSheafι b hsqb =
      (modulePushforward (a ≫ b).toLRSHom.toShHom).map σ.s ≫
        firstOrderImmersionConormalSheafι (a ≫ b) hsq) :
    IsIso (α ≫ conormalSequenceRightMap a b) := by
  obtain ⟨ρ, hρ⟩ := exists_iso_comp_eq_conormalLeftMap a b hsq hsqb σ.s lam hlam
  have hmono : Mono (conormalLeftMap a b) := by
    have : IsSplitMono σ.s := ⟨⟨⟨γ, σ.s_g⟩⟩⟩
    rw [← hρ]
    infer_instance
  have hzero2 : σ.s ≫ conormalSequenceRightMap a b = 0 := by
    rw [show σ.s = ρ.inv ≫ conormalLeftMap a b by rw [← hρ, Iso.inv_hom_id_assoc],
      Category.assoc, conormalSequence_comp_zero a b, comp_zero]
  have := epi_conormalSequenceRightMap a b
  have hfac : σ.r ≫ α ≫ conormalSequenceRightMap a b = conormalSequenceRightMap a b := by
    simpa only [Preadditive.add_comp, Category.id_comp, Category.assoc, hzero2, comp_zero,
      add_zero] using congrArg (· ≫ conormalSequenceRightMap a b) σ.id
  have : Epi (σ.r ≫ α ≫ conormalSequenceRightMap a b) := by rw [hfac]; infer_instance
  have := epi_of_epi σ.r (α ≫ conormalSequenceRightMap a b)
  have : Mono (α ≫ conormalSequenceRightMap a b) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro T u hu
    have : Mono (conormalSequenceShortComplex a b).f := hmono
    obtain ⟨v, hv⟩ := (conormalSequence_exact a b).lift' (u ≫ α)
      ((Category.assoc u α _).trans hu)
    have h1 : u ≫ α ≫ σ.r = u := by
      rw [show α ≫ σ.r = 𝟙 A from σ.f_r, Category.comp_id]
    have h2 : conormalLeftMap a b ≫ σ.r = 0 := by
      rw [← hρ, Category.assoc, σ.s_r, comp_zero]
    have h3 : (u ≫ α) ≫ σ.r = 0 :=
      ((congrArg (· ≫ σ.r) hv).symm.trans (Category.assoc v _ σ.r)).trans
        ((congrArg (v ≫ ·) h2).trans comp_zero)
    exact h1.symm.trans ((Category.assoc u α σ.r).symm.trans h3)
  exact isIso_of_mono_of_epi _

end Summand

section Transport

variable {X X' : Scheme.{u}}

omit [IsClosedImmersion a] [IsClosedImmersion b] in
/-- The square with horizontal maps `a` and `a ≫ b` and vertical maps `𝟙_Z` and `b`, which is the
one the right-hand map of the conormal sequence of [Stacks Project, Tag 062S] is attached to. -/
theorem id_comp_square : a ≫ b = 𝟙 Z ≫ (a ≫ b) := (Category.id_comp _).symm

/-- The right-hand map of the conormal sequence, as the `Tag 01R4` map of the square with vertical
maps `𝟙_Z` and `b`, read through the pullback-identity comparison. -/
theorem immersionConormalSheafMap_id_eq :
    immersionConormalSheafMap a (a ≫ b) (𝟙 Z) b (toShHom_square (id_comp_square a b)) =
      (((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
          (immersionConormalSheaf (a ≫ b))).hom :
        (modulePullback (𝟙 Z : Z ⟶ Z).toLRSHom.toShHom).obj (immersionConormalSheaf (a ≫ b)) ⟶
          immersionConormalSheaf (a ≫ b)) ≫ conormalSequenceRightMap a b :=
  (Iso.hom_inv_id_assoc _ _).symm

/-- **The conclusion of `Stacks.Thickenings.isIso_comp_conormalSequenceRightMap_of_splitting`,
transported along the functoriality of [Stacks Project, Tag 01R4].**  For a square
`(Z ⊆ W) → (X ⊆ X')` of immersions, if the canonical map `f^* 𝒞_{X/X'} ⟶ 𝒞_{Z/W}` of the square
followed by the right-hand map `𝒞_{Z/W} ⟶ 𝒞_{Z/Y}` of the conormal sequence of `Z ⊆ Y ⊆ W` is an
isomorphism, then so is the canonical map `f^* 𝒞_{X/X'} ⟶ 𝒞_{Z/Y}` of the square
`(Z ⊆ Y) → (X ⊆ X')` obtained by restricting along `b : Y ⟶ W`; its left vertical map is written
`𝟙_Z ≫ f`. -/
theorem isIso_immersionConormalSheafMap_of_isIso_comp_conormalSequenceRightMap
    (iX : X ⟶ X') [IsImmersion iX] (f : Z ⟶ X) (g : W ⟶ X')
    (comm₂ : (a ≫ b) ≫ g = f ≫ iX)
    (h : IsIso (immersionConormalSheafMap (a ≫ b) iX f g (toShHom_square comm₂) ≫
      conormalSequenceRightMap a b)) :
    IsIso (immersionConormalSheafMap a iX (𝟙 Z ≫ f) (b ≫ g)
      (toShHom_square (square_comp (id_comp_square a b) comm₂))) := by
  have hQ : (modulePullback (𝟙 Z : Z ⟶ Z).toLRSHom.toShHom).map
        (immersionConormalSheafMap (a ≫ b) iX f g (toShHom_square comm₂)) ≫
      (((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
        (immersionConormalSheaf (a ≫ b))).hom :
          (modulePullback (𝟙 Z : Z ⟶ Z).toLRSHom.toShHom).obj
            (immersionConormalSheaf (a ≫ b)) ⟶ immersionConormalSheaf (a ≫ b)) =
      (((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
        ((modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf iX))).hom :
          (modulePullback (𝟙 Z : Z ⟶ Z).toLRSHom.toShHom).obj
            ((modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf iX)) ⟶
            (modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf iX)) ≫
        immersionConormalSheafMap (a ≫ b) iX f g (toShHom_square comm₂) :=
    (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).hom.naturality _
  have hfin : (modulePullback (𝟙 Z : Z ⟶ Z).toLRSHom.toShHom).map
        (immersionConormalSheafMap (a ≫ b) iX f g (toShHom_square comm₂)) ≫
      immersionConormalSheafMap a (a ≫ b) (𝟙 Z) b (toShHom_square (id_comp_square a b)) =
      (((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
        ((modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf iX))).hom :
          (modulePullback (𝟙 Z : Z ⟶ Z).toLRSHom.toShHom).obj
            ((modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf iX)) ⟶
            (modulePullback f.toLRSHom.toShHom).obj (immersionConormalSheaf iX)) ≫
        (immersionConormalSheafMap (a ≫ b) iX f g (toShHom_square comm₂) ≫
          conormalSequenceRightMap a b) :=
    ((congrArg (fun φ => (modulePullback (𝟙 Z : Z ⟶ Z).toLRSHom.toShHom).map
          (immersionConormalSheafMap (a ≫ b) iX f g (toShHom_square comm₂)) ≫ φ)
        (immersionConormalSheafMap_id_eq a b)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun φ => φ ≫ conormalSequenceRightMap a b) hQ))).trans
      (Category.assoc _ _ _)
  rw [immersionConormalSheafMap_comp a (a ≫ b) iX (𝟙 Z) b (id_comp_square a b) f g comm₂, hfin]
  exact IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
    (IsIso.comp_isIso' (Iso.isIso_hom _) h)

/-- **The conormal-sheaf map of the square `(Z ⊆ Y) → (X ⊆ X')` is an isomorphism**, where
`Z ⟶ Y ⟶ W` is a factorization of a first-order thickening `i : Z ⟶ W` obtained by cutting a
summand of its conormal sheaf out of `W`.

The hypotheses are: a split short exact sequence `0 → f^* 𝒞_{X/X'} → 𝒞_{Z/W} → C → 0` whose left
map is the canonical map of [Stacks Project, Tag 01R4] for the square `(Z ⊆ W) → (X ⊆ X')`, and an
identification of the pushforward of `C` with the conormal sheaf of `Y ⊆ W` compatible with the
inclusions into `𝒪_W`. -/
theorem isIso_immersionConormalSheafMap_of_splitting
    (i : Z ⟶ W) (hab : a ≫ b = i) [IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (hsqb : b.ker ^ 2 = ⊥)
    (iX : X ⟶ X') [IsImmersion iX] (fZ : Z ⟶ X) (g : W ⟶ X') (comm : i ≫ g = fZ ≫ iX)
    {C : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    (γ : immersionConormalSheaf i ⟶ C)
    (hzero : immersionConormalSheafMap i iX fZ g (toShHom_square comm) ≫ γ = 0)
    (σ : (ShortComplex.mk (immersionConormalSheafMap i iX fZ g (toShHom_square comm)) γ
      hzero).Splitting)
    (lam : (modulePushforward i.toLRSHom.toShHom).obj C ≅
      (modulePushforward b.toLRSHom.toShHom).obj (immersionConormalSheaf b))
    (hlam : lam.hom ≫ firstOrderImmersionConormalSheafι b hsqb =
      (modulePushforward i.toLRSHom.toShHom).map σ.s ≫
        firstOrderImmersionConormalSheafι i hsq) :
    IsIso (immersionConormalSheafMap a iX (𝟙 Z ≫ fZ) (b ≫ g)
      (toShHom_square (show a ≫ (b ≫ g) = (𝟙 Z ≫ fZ) ≫ iX by
        rw [Category.id_comp, ← Category.assoc, hab, comm]))) := by
  subst hab
  exact isIso_immersionConormalSheafMap_of_isIso_comp_conormalSequenceRightMap a b iX fZ g comm
    (isIso_comp_conormalSequenceRightMap_of_splitting a b hsq hsqb
      (immersionConormalSheafMap (a ≫ b) iX fZ g (toShHom_square comm)) γ hzero σ lam hlam)

end Transport

end Stacks.Thickenings

end
