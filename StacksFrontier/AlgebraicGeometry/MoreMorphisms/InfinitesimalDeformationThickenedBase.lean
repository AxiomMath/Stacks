module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationUnthickenedTarget

/-!
# Infinitesimal deformations of maps over a thickened base

Let `k : Z ⟶ Z'` be an immersion, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be immersions over `Z'` by
morphisms of thickenings `(g, g') : (X ⊂ X') ⟶ (Z ⊂ Z')` and `(h, h') : (Y ⊂ Y') ⟶ (Z ⊂ Z')`, and
assume `Y = Z ×_{Z'} Y'`. This is the situation of [Stacks Project, Tag 0CK2], the case of
[Stacks Project, Tag 04FH] in which the base is itself a thickening and the target thickening is
pulled back from it.

In that situation the datum `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04FH] is
determined by `a`: the map `h^* 𝒞_{Z/Z'} ⟶ 𝒞_{Y/Y'}` is an epimorphism because the square is
cartesian, so the same holds after pulling back along `a`, and the composite
`g^* 𝒞_{Z/Z'} ⟶ a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` has to be the canonical map of the square
`i ≫ g' = g ≫ k`. The sheaf of [Stacks Project, Tag 04FH] is therefore the elementary rule
`Stacks.Thickenings.liftsOverBasePresheaf`, assigning to an open `V` of `X'` the morphisms
`V ⟶ Y'` over `Z'` restricting to `a` on `X ∩ V`.

## Main definitions

* `Stacks.Thickenings.IsBaseCompatibleConormalMap`: the condition on `A` that the composite
  `g^* 𝒞_{Z/Z'} ⟶ a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is the canonical map of [Stacks Project, Tag 01R4]
  attached to the square `i ≫ g' = g ≫ k`.

## Main results

* `Stacks.Thickenings.epi_modulePullback_immersionConormalSheafMap`: the pullback along any
  morphism into `Y` of the canonical map `h^* 𝒞_{Z/Z'} ⟶ 𝒞_{Y/Y'}` is an epimorphism.
* `Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap`: `A` is determined by `a`.
* `Stacks.Thickenings.isBaseCompatibleConormalMap_restrict`: the restriction of `A` to an open of
  `X'` is again compatible with the base.
* `Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift`: the canonical map of conormal sheaves
  attached to a lift of `a` over `Z'` is compatible with the base.
* `Stacks.Thickenings.isBaseCompatibleConormalMap_of_isCompatibleLift`: a datum `A` that admits a
  compatible lift over an open of `X'` is compatible with the base there — the composition
  `g^* 𝒞_{Z/Z'} ⟶ a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` *has to be* the canonical map induced by `g'`.
* `Stacks.Thickenings.isCompatibleLift_iff_of_isBaseCompatible`: the third condition of
  [Stacks Project, Tag 04FI] is automatic, so a compatible lift is exactly a lift over `Z'`
  extending `a`.
* `Stacks.Thickenings.compatibleLiftsPresheafIsoLiftsOverBasePresheafOfBase`: the presheaf of
  [Stacks Project, Tag 04FH] is isomorphic to the elementary rule.

The remaining assertion of [Stacks Project, Tag 0CK2] — that
`Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` acts on the elementary rule, simply transitively over an open
carrying a lift — is `Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBaseOfBase`
in `StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseAction`.
That file transports the unrestricted [Stacks Project, Tag 04FJ] for the base `Z'` along the
isomorphism above, and along `Ω_{Y/Z'} ≅ Ω_{Y/Z}`
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsIsoOfEq`, which holds because `k` is an
immersion) so that the acting sheaf is the one the source names. Every assertion of the remark
therefore holds, with no hypothesis beyond the source's.

Base compatibility of `A` is the source's own determination of `A` by `a`, not an added
hypothesis: the statements about the lifting sheaf are false for a datum that is not the
determined one, and by
`Stacks.Thickenings.isBaseCompatibleConormalMap_of_isCompatibleLift` any datum whose sheaf of
lifts has a section over an open is base compatible over that open. So over the opens where
there is anything to describe, the condition holds of itself.

## Implementation notes

The morphism `g : X ⟶ Z` is not carried as separate data: the commuting triangle of the source
forces `g = a ≫ h`, so the composite is written out. This keeps the pullback indices on the nose
and avoids transporting the canonical map of [Stacks Project, Tag 01R4] along an equality of
edges.

Surjectivity before the pullback is [Stacks Project, Tag 0473],
`Stacks.Immersion.epi_immersionConormalSheafMap`; it survives the pullback because the module
pullback is a left adjoint, hence preserves epimorphisms.

That compatibility with the base restricts to an open `V` of `X'` is where the pseudofunctor
coherences enter: the composite is reassociated using naturality of the pullback composition
isomorphism, its associativity coherence
`RingedSpaceModuleAdjunction.modulePullbackComp_assoc`, and the composition law
`Stacks.Immersion.immersionConormalSheafMap_comp` for the canonical map. The reassociation is
factored through the abstract `Stacks.Thickenings.assoc_shuffle` and
`Stacks.Thickenings.base_shuffle`, so that the large module terms are written once. Splitting it
that way is what keeps the two spellings of the pullback along `ι_{i⁻¹V} ≫ a ≫ h` — one grouping
`ι_{i⁻¹V} ≫ a` first, the other `a ≫ h` — confined to the statement of
`Stacks.Thickenings.modulePullbackComp_assoc_base`; a single combined proof spends its whole
heartbeat budget on that one definitional unfolding.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

/-- The reassociation used in the proof of
`Stacks.Thickenings.isBaseCompatibleConormalMap_restrict`, stated so that the large module terms
it is applied at are written once. -/
private theorem base_shuffle {C : Type*} [Category C] {A₀ A₁ A₂ A₃ B₀ B₁ B₂ C₀ : C}
    {c1 : A₀ ⟶ A₁} {m1 : A₁ ⟶ A₂} {c2 : A₂ ⟶ A₃} {m2 : A₃ ⟶ B₀} {t : B₀ ⟶ B₁}
    {m1' : B₂ ⟶ A₃} {d1 : A₀ ⟶ C₀} {d2 : C₀ ⟶ B₂} {w : C₀ ⟶ B₀}
    (h1 : c1 ≫ m1 ≫ c2 = d1 ≫ d2 ≫ m1') (h2 : d2 ≫ m1' ≫ m2 = w) :
    c1 ≫ m1 ≫ c2 ≫ m2 ≫ t = d1 ≫ w ≫ t := by
  subst h2
  calc c1 ≫ m1 ≫ c2 ≫ m2 ≫ t
      = (c1 ≫ m1 ≫ c2) ≫ m2 ≫ t := by simp only [Category.assoc]
    _ = (d1 ≫ d2 ≫ m1') ≫ m2 ≫ t := by rw [h1]
    _ = d1 ≫ (d2 ≫ m1' ≫ m2) ≫ t := by simp only [Category.assoc]

/-- The reassociation combining a naturality square with an associativity coherence, stated
abstractly so that the two spellings of the three-fold pullback meet only in the types of the two
hypotheses. -/
private theorem assoc_shuffle {C : Type*} [Category C] {A₀ A₁ A₂ A₃ B₂ C₀ : C}
    {c1 : A₀ ⟶ A₁} {m1 : A₁ ⟶ A₂} {c2 : A₂ ⟶ A₃} {c2' : A₁ ⟶ B₂} {m1' : B₂ ⟶ A₃}
    {d1 : A₀ ⟶ C₀} {d2 : C₀ ⟶ B₂} (nat : m1 ≫ c2 = c2' ≫ m1')
    (hassoc : d1 ≫ d2 = c1 ≫ c2') : c1 ≫ m1 ≫ c2 = d1 ≫ d2 ≫ m1' := by
  rw [nat, ← Category.assoc, ← hassoc, Category.assoc]

variable {X X' Y Y' Z Z' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {k : Z ⟶ Z'}

/-! ### Surjectivity of the conormal map coming from the base -/

/-- **The canonical map of conormal sheaves coming from the base stays surjective after
pullback.** For `Y = Z ×_{Z'} Y'` the canonical map `h^* 𝒞_{Z/Z'} ⟶ 𝒞_{Y/Y'}` of
[Stacks Project, Tag 01R4] is an epimorphism by [Stacks Project, Tag 0473], and the module
pullback along any morphism `c : W ⟶ Y` preserves epimorphisms, being a left adjoint.

Taken at `c = a` this is the surjectivity of `g^* 𝒞_{Z/Z'} ⟶ a^* 𝒞_{Y/Y'}` used in
[Stacks Project, Tag 0CK2]; taken at `c = ι_{i⁻¹V} ≫ a` it is the same statement over an open
of `X'`. -/
@[stacks 0CK2 "surjectivity of the conormal map coming from the base, after pullback"]
theorem epi_modulePullback_immersionConormalSheafMap [IsImmersion j] [IsImmersion k]
    {W : Scheme.{u}} {h : Y ⟶ Z} {h' : Y' ⟶ Z'} (sq : IsPullback j h h' k) (c : W ⟶ Y) :
    Epi ((modulePullback c.toLRSHom.toShHom).map
      (immersionConormalSheafMap j k h h' (toShHom_square sq.w))) := by
  have : Epi (immersionConormalSheafMap j k h h' (toShHom_square sq.w)) :=
    epi_immersionConormalSheafMap j k h h' sq
  have : Functor.IsLeftAdjoint (modulePullback c.toLRSHom.toShHom) :=
    ⟨modulePushforward _, ⟨modulePullbackPushforwardAdjunction _⟩⟩
  exact (modulePullback c.toLRSHom.toShHom).map_epi _

/-! ### The conormal datum is determined by the map on the closed subschemes -/

/-- **Compatibility of a conormal datum with the base thickening.** For `a : X ⟶ Y` and
`A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}`, this says that the composite
`g^* 𝒞_{Z/Z'} = a^* h^* 𝒞_{Z/Z'} ⟶ a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is the canonical map of
[Stacks Project, Tag 01R4] attached to the square `i ≫ g' = (a ≫ h) ≫ k`.

[Stacks Project, Tag 0CK2] observes that this holds for the conormal datum of any lift of `a`,
and that it pins `A` down. -/
def IsBaseCompatibleConormalMap (i : X ⟶ X') (j : Y ⟶ Y') (k : Z ⟶ Z')
    [IsImmersion i] [IsImmersion j] [IsImmersion k] (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z')
    (a : X ⟶ Y) (hj : j ≫ h' = h ≫ k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) : Prop :=
  (modulePullbackComp a.toLRSHom.toShHom h.toLRSHom.toShHom).hom.app
        (immersionConormalSheaf k) ≫
      (modulePullback a.toLRSHom.toShHom).map
        (immersionConormalSheafMap j k h h' (toShHom_square hj)) ≫ A =
    immersionConormalSheafMap i k (a ≫ h) g' (toShHom_square ci)

variable {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X ⟶ Y}

/-- **The square over the base cut out by an open of the ambient scheme.** The restriction of
`i` to an open `V` of `X'` sits over `Z'` by `V.ι ≫ g'`, compatibly with `ι_{i⁻¹V} ≫ a`. -/
theorem comm_restrict_base (i : X ⟶ X') (k : Z ⟶ Z') (h : Y ⟶ Z) (g' : X' ⟶ Z') (a : X ⟶ Y)
    (ci : i ≫ g' = (a ≫ h) ≫ k) (V : X'.Opens) :
    i ∣_ V ≫ (V.ι ≫ g') = (((i ⁻¹ᵁ V).ι ≫ a) ≫ h) ≫ k :=
  square_comp (f₂ := a ≫ h) (morphismRestrict_ι i V) ci

section

variable [IsImmersion i] [IsImmersion j] [IsImmersion k]

/-- **The conormal datum of [Stacks Project, Tag 04FH] is determined by `a` over a thickened
base.** If two maps `A, B : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` are both compatible with the base, they are
equal: the map they are precomposed with is an epimorphism by
`Stacks.Thickenings.epi_modulePullback_immersionConormalSheafMap`. -/
@[stacks 0CK2 "the conormal datum is determined by the map on the closed subschemes"]
theorem eq_of_isBaseCompatibleConormalMap (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A B : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A)
    (hB : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci B) : A = B := by
  have hepi := epi_modulePullback_immersionConormalSheafMap sq a
  have hiso : IsIso ((modulePullbackComp a.toLRSHom.toShHom h.toLRSHom.toShHom).hom.app
      (immersionConormalSheaf k)) := inferInstance
  exact (cancel_epi _).mp ((cancel_epi _).mp (hA.trans hB.symm))

/-! ### Compatibility with the base restricts to an open of the ambient scheme -/

omit [IsImmersion i] in
/-- Naturality of the pullback composition isomorphism of `ι_{i⁻¹V}` and `a` at the canonical map
of conormal sheaves coming from the base. -/
private theorem modulePullbackComp_naturality_base (sq : IsPullback j h h' k) (V : X'.Opens) :
    (modulePullback ((i ⁻¹ᵁ V).ι ≫ a).toLRSHom.toShHom).map
          (immersionConormalSheafMap j k h h' (toShHom_square sq.w)) ≫
        (modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.app
          (immersionConormalSheaf j) =
      (modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.app
          ((modulePullback h.toLRSHom.toShHom).obj (immersionConormalSheaf k)) ≫
        (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
          ((modulePullback a.toLRSHom.toShHom).map
            (immersionConormalSheafMap j k h h' (toShHom_square sq.w))) :=
  (modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.naturality _

omit [IsImmersion i] [IsImmersion j] in
/-- The associativity coherence of the pullback composition isomorphism at the triple
`ι_{i⁻¹V}`, `a`, `h`. -/
private theorem modulePullbackComp_assoc_base (V : X'.Opens) :
    (modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom (a ≫ h).toLRSHom.toShHom).hom.app
          (immersionConormalSheaf k) ≫
        (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
          ((modulePullbackComp a.toLRSHom.toShHom h.toLRSHom.toShHom).hom.app
            (immersionConormalSheaf k)) =
      (modulePullbackComp ((i ⁻¹ᵁ V).ι ≫ a).toLRSHom.toShHom h.toLRSHom.toShHom).hom.app
          (immersionConormalSheaf k) ≫
        (modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.app
          ((modulePullback h.toLRSHom.toShHom).obj (immersionConormalSheaf k)) :=
  modulePullbackComp_assoc (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom h.toLRSHom.toShHom
    (immersionConormalSheaf k)

/-- The three factors of the base compatibility of `A`, pulled back along `ι_{i⁻¹V}` and merged
into the pullback of the canonical map of the square `i ≫ g' = (a ≫ h) ≫ k`. -/
private theorem base_merge (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens) :
    (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
          ((modulePullbackComp a.toLRSHom.toShHom h.toLRSHom.toShHom).hom.app
            (immersionConormalSheaf k)) ≫
        (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
            ((modulePullback a.toLRSHom.toShHom).map
              (immersionConormalSheafMap j k h h' (toShHom_square sq.w))) ≫
          (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map A =
      (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
        (immersionConormalSheafMap i k (a ≫ h) g' (toShHom_square ci)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map hA

/-- **Compatibility with the base restricts to an open of the ambient scheme.** If
`A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` is compatible with the base, then its restriction to an open `V` of
`X'`, in the sense of `Stacks.Thickenings.restrictConormalSheafMap`, is compatible with the base
for the restricted thickening `i ∣_ V` over `V.ι ≫ g'`. -/
theorem isBaseCompatibleConormalMap_restrict (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens) :
    IsBaseCompatibleConormalMap (i ∣_ V) j k h h' (V.ι ≫ g') ((i ⁻¹ᵁ V).ι ≫ a) sq.w
      (comm_restrict_base i k h g' a ci V) (restrictConormalSheafMap a A V) := by
  refine Eq.trans ?_ (immersionConormalSheafMap_comp (i ∣_ V) i k (i ⁻¹ᵁ V).ι V.ι
    (morphismRestrict_ι i V) (a ≫ h) g' ci).symm
  rw [restrictConormalSheafMap_eq a A V]
  exact base_shuffle
    (assoc_shuffle (modulePullbackComp_naturality_base sq V) (modulePullbackComp_assoc_base V))
    (base_merge sq ci hA V)

/-! ### The elementary description of the lifting sheaf -/

/-- **The conormal datum of a lift over the base is compatible with the base.** For a morphism
`b : V ⟶ Y'` over `Z'` restricting to `a` on `i⁻¹V`, the canonical map of conormal sheaves of the
square it forms is compatible with the base: stacking that square on the cartesian square gives
the square `(i ∣_ V) ≫ (V.ι ≫ g') = (ι_{i⁻¹V} ≫ a ≫ h) ≫ k`, whose canonical map does not
involve `b`.

This is the assertion of [Stacks Project, Tag 0CK2] that the composition
`g^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` "has to be the canonical map induced by `g'`", read for
the datum attached to an actual lift. -/
@[stacks 0CK2 "the composition g^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'} is the canonical map \
induced by g', for the datum of a lift"]
theorem isBaseCompatibleConormalMap_of_lift (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k) {V : X'.Opens} {b : V.toScheme ⟶ Y'}
    (hb₁ : b ≫ h' = V.ι ≫ g') (hb₂ : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j) :
    IsBaseCompatibleConormalMap (i ∣_ V) j k h h' (V.ι ≫ g') ((i ⁻¹ᵁ V).ι ≫ a) sq.w
      (comm_restrict_base i k h g' a ci V)
      (immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b (toShHom_square hb₂)) := by
  refine Eq.trans ?_ (immersionConormalSheafMap_congr (i ∣_ V) k
    (rfl : ((i ⁻¹ᵁ V).ι ≫ a) ≫ h = ((i ⁻¹ᵁ V).ι ≫ a) ≫ h) hb₁
    (toShHom_square (square_comp hb₂ sq.w))
    (toShHom_square (comm_restrict_base i k h g' a ci V))).symm
  rw [eqToHom_refl, Category.id_comp]
  exact (immersionConormalSheafMap_comp (i ∣_ V) j k ((i ⁻¹ᵁ V).ι ≫ a) b hb₂ h h' sq.w).symm

/-- **A conormal datum that admits a compatible lift is compatible with the base.** If some
morphism `b : V ⟶ Y'` out of an open `V` of `X'` is a compatible lift of `a` for the datum `A`,
then the restriction of `A` to `V` is compatible with the base: condition (3) of
[Stacks Project, Tag 04FI] identifies that restriction with the canonical map of the square `b`
forms, which is compatible with the base by
`Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift`.

This is the assertion of [Stacks Project, Tag 0CK2] that the composition
`g^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` *has to be* the canonical map induced by `g'`, read for
the given datum: wherever the sheaf of [Stacks Project, Tag 04FH] has a section, `A` is forced
to be base compatible, and by `Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap` that pins
it down. So base compatibility is not a restriction on the data the source considers; it is the
source's determination of `A` by `a`. -/
@[stacks 0CK2 "the composition g^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'} has to be the canonical \
map induced by g', for the given datum: a datum with a compatible lift over an open is base \
compatible there"]
theorem isBaseCompatibleConormalMap_of_isCompatibleLift (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i} {V : X'.Opens} {b : V.toScheme ⟶ Y'}
    (hb : IsCompatibleLift g' h' a A V b) :
    IsBaseCompatibleConormalMap (i ∣_ V) j k h h' (V.ι ≫ g') ((i ⁻¹ᵁ V).ι ≫ a) sq.w
      (comm_restrict_base i k h g' a ci V) (restrictConormalSheafMap a A V) := by
  obtain ⟨hb₂, hA⟩ := hb.2
  exact hA ▸ isBaseCompatibleConormalMap_of_lift sq ci hb.1 hb₂

/-- **The third condition of [Stacks Project, Tag 04FI] is automatic over a thickened base.** For
`A` compatible with the base, a morphism `b : V ⟶ Y'` out of an open `V` of `X'` is a compatible
lift of `a` exactly when it is a morphism over `Z'` restricting to `a` on `i⁻¹V`. -/
@[stacks 0CK2 "the conormal condition on a lift is automatic"]
theorem isCompatibleLift_iff_of_isBaseCompatible (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens)
    (b : V.toScheme ⟶ Y') :
    IsCompatibleLift g' h' a A V b ↔
      b ≫ h' = V.ι ≫ g' ∧ i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j := by
  refine ⟨fun hb => ⟨hb.1, hb.2.choose⟩, fun hb => ⟨hb.1, hb.2, ?_⟩⟩
  exact eq_of_isBaseCompatibleConormalMap sq (comm_restrict_base i k h g' a ci V)
    (isBaseCompatibleConormalMap_of_lift sq ci hb.1 hb.2)
    (isBaseCompatibleConormalMap_restrict sq ci hA V)

/-- **The sheaf of [Stacks Project, Tag 04FH] is the elementary rule over a thickened base.** For
`A` compatible with the base, the presheaf of compatible lifts of `a` is isomorphic to the
presheaf `Stacks.Thickenings.liftsOverBasePresheaf` of morphisms `V ⟶ Y'` over `Z'` restricting
to `a` on `i⁻¹V`, by the isomorphism which is the identity on underlying morphisms.

This is the description of the sheaf asserted by [Stacks Project, Tag 0CK2]. The simply
transitive action of `Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` on the elementary rule — the last
assertion of that remark — is
`Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBaseOfBase` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseAction`,
obtained by transporting the unrestricted [Stacks Project, Tag 04FJ] for the base `Z'` along
this isomorphism and along the identification `Ω_{Y/Z'} ≅ Ω_{Y/Z}` that holds because `k` is an
immersion. -/
@[stacks 0CK2 "the elementary description of the lifting sheaf"]
def compatibleLiftsPresheafIsoLiftsOverBasePresheafOfBase (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) :
    compatibleLiftsPresheaf g' h' a A ≅ liftsOverBasePresheaf i j g' h' a :=
  NatIso.ofComponents
    (fun V =>
      { hom := TypeCat.ofHom fun c =>
          ⟨c.1, (isCompatibleLift_iff_of_isBaseCompatible sq ci hA V.unop c.1).mp c.2⟩
        inv := TypeCat.ofHom fun c =>
          ⟨c.1, (isCompatibleLift_iff_of_isBaseCompatible sq ci hA V.unop c.1).mpr c.2⟩
        hom_inv_id := by ext c; exact Subtype.ext rfl
        inv_hom_id := by ext c; exact Subtype.ext rfl })
    fun f => by ext c; exact Subtype.ext rfl

/-- The isomorphism of [Stacks Project, Tag 0CK2] is the identity on underlying morphisms. -/
theorem compatibleLiftsPresheafIsoLiftsOverBasePresheafOfBase_hom_coe
    (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens)
    (c : compatibleLifts g' h' a A V) :
    (((compatibleLiftsPresheafIsoLiftsOverBasePresheafOfBase sq ci hA).hom.app (op V)) c).1
      = c.1 := rfl

end

end Stacks.Thickenings

end
