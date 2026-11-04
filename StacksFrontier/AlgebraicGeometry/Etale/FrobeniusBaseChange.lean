module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.RelativeFrobenius
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.Frobenius

/-!
# Frobenius base change of an étale scheme over a ring

Let `p` be a prime number, let `A` be a commutative ring in which `p` vanishes and let
`F : A → A`, `a ↦ aᵖ`, be its Frobenius endomorphism. For a scheme `V` over `Spec A` the
Frobenius twist of `V` is the fibre product `V ×_{Spec A, Spec F} Spec A`, regarded as a scheme
over `Spec A` through its second projection, and the relative Frobenius of `V` is the canonical
morphism from `V` to that twist: the morphism whose first projection is the absolute Frobenius of
`V` and whose second projection is the structure morphism of `V`. When `V` is étale over `Spec A`
the relative Frobenius is an isomorphism, so the Frobenius twist of an étale `A`-scheme is
canonically isomorphic to it over `Spec A`; equivalently, the square formed by the absolute
Frobenius of `V`, the structure morphism of `V` and `Spec F` is Cartesian.

For `V` quasi-compact, quasi-separated and étale over `Spec A` that Cartesian square yields an
isomorphism

`RΓ(V, 𝒪_V) ⊗^L_{A, F} A ≅ RΓ(V, 𝒪_V)`

in `D(A)`, given cohomology and base change for the structure sheaf over an affine base.

## Main definitions

* `Stacks.EtaleFrobenius.frobeniusTwistComparison` — the relative Frobenius
  `V ⟶ V ×_{Spec A, Spec F} Spec A`, with the Frobenius of `Spec A` spelled as `Spec F`.
* `Stacks.EtaleFrobenius.frobeniusTwistIso` — that morphism as an isomorphism over `Spec A`,
  for `V` étale over `Spec A`.
* `Stacks.EtaleFrobenius.derivedStructureSheaf` — the structure sheaf of a scheme, placed in
  degree zero of the unbounded derived category of its modules.
* `Stacks.EtaleFrobenius.DerivedGlobalSectionsBaseChange` — cohomology and base change for the
  structure sheaf of a flat quasi-compact quasi-separated scheme over an affine base: for every
  ring map `φ : A → A'` and every Cartesian square over `Spec φ`, derived extension of scalars
  along `φ` carries the derived global sections of the source to those of the base change.

## Main results

* `Stacks.EtaleFrobenius.specMap_frobeniusOfNatCastEqZero` identifies the absolute Frobenius of
  `Spec A` with `Spec F`.
* `Stacks.EtaleFrobenius.isIso_frobeniusTwistComparison` states that the relative Frobenius of an
  étale `A`-scheme is an isomorphism.
* `Stacks.EtaleFrobenius.isPullback_absoluteFrobenius`: for `V` étale over `Spec A` the absolute
  Frobenius of `V` exhibits `V` as the fibre product `V ×_{Spec A, Spec F} Spec A`.
* `Stacks.EtaleFrobenius.nonempty_extendScalarsDerived_derivedGlobalSections_iso`:
  `RΓ(V, 𝒪_V) ⊗^L_{A, F} A ≅ RΓ(V, 𝒪_V)` for `V` quasi-compact, quasi-separated and étale over
  `Spec A`.

## References

* [Stacks Project, Tag 0EC9](https://stacks.math.columbia.edu/tag/0EC9)
* [Stacks Project, Tag 0EBS](https://stacks.math.columbia.edu/tag/0EBS)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0CC9](https://stacks.math.columbia.edu/tag/0CC9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Frobenius

universe u

namespace Stacks.EtaleFrobenius

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp0 : (p : A) = 0)
  {V : Scheme.{u}} (f : V ⟶ Spec (.of A))

/-- The spectrum of the Frobenius endomorphism of a ring in which `p` vanishes is the absolute
Frobenius of its spectrum. -/
theorem specMap_frobeniusOfNatCastEqZero (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (hp0 : (p : A) = 0) :
    Spec.map (CommRingCat.ofHom
        (Stacks.LocalCohomology.frobeniusOfNatCastEqZero A p Fact.out hp0)) =
      absoluteFrobenius (Spec (.of A)) p (isInCharacteristic_spec A p hp0) := by
  refine (specMap_eq_absoluteFrobeniusPow _ p 1 (isInCharacteristic_spec A p hp0)
    (fun a => by simp)).trans ?_
  show End.asHom ((End.of (absoluteFrobenius (Spec (.of A)) p _)) ^ 1) = _
  rw [pow_one]

/-- The absolute Frobenius of a scheme over `Spec A` lies over the spectrum of the Frobenius
of `A`. -/
theorem absoluteFrobenius_comp :
    absoluteFrobenius V p (isInCharacteristic_of_hom f p (isInCharacteristic_spec A p hp0)) ≫ f =
      f ≫ Spec.map (CommRingCat.ofHom
        (Stacks.LocalCohomology.frobeniusOfNatCastEqZero A p Fact.out hp0)) := by
  rw [specMap_frobeniusOfNatCastEqZero]
  exact absoluteFrobenius_naturality f p
    (isInCharacteristic_of_hom f p (isInCharacteristic_spec A p hp0))
    (isInCharacteristic_spec A p hp0)

/-- **The relative Frobenius of a scheme over a ring in which `p` vanishes.** The canonical
morphism from `V` to its Frobenius twist `V ×_{Spec A, Spec F} Spec A`: its first projection is
the absolute Frobenius of `V` and its second projection is the structure morphism of `V`. -/
@[sga "3 VIIA 4.1" "special case",
  sga "3 VIIA 4.1.3" "special case",
  sga "5 XII 7.3" "special case",
  sga "5 XV 1.Definition3" "special case"]
def frobeniusTwistComparison :
    V ⟶ pullback f (Spec.map (CommRingCat.ofHom
      (Stacks.LocalCohomology.frobeniusOfNatCastEqZero A p Fact.out hp0))) :=
  pullback.lift
    (absoluteFrobenius V p (isInCharacteristic_of_hom f p (isInCharacteristic_spec A p hp0))) f
    (absoluteFrobenius_comp p hp0 f)

/-- The first projection of the relative Frobenius is the absolute Frobenius of `V`. -/
@[simp, reassoc]
theorem frobeniusTwistComparison_fst :
    frobeniusTwistComparison p hp0 f ≫ pullback.fst _ _ =
      absoluteFrobenius V p (isInCharacteristic_of_hom f p (isInCharacteristic_spec A p hp0)) :=
  pullback.lift_fst _ _ _

/-- The second projection of the relative Frobenius is the structure morphism of `V`. -/
@[simp, reassoc]
theorem frobeniusTwistComparison_snd :
    frobeniusTwistComparison p hp0 f ≫ pullback.snd _ _ = f :=
  pullback.lift_snd _ _ _

/-- **Stacks Project, Tag 0EBS.** The relative Frobenius of an étale scheme over a ring in which
`p` vanishes is an isomorphism. -/
@[sga "4½ Fonctions_L 3.4" "special case"]
instance isIso_frobeniusTwistComparison [Etale f] :
    IsIso (frobeniusTwistComparison p hp0 f) := by
  have hS := isInCharacteristic_spec A p hp0
  have hEtale : Etale (CategoryTheory.Over.mk f).hom := by change Etale f; infer_instance
  have key : ∀ g : Spec (.of A) ⟶ Spec (.of A), g = absoluteFrobenius (Spec (.of A)) p hS →
      ∀ c : V ⟶ pullback f g,
        c ≫ pullback.fst _ _ =
          absoluteFrobenius V p (isInCharacteristic_of_hom f p hS) →
        c ≫ pullback.snd _ _ = f → IsIso c := by
    intro g hg c h₁ h₂
    subst hg
    have hrel : IsIso ((CategoryTheory.Over.forget (Spec (.of A))).map
        (relativeFrobenius (Spec (.of A)) p hS (CategoryTheory.Over.mk f))) := inferInstance
    have hc : c = (relativeFrobenius (Spec (.of A)) p hS (CategoryTheory.Over.mk f)).left :=
      pullback.hom_ext
        (h₁.trans (relativeFrobenius_fst (Spec (.of A)) p hS (CategoryTheory.Over.mk f)).symm)
        (h₂.trans (relativeFrobenius_snd (Spec (.of A)) p hS (CategoryTheory.Over.mk f)).symm)
    rw [hc]
    exact hrel
  exact key _ (specMap_frobeniusOfNatCastEqZero A p hp0) _
    (frobeniusTwistComparison_fst p hp0 f) (frobeniusTwistComparison_snd p hp0 f)

/-- For a scheme `V` étale over `Spec A`, where `p` vanishes in `A`, the relative Frobenius
identifies `V` with its Frobenius twist `V ×_{Spec A, Spec F} Spec A` over `Spec A`. -/
@[sga "4½ Fonctions_L 3.4" "special case"]
def frobeniusTwistIso [Etale f] :
    CategoryTheory.Over.mk f ≅ CategoryTheory.Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom
        (Stacks.LocalCohomology.frobeniusOfNatCastEqZero A p Fact.out hp0)))) :=
  have : IsIso ((CategoryTheory.Over.forget (Spec (.of A))).map
      (CategoryTheory.Over.homMk (frobeniusTwistComparison p hp0 f)
        (frobeniusTwistComparison_snd p hp0 f) :
          CategoryTheory.Over.mk f ⟶ CategoryTheory.Over.mk (pullback.snd _ _))) :=
    isIso_frobeniusTwistComparison p hp0 f
  have : IsIso (CategoryTheory.Over.homMk (frobeniusTwistComparison p hp0 f)
      (frobeniusTwistComparison_snd p hp0 f) :
        CategoryTheory.Over.mk f ⟶ CategoryTheory.Over.mk (pullback.snd _ _)) :=
    isIso_of_reflects_iso _ (CategoryTheory.Over.forget _)
  asIso (CategoryTheory.Over.homMk (frobeniusTwistComparison p hp0 f)
    (frobeniusTwistComparison_snd p hp0 f))

/-- The underlying morphism of schemes of the Frobenius twist isomorphism is the relative
Frobenius. -/
@[simp]
theorem frobeniusTwistIso_hom_left [Etale f] :
    (frobeniusTwistIso p hp0 f).hom.left = frobeniusTwistComparison p hp0 f := rfl

/-- **The absolute Frobenius square of an étale scheme is Cartesian.** For `V` étale over
`Spec A`, where `p` vanishes in `A`, the absolute Frobenius of `V` and the structure morphism of
`V` exhibit `V` as the fibre product `V ×_{Spec A, Spec F} Spec A`. -/
@[sga "4½ Rapport 1.2" "special case"]
theorem isPullback_absoluteFrobenius [Etale f] :
    IsPullback
      (absoluteFrobenius V p (isInCharacteristic_of_hom f p (isInCharacteristic_spec A p hp0)))
      f f
      (Spec.map (CommRingCat.ofHom
        (Stacks.LocalCohomology.frobeniusOfNatCastEqZero A p Fact.out hp0))) :=
  IsPullback.of_iso_pullback ⟨absoluteFrobenius_comp p hp0 f⟩
    (asIso (frobeniusTwistComparison p hp0 f))
    (frobeniusTwistComparison_fst p hp0 f) (frobeniusTwistComparison_snd p hp0 f)

/-- The structure sheaf of a scheme, as the object of the unbounded derived category of its
sheaves of modules concentrated in degree zero. -/
abbrev derivedStructureSheaf (W : Scheme.{u}) : DerivedCategory W.Modules :=
  (DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)

/-- **Cohomology and base change for the structure sheaf over an affine base.** For every ring
map `φ : A ⟶ A'`, every flat quasi-compact quasi-separated `h : W ⟶ Spec A` and every Cartesian
square exhibiting `h' : W' ⟶ Spec A'` as the base change of `h` along `Spec φ`, the derived base
change `RΓ(W, 𝒪_W) ⊗^L_{A, φ} A'` of the derived global sections of `W` is the derived global
sections `RΓ(W', 𝒪_{W'})` of the base change. -/
abbrev DerivedGlobalSectionsBaseChange (A : Type u) [CommRing A] : Prop :=
  ∀ (A' : Type u) [CommRing A'] (φ : A →+* A') {W W' : Scheme.{u}} (h : W ⟶ Spec (.of A))
    (h' : W' ⟶ Spec (.of A')) (q : W' ⟶ W),
    IsPullback q h' h (Spec.map (CommRingCat.ofHom φ)) →
    QuasiCompact h → QuasiSeparated h → Flat h →
    Nonempty ((StacksDraft.PseudoCoherence.extendScalarsDerived φ).obj
        ((derivedGlobalSectionsOver h).obj (derivedStructureSheaf W)) ≅
      (derivedGlobalSectionsOver h').obj (derivedStructureSheaf W'))

/-- Let `p` be a prime number, let `A` be a commutative ring in which `p` vanishes and let
`F : A → A`, `a ↦ aᵖ`, be its Frobenius endomorphism. Assuming cohomology and base change
`Stacks.EtaleFrobenius.DerivedGlobalSectionsBaseChange A`, for a quasi-compact, quasi-separated,
étale scheme `V` over `Spec A` there is an isomorphism

`RΓ(V, 𝒪_V) ⊗^L_{A, F} A ≅ RΓ(V, 𝒪_V)`

in `D(A)`. -/
@[stacks 0EC9 "cohomology and base change is the explicit hypothesis \
`Stacks.EtaleFrobenius.DerivedGlobalSectionsBaseChange A`, namely Stacks 08IB for the structure \
sheaf over an affine base: for every ring map out of `A` and every Cartesian square over its \
spectrum whose left-hand morphism is flat, quasi-compact and quasi-separated, derived extension \
of scalars carries the derived global sections of the source to those of the base change. The \
library carries the base change morphism of Stacks 08HY but not its invertibility in \
Tor-independent generality, whose globalization step is Stacks 0DJ9. Everything else is proved: \
the Cartesian square supplied to that hypothesis is the absolute Frobenius square of `V`, \
Cartesian by Stacks 0EBS"]
theorem nonempty_extendScalarsDerived_derivedGlobalSections_iso
    [QuasiCompact f] [QuasiSeparated f] [Etale f]
    (hbc : DerivedGlobalSectionsBaseChange A) :
    Nonempty ((StacksDraft.PseudoCoherence.extendScalarsDerived
        (Stacks.LocalCohomology.frobeniusOfNatCastEqZero A p Fact.out hp0)).obj
        ((derivedGlobalSectionsOver f).obj (derivedStructureSheaf V)) ≅
      (derivedGlobalSectionsOver f).obj (derivedStructureSheaf V)) :=
  hbc A _ f f _ (isPullback_absoluteFrobenius p hp0 f) inferInstance inferInstance inferInstance

end Stacks.EtaleFrobenius

end
