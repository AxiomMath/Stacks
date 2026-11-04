module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Full
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.Directedness
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two finite type quasi-coherent algebra sheaves are dominated by a third

Let `X` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras. Any two
quasi-coherent algebra sheaves of finite type mapping to `A` both map compatibly to a single
quasi-coherent algebra sheaf of finite type mapping to `A`, namely the pushed-forward structure
sheaf of the fibre product of their relative spectra. Consequently the finite type quasi-coherent
subalgebras of `A` form a filtered category, given the hypotheses `ImageIsQuasicoherent X` and
`ImageIsLocallySurjective X`.

## Main definitions

* `relativeSpecOver` and `relativeSpecOverIso`: the relative spectrum of a quasi-coherent
  algebra sheaf as an object over `X`, together with the identification of its pushed-forward
  structure sheaf with the algebra sheaf itself.
* `overHomOfSheafHom`: the morphism of schemes over `X` attached to a morphism of quasi-coherent
  algebra sheaves.
* `joinOver`, `joinProj₁`, `joinProj₂`, `joinLift`: the fibre product of two relative spectra
  over `X`, its two projections, and the morphism into it induced by a pair of morphisms of
  algebra sheaves into a common target.

## Main results

* `isFiniteType_pushforwardAlgebra_iff`: for an affine morphism `g` of schemes, the algebra
  sheaf `g_* 𝒪` is of finite type exactly when `g` is locally of finite type.
* `exists_dominating`: two quasi-coherent algebra sheaves of finite type mapping to a
  quasi-coherent `A` are dominated by a quasi-coherent algebra sheaf of finite type mapping to `A`.
* `exists_finiteType_receiving_pair`: two quasi-coherent algebra sheaves of finite type both map
  to a single quasi-coherent algebra sheaf of finite type.
* `exists_join`, `isFilteredOrEmpty`, `isFiltered`: any two finite type quasi-coherent
  subalgebras of `A` are contained in a third, and these subalgebras form a filtered category.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.AlgebraicGeometry.FiniteTypeDominating

/-! ### Finite type algebra sheaves and `LocallyOfFiniteType` -/

/-- If `g` is affine and locally of finite type, then the algebra sheaf `pushforwardAlgebra g` is
of finite type. -/
@[ega "I 6.3.3" "more general", ega "IV 1.3.6" "more general"]
theorem isFiniteType_pushforwardAlgebra {W X : Scheme.{u}} (g : W ⟶ X) [IsAffineHom g]
    [LocallyOfFiniteType g] : AlgebraSheaf.IsFiniteType (pushforwardAlgebra g) := by
  intro U hU
  have h : RingHom.FiniteType (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) g ‹_› ⟨U, hU⟩
      ⟨g ⁻¹ᵁ U, hU.preimage g⟩ le_rfl
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- A restriction map between affine opens of a scheme is of finite type. -/
theorem finiteType_presheaf_map {W : Scheme.{u}} {U V : W.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : V ≤ U) :
    RingHom.FiniteType (W.presheaf.map (homOfLE e).op).hom := by
  have h : RingHom.FiniteType (Scheme.Hom.appLE (𝟙 W) U V e).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (𝟙 W) inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  have h2 : Scheme.Hom.appLE (𝟙 W) U V e = W.presheaf.map (homOfLE e).op :=
    Category.id_comp _
  rwa [h2] at h

/-- An affine morphism `g` whose algebra sheaf `pushforwardAlgebra g` is of finite type is locally
of finite type. -/
theorem locallyOfFiniteType_of_isFiniteType_pushforwardAlgebra {W X : Scheme.{u}} (g : W ⟶ X)
    [IsAffineHom g] (h : AlgebraSheaf.IsFiniteType (pushforwardAlgebra g)) :
    LocallyOfFiniteType g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)]
  intro U V e
  exact (finiteType_presheaf_map (U.2.preimage g) V.2 e).comp (h U.1 U.2)

/-- For an affine morphism `g` of schemes, the algebra sheaf `pushforwardAlgebra g` is of finite
type if and only if `g` is locally of finite type. -/
theorem isFiniteType_pushforwardAlgebra_iff {W X : Scheme.{u}} (g : W ⟶ X) [IsAffineHom g] :
    AlgebraSheaf.IsFiniteType (pushforwardAlgebra g) ↔ LocallyOfFiniteType g :=
  ⟨locallyOfFiniteType_of_isFiniteType_pushforwardAlgebra g,
    fun _ ↦ isFiniteType_pushforwardAlgebra g⟩

/-! ### The relative spectrum as an object over the base -/

variable {X : Scheme.{u}}

/-- The relative spectrum of a quasi-coherent algebra sheaf, as an object over `X`. -/
@[sga "3 I 4.2" "partial"]
def relativeSpecOver (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] : Over X :=
  Over.mk (relativeSpecToBase A)

/-- The structure morphism of `relativeSpecOver A` is the structure morphism of the relative
spectrum. -/
theorem relativeSpecOver_hom (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] :
    (relativeSpecOver A).hom = relativeSpecToBase A :=
  rfl

/-- The structure morphism of `relativeSpecOver A` is affine. -/
instance isAffineHom_relativeSpecOver (A : AlgebraSheaf X)
    [AlgebraSheaf.IsQuasicoherent A] : IsAffineHom (relativeSpecOver A).hom :=
  isAffineHom_relativeSpecToBase A

/-- The pushed-forward structure sheaf of the relative spectrum `relativeSpecOver A` is
isomorphic to the algebra sheaf `A`. -/
def relativeSpecOverIso (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] :
    pushforwardAlgebra (relativeSpecOver A).hom ≅ A :=
  pushforwardAlgebraIso A

/-- **The relative spectrum of a finite type quasi-coherent algebra sheaf is locally of finite
type over the base.** -/
theorem locallyOfFiniteType_relativeSpecOver (A : AlgebraSheaf X)
    [AlgebraSheaf.IsQuasicoherent A] (hA : AlgebraSheaf.IsFiniteType A) :
    LocallyOfFiniteType (relativeSpecOver A).hom :=
  locallyOfFiniteType_of_isFiniteType_pushforwardAlgebra _
    (FiniteTypeSubalgebras.isFiniteType_of_iso (relativeSpecOverIso A).symm hA)

/-- The morphism `relativeSpecOver A ⟶ relativeSpecOver S` of schemes over `X` attached to a
morphism `s : S ⟶ A` of quasi-coherent algebra sheaves: the morphism over `X` inducing `s` on
pushed-forward structure sheaves, up to `relativeSpecOverIso`. -/
def overHomOfSheafHom {A S : AlgebraSheaf X} [AlgebraSheaf.IsQuasicoherent A]
    [AlgebraSheaf.IsQuasicoherent S] (s : S ⟶ A) :
    relativeSpecOver A ⟶ relativeSpecOver S :=
  overHomOfAlgebraHom ((relativeSpecOverIso S).hom ≫ s ≫ (relativeSpecOverIso A).inv)

/-- `overHomOfSheafHom s` induces `s` back, up to the two identifications. -/
theorem pushforwardAlgebraMap_overHomOfSheafHom {A S : AlgebraSheaf X}
    [AlgebraSheaf.IsQuasicoherent A] [AlgebraSheaf.IsQuasicoherent S] (s : S ⟶ A) :
    pushforwardAlgebraMap (overHomOfSheafHom s)
      = (relativeSpecOverIso S).hom ≫ s ≫ (relativeSpecOverIso A).inv :=
  pushforwardAlgebraMap_overHomOfAlgebraHom _

/-! ### The fibre product of two relative spectra -/

variable (S T : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent S] [AlgebraSheaf.IsQuasicoherent T]

/-- The fibre product of the relative spectra of `S` and `T`, as an object over `X`. -/
def joinOver : Over X :=
  Over.mk (pullback.fst (relativeSpecOver S).hom (relativeSpecOver T).hom ≫
    (relativeSpecOver S).hom)

/-- The structure morphism of the fibre product `joinOver S T` is affine. -/
instance isAffineHom_joinOver : IsAffineHom (joinOver S T).hom :=
  haveI : IsAffineHom (pullback.fst (relativeSpecOver S).hom (relativeSpecOver T).hom) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (relativeSpecOver S).hom (relativeSpecOver T).hom).flip
      inferInstance
  inferInstanceAs (IsAffineHom (pullback.fst (relativeSpecOver S).hom (relativeSpecOver T).hom ≫
    (relativeSpecOver S).hom))

/-- If `S` and `T` are of finite type, the structure morphism of the fibre product
`joinOver S T` is locally of finite type. -/
theorem locallyOfFiniteType_joinOver (hS : AlgebraSheaf.IsFiniteType S)
    (hT : AlgebraSheaf.IsFiniteType T) : LocallyOfFiniteType (joinOver S T).hom :=
  have := locallyOfFiniteType_relativeSpecOver S hS
  have := locallyOfFiniteType_relativeSpecOver T hT
  inferInstanceAs (LocallyOfFiniteType
    (pullback.fst (relativeSpecOver S).hom (relativeSpecOver T).hom ≫ (relativeSpecOver S).hom))

/-- The first projection of the fibre product, as a morphism over `X`. -/
def joinProj₁ : joinOver S T ⟶ relativeSpecOver S :=
  Over.homMk (pullback.fst _ _) rfl

/-- The second projection of the fibre product, as a morphism over `X`. -/
def joinProj₂ : joinOver S T ⟶ relativeSpecOver T :=
  Over.homMk (pullback.snd _ _) pullback.condition.symm

variable {S T}

/-- **The morphism into the fibre product induced by a pair of morphisms of algebra sheaves into
a common quasi-coherent target.** -/
def joinLift {A : AlgebraSheaf X} [AlgebraSheaf.IsQuasicoherent A] (s : S ⟶ A) (t : T ⟶ A) :
    relativeSpecOver A ⟶ joinOver S T :=
  Over.homMk
    (pullback.lift (overHomOfSheafHom s).left (overHomOfSheafHom t).left
      ((Over.w (overHomOfSheafHom s)).trans (Over.w (overHomOfSheafHom t)).symm))
    (by
      change pullback.lift (overHomOfSheafHom s).left (overHomOfSheafHom t).left _ ≫
        (pullback.fst (relativeSpecOver S).hom (relativeSpecOver T).hom ≫
          (relativeSpecOver S).hom) = _
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w (overHomOfSheafHom s))

/-- `joinLift` followed by the first projection is the morphism attached to `s`. -/
theorem joinLift_proj₁ {A : AlgebraSheaf X} [AlgebraSheaf.IsQuasicoherent A] (s : S ⟶ A)
    (t : T ⟶ A) : joinLift s t ≫ joinProj₁ S T = overHomOfSheafHom s := by
  ext
  exact pullback.lift_fst _ _ _

/-- `joinLift` followed by the second projection is the morphism attached to `t`. -/
theorem joinLift_proj₂ {A : AlgebraSheaf X} [AlgebraSheaf.IsQuasicoherent A] (s : S ⟶ A)
    (t : T ⟶ A) : joinLift s t ≫ joinProj₂ S T = overHomOfSheafHom t := by
  ext
  exact pullback.lift_snd _ _ _

/-! ### The domination -/

/-- **The factorisation, one side at a time.**  If a morphism `q` out of an object `OW` over `X`
is cut out of `overHomOfSheafHom s` by a morphism `lam` into `OW`, then the morphism of algebra
sheaves `S ⟶ pushforwardAlgebra OW.hom` attached to `q` composed with the one attached to `lam`
recovers `s`. -/
theorem comp_eq_of_factor {A S : AlgebraSheaf X} [AlgebraSheaf.IsQuasicoherent A]
    [AlgebraSheaf.IsQuasicoherent S] (s : S ⟶ A) {OW : Over X} (q : OW ⟶ relativeSpecOver S)
    (lam : relativeSpecOver A ⟶ OW) (hl : lam ≫ q = overHomOfSheafHom s) :
    ((relativeSpecOverIso S).inv ≫ pushforwardAlgebraMap q) ≫
      (pushforwardAlgebraMap lam ≫ (relativeSpecOverIso A).hom) = s := by
  have key : pushforwardAlgebraMap q ≫ pushforwardAlgebraMap lam
      = (relativeSpecOverIso S).hom ≫ s ≫ (relativeSpecOverIso A).inv := by
    rw [← pushforwardAlgebraMap_comp, hl, pushforwardAlgebraMap_overHomOfSheafHom]
  rw [Category.assoc, ← Category.assoc (pushforwardAlgebraMap q), key]
  simp

/-- The pushed-forward structure sheaf of `joinOver S T` is quasi-coherent, and of finite type if
`S` and `T` are. -/
private theorem isQuasicoherent_and_isFiniteType_pushforwardAlgebra_joinOver
    (hS : AlgebraSheaf.IsFiniteType S) (hT : AlgebraSheaf.IsFiniteType T) :
    AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra (joinOver S T).hom) ∧
      AlgebraSheaf.IsFiniteType (pushforwardAlgebra (joinOver S T).hom) :=
  have := locallyOfFiniteType_joinOver S T hS hT
  ⟨isQuasicoherent_pushforwardAlgebra _, isFiniteType_pushforwardAlgebra _⟩

/-- **Two quasi-coherent algebra sheaves of finite type mapping to a quasi-coherent algebra sheaf
`A` are dominated by a quasi-coherent algebra sheaf of finite type mapping to `A`.** The
dominating object is the pushed-forward structure sheaf of the fibre product of the relative
spectra of `S` and `T`. -/
theorem exists_dominating (A S T : AlgebraSheaf X) (s : S ⟶ A) (t : T ⟶ A)
    (hA : AlgebraSheaf.IsQuasicoherent A)
    (hS : AlgebraSheaf.IsQuasicoherent S) (hSft : AlgebraSheaf.IsFiniteType S)
    (hT : AlgebraSheaf.IsQuasicoherent T) (hTft : AlgebraSheaf.IsFiniteType T) :
    ∃ (C : AlgebraSheaf X) (c : C ⟶ A), AlgebraSheaf.IsQuasicoherent C ∧
      AlgebraSheaf.IsFiniteType C ∧ (∃ u : S ⟶ C, u ≫ c = s) ∧ (∃ v : T ⟶ C, v ≫ c = t) := by
  obtain ⟨hq, hf⟩ := isQuasicoherent_and_isFiniteType_pushforwardAlgebra_joinOver hSft hTft
  refine ⟨pushforwardAlgebra (joinOver S T).hom,
    pushforwardAlgebraMap (joinLift s t) ≫ (relativeSpecOverIso A).hom, hq, hf, ?_, ?_⟩
  · exact ⟨_, comp_eq_of_factor s _ _ (joinLift_proj₁ s t)⟩
  · exact ⟨_, comp_eq_of_factor t _ _ (joinLift_proj₂ s t)⟩

/-- **The part of the domination that does not mention `A` at all.**  Two quasi-coherent algebra
sheaves of finite type both map to a *single* quasi-coherent algebra sheaf of finite type, namely
the pushed-forward structure sheaf of the fibre product of their relative spectra. -/
theorem exists_finiteType_receiving_pair (S T : AlgebraSheaf X)
    (hS : AlgebraSheaf.IsQuasicoherent S) (hSft : AlgebraSheaf.IsFiniteType S)
    (hT : AlgebraSheaf.IsQuasicoherent T) (hTft : AlgebraSheaf.IsFiniteType T) :
    ∃ C : AlgebraSheaf X, AlgebraSheaf.IsQuasicoherent C ∧ AlgebraSheaf.IsFiniteType C ∧
      Nonempty (S ⟶ C) ∧ Nonempty (T ⟶ C) := by
  obtain ⟨hq, hf⟩ := isQuasicoherent_and_isFiniteType_pushforwardAlgebra_joinOver hSft hTft
  refine ⟨pushforwardAlgebra (joinOver S T).hom, hq, hf, ?_, ?_⟩
  · exact ⟨(relativeSpecOverIso S).inv ≫ pushforwardAlgebraMap (joinProj₁ S T)⟩
  · exact ⟨(relativeSpecOverIso T).inv ≫ pushforwardAlgebraMap (joinProj₂ S T)⟩

/-! ### Directedness -/

/-- **Any two finite type quasi-coherent subalgebras of a quasi-coherent algebra sheaf `A` are
contained in a third**, given the hypotheses `ImageIsQuasicoherent X` and
`ImageIsLocallySurjective X`. -/
theorem exists_join (h₁ : FiniteTypeSubalgebras.ImageIsQuasicoherent X)
    (h₂ : FiniteTypeSubalgebras.ImageIsLocallySurjective X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A)
    (B C : FiniteTypeSubalgebras.FiniteTypeSubalgebra A) :
    ∃ D : FiniteTypeSubalgebras.FiniteTypeSubalgebra A, B.obj ≤ D.obj ∧ C.obj ≤ D.obj := by
  obtain ⟨E, c, hEqc, hEft, ⟨u, hu⟩, ⟨v, hv⟩⟩ :=
    exists_dominating A _ _ B.obj.arrow C.obj.arrow hA B.property.1 B.property.2
      C.property.1 C.property.2
  refine ⟨FiniteTypeSubalgebras.ofImage h₁ h₂ c hEqc hA hEft, ?_, ?_⟩
  · exact Subobject.le_mk_of_comm (u ≫ factorThruImage c)
      (by rw [Category.assoc, image.fac, hu])
  · exact Subobject.le_mk_of_comm (v ≫ factorThruImage c)
      (by rw [Category.assoc, image.fac, hv])

/-- The finite type quasi-coherent subalgebras of a quasi-coherent algebra sheaf form a filtered
or empty category, given the hypotheses `ImageIsQuasicoherent X` and
`ImageIsLocallySurjective X`. -/
theorem isFilteredOrEmpty (h₁ : FiniteTypeSubalgebras.ImageIsQuasicoherent X)
    (h₂ : FiniteTypeSubalgebras.ImageIsLocallySurjective X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) :
    IsFilteredOrEmpty (FiniteTypeSubalgebras.FiniteTypeSubalgebra A) :=
  FiniteTypeSubalgebras.isFilteredOrEmpty_of_exists_join A (exists_join h₁ h₂ A hA)

/-- **The finite type quasi-coherent subalgebras of a quasi-coherent algebra sheaf form a filtered
category**, given the hypotheses `ImageIsQuasicoherent X` and `ImageIsLocallySurjective X`. -/
theorem isFiltered (h₁ : FiniteTypeSubalgebras.ImageIsQuasicoherent X)
    (h₂ : FiniteTypeSubalgebras.ImageIsLocallySurjective X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) :
    IsFiltered (FiniteTypeSubalgebras.FiniteTypeSubalgebra A) :=
  FiniteTypeSubalgebras.isFiltered_of_exists_join A
    (FiniteTypeSubalgebras.nonempty_finiteTypeSubalgebra h₁ h₂ A hA) (exists_join h₁ h₂ A hA)

end Stacks.AlgebraicGeometry.FiniteTypeDominating

end
