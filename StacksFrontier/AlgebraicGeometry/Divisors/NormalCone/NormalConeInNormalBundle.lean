module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.SymmetricQuotient
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraHomComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normal cone inside the normal bundle

Let `i : Z ⟶ X` be an immersion of schemes with conormal algebra `𝒞_{Z/X,*}` and conormal sheaf
`𝒞_{Z/X} = 𝒞_{Z/X,1}`. The *normal cone* of `Z` in `X` is the relative spectrum
`C_ZX = Spec_Z(𝒞_{Z/X,*})` and the *normal bundle* is `N_ZX = Spec_Z(Sym(𝒞_{Z/X}))`. The
canonical map of graded algebras `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` therefore induces a morphism

`C_ZX ⟶ N_ZX`

of schemes over `Z`, and this file constructs it.

Two steps are needed. The relative spectrum consumes a sheaf of *commutative* algebras over the
structure sheaf, so the conormal algebra has to be presented in that shape: that is
`Stacks.RelativeSpec.gradedAlgebraSheaf`, whose one input is commutativity of the homogeneous
multiplication in every pair of *integer* degrees. Commutativity in nonnegative degrees is
`Stacks.Conormal.ConormalAlgebraData.mul_comm`, and the negative pieces of the conormal algebra
are zero objects, so `ConormalAlgebraData.mul_comm_int` extends it. The canonical map is then
carried along by functoriality of the ungraded realization and the relative spectrum.

## Main definitions

* `Stacks.Conormal.conormalSheafDegreeOne`: `𝒞_{Z/X}`, the degree-one piece of the conormal
  algebra, which is quasi-coherent.
* `Stacks.Conormal.conormalAlgebraSheaf`: **`𝒞_{Z/X,*}` as a sheaf of commutative `𝒪_Z`-algebras**,
  the shape the relative spectrum takes as input.
* `Stacks.Conormal.normalBundleAlgebra`: `Sym(𝒞_{Z/X})` in the same shape, so that `N_ZX` is
  `AlgebraicGeometry.Scheme.Modules.vectorBundle` of `𝒞_{Z/X}`.
* `Stacks.Conormal.conormalSymmetricAlgebraSheafHom`: the canonical map of *algebra* sheaves
  `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` induced by the canonical map of graded algebras.
* `Stacks.Conormal.normalCone` and `normalConeToBase`: **`C_ZX = Spec_Z(𝒞_{Z/X,*})`** and its
  projection to `Z`.
* `Stacks.Conormal.normalConeToNormalBundle`: **the canonical morphism `C_ZX ⟶ N_ZX`.**

## Main results

* `Stacks.Conormal.ConormalAlgebraData.eq_zero_of_neg`: a homogeneous section of the conormal
  algebra in a negative degree vanishes.
* `Stacks.Conormal.ConormalAlgebraData.mul_comm_int`: **homogeneous multiplication in the conormal
  algebra is commutative in every pair of integer degrees.**
* `Stacks.Conormal.isQuasicoherent_conormalAlgebraSheaf`: **`𝒞_{Z/X,*}` is quasi-coherent as a
  sheaf of algebras**, which is what the relative spectrum requires of it.
* `Stacks.Conormal.normalConeToNormalBundle_toBase`: **the canonical morphism is a morphism over
  `Z`**, compatibly with the two projections.
* `Stacks.Conormal.ι_normalConeToNormalBundle` and `normalConeToNormalBundle_appLE`: **the
  characterising property of the canonical morphism**, chart by chart over an affine open of `Z`
  and on sections.

## Implementation notes

### Quasi-coherence of the two algebra sheaves

Both relative spectra need their algebra sheaf to be quasi-coherent, and both are: `Sym(𝒞_{Z/X})`
by `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf`, which is Tag 01CK in
the shape the relative spectrum consumes, and `𝒞_{Z/X,*}` by
`Stacks.Conormal.isQuasicoherent_conormalAlgebraSheaf` below. The latter composes three facts: the
conormal algebra is concentrated in nonnegative degrees, so
`Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule` identifies the module underlying its
ungraded realization with the coproduct of its homogeneous pieces; those pieces are quasi-coherent
by Tag 0630; and quasi-coherence on a scheme is stable under coproducts, which is
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma` once the index type `ℕ` has
been shrunk into the module universe.

### Where Tag 0637 is registered

Tag 0637 is the displayed arrow `C_ZX ⟶ N_ZX` of the section on the normal cone, and the sentence
carrying it asserts three things: that the canonical surjection of graded algebras **defines** a
morphism `C_ZX ⟶ N_ZX`, that this morphism is a **closed immersion**, and that it is a morphism
**of cones over `Z`**. The first is proved here, over `Z` and with its characterising property,
and the attributes below are registered on it. The closed-immersion clause is
`Stacks.Conormal.isClosedImmersion_normalConeToNormalBundle` of
`StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ConeEmbedding`: over an affine open the
morphism is the spectrum of the map on sections, which is surjective by Tag 0632. The cone clause,
together with the whole statement, is
`Stacks.Conormal.isClosedImmersion_normalConeToNormalBundle_and_coneHom` of
`StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeConeHom`, built on the morphism of
cones `Stacks.Conormal.normalConeToNormalBundleConeHom`.

## References

* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

/-! ### Commutativity in every pair of integer degrees -/

/-- Two elements of the members of a family indexed by the integers are heterogeneously equal as
soon as their indices agree and both are the distinguished element of their member. -/
private theorem heq_of_eq_pt {F : ℤ → Type u} (z : ∀ k, F k) {k l : ℤ} (e : k = l) {a : F k}
    {b : F l} (ha : a = z k) (hb : b = z l) : HEq a b := by
  subst e
  exact heq_of_eq (ha.trans hb.symm)

/-- **A homogeneous section of the conormal algebra in a negative degree vanishes**, over any open
of the source: the piece of that degree is a zero object, so its identity is the zero morphism. -/
theorem ConormalAlgebraData.eq_zero_of_neg {i : Z ⟶ X} [IsImmersion i] (D : ConormalAlgebraData i)
    (n : ℤ) (hn : n < 0) (W : (Opens ↥Z)ᵒᵖ) (a : (D.algebra.piece n).val.obj W) : a = 0 := by
  have h : (𝟙 (D.algebra.piece n) : D.algebra.piece n ⟶ D.algebra.piece n) = 0 :=
    (D.negative_isZero n hn).eq_of_src _ _
  have h2 := congrArg
    (fun φ : D.algebra.piece n ⟶ D.algebra.piece n =>
      PresheafOfModules.Hom.app φ.val W a) h
  have hz : PresheafOfModules.Hom.app (0 : D.algebra.piece n ⟶ D.algebra.piece n).val W a = 0 :=
    (SheafOfModules.mem_kerSubmodule 0 W a).mp rfl
  exact h2.trans hz

/-- **Homogeneous multiplication in the conormal algebra of an immersion is commutative in every
pair of integer degrees.** In nonnegative degrees this is
`Stacks.Conormal.ConormalAlgebraData.mul_comm`; if either degree is negative both products
vanish, being biadditive in a section of a zero piece. -/
theorem ConormalAlgebraData.mul_comm_int {i : Z ⟶ X} [IsImmersion i] (D : ConormalAlgebraData i)
    (m n : ℤ) (W : (Opens ↥Z)ᵒᵖ) (a : (D.algebra.piece m).val.obj W)
    (b : (D.algebra.piece n).val.obj W) :
    HEq ((D.algebra.mul m n).app W a b) ((D.algebra.mul n m).app W b a) := by
  let z (k : ℤ) : (D.algebra.piece k).val.obj W := 0
  rcases lt_or_ge m 0 with hm | hm
  · have := D.eq_zero_of_neg m hm W a
    exact heq_of_eq_pt z (add_comm m n) (by simp [this, z]) (by simp [this, z])
  rcases lt_or_ge n 0 with hn | hn
  · have := D.eq_zero_of_neg n hn W b
    exact heq_of_eq_pt z (add_comm m n) (by simp [this, z]) (by simp [this, z])
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact D.mul_comm p q W.unop a b

/-! ### The conormal algebra and the symmetric algebra as algebra sheaves -/

/-- `𝒞_{Z/X}`, the conormal sheaf of an immersion, taken as the degree-one piece of its conormal
algebra; this is the identification the source itself makes. -/
abbrev conormalSheafDegreeOne (i : Z ⟶ X) [IsImmersion i] : SheafOfModules.{u} Z.ringCatSheaf :=
  (conormalAlgebra i).algebra.piece 1

/-- The conormal sheaf is quasi-coherent, being a homogeneous piece of the conormal algebra. -/
instance isQuasicoherent_conormalSheafDegreeOne (i : Z ⟶ X) [IsImmersion i] :
    (conormalSheafDegreeOne i).IsQuasicoherent :=
  (conormalAlgebra i).isQuasicoherent 1

/-- **`𝒞_{Z/X,*}` as a sheaf of commutative `𝒪_Z`-algebras**: the ungraded realization of the
conormal algebra, commutative by `Stacks.Conormal.ConormalAlgebraData.mul_comm_int`. This is the
input the relative spectrum takes. -/
def conormalAlgebraSheaf (i : Z ⟶ X) [IsImmersion i] : Stacks.RelativeSpec.AlgebraSheaf Z :=
  Stacks.RelativeSpec.gradedAlgebraSheaf Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int

/-- `Sym(𝒞_{Z/X})` as a sheaf of commutative `𝒪_Z`-algebras, the algebra whose relative spectrum
is the normal bundle. -/
abbrev normalBundleAlgebra (i : Z ⟶ X) [IsImmersion i] : Stacks.RelativeSpec.AlgebraSheaf Z :=
  Scheme.Modules.symmetricAlgebraSheaf Z (conormalSheafDegreeOne i)

/-- **The canonical map of algebra sheaves `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`**: the ungraded realization
of the canonical map of graded algebras `Stacks.Conormal.conormalSymmetricHom` of Tag 0632. -/
@[ega "IV 17.12.1" "partial"]
def conormalSymmetricAlgebraSheafHom (i : Z ⟶ X) [IsImmersion i] :
    normalBundleAlgebra i ⟶ conormalAlgebraSheaf i :=
  Stacks.RelativeSpec.gradedAlgebraSheafMap Z (conormalSymmetricHom i)
    (Scheme.Modules.symmetricAlgebra_mul_comm Z (conormalSheafDegreeOne i))
    (conormalAlgebra i).mul_comm_int

/-! ### Quasi-coherence of the conormal algebra sheaf -/

/-- A coproduct of quasi-coherent modules on a scheme is quasi-coherent also when its index type
merely admits an equivalence with a type of the module universe, rather than lying in that
universe itself: reindex along a shrinking of the index type. An `ℕ`-graded coproduct is the
case needed, and `ℕ` does not lie in the module universe unless that universe is `0`. -/
private theorem isQuasicoherent_coprodOfSmall {Y : Scheme.{u}} {ι : Type*} [Small.{u} ι]
    (M : ι → SheafOfModules.{u} Y.ringCatSheaf) [Limits.HasCoproduct M]
    (h : ∀ j, (M j).IsQuasicoherent) :
    (∐ M).IsQuasicoherent :=
  haveI (j : Shrink.{u} ι) : (M ((equivShrink ι).symm j)).IsQuasicoherent := h _
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso SheafOfModules.sigmaShrinkIso
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma
      fun j : Shrink.{u} ι => M ((equivShrink ι).symm j))

/-- **`𝒞_{Z/X,*}` is a quasi-coherent sheaf of algebras.** The conormal algebra is concentrated
in nonnegative degrees, so the module underlying its ungraded realization is the coproduct of its
homogeneous pieces; those are quasi-coherent by Tag 0630, and quasi-coherence is stable under
coproducts on a scheme. -/
instance isQuasicoherent_conormalAlgebraSheaf (i : Z ⟶ X) [IsImmersion i] :
    (conormalAlgebraSheaf i).IsQuasicoherent :=
  Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (conormalAlgebra i).negative_isZero
    (isQuasicoherent_coprodOfSmall (fun n : ℕ => (conormalAlgebra i).algebra.piece (n : ℤ))
      fun n => (conormalAlgebra i).isQuasicoherent (n : ℤ))

/-! ### The normal cone, the normal bundle, and the canonical morphism between them -/

variable (i : Z ⟶ X) [IsImmersion i]

/-- The relative-spectrum situation of `Sym(𝒞_{Z/X})` on `Z`, whose spectrum is the normal
bundle. A `reducible` abbreviation, so that its base unifies with `Z` on sight. -/
abbrev normalBundleSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  { base := Z, algebra := normalBundleAlgebra i }

/-- **The normal cone `C_ZX = Spec_Z(𝒞_{Z/X,*})`** of an immersion `i : Z ⟶ X`. -/
def normalCone : Scheme.{u} :=
  Stacks.AffineAlgebraEquivalence.relativeSpec (conormalAlgebraSheaf i)

/-- **The projection `C_ZX ⟶ Z`** of the normal cone to its base. -/
def normalConeToBase : normalCone i ⟶ Z :=
  Stacks.AffineAlgebraEquivalence.relativeSpecToBase (conormalAlgebraSheaf i)

/-- **Stacks Project, Tag 0637.** **The canonical morphism `C_ZX ⟶ N_ZX` from the normal cone to
the normal bundle of an immersion**, defined by the canonical map
`Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of graded algebras of Tag 0632: it is the morphism of relative
spectra attached to that map of algebra sheaves, and
`Stacks.Conormal.ι_normalConeToNormalBundle` is its characterising property. -/
@[stacks 0637 "the canonical surjection of graded algebras defines a morphism C_ZX → N_ZX"]
def normalConeToNormalBundle :
    normalCone i ⟶ Scheme.Modules.vectorBundle Z (conormalSheafDegreeOne i) :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom (normalBundleSituation i)
    (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (conormalSymmetricAlgebraSheafHom i)

/-- **Stacks Project, Tag 0637.** The canonical morphism `C_ZX ⟶ N_ZX` is a morphism of schemes
over `Z`: it carries the projection of the normal bundle to the projection of the normal cone. -/
@[stacks 0637 "the morphism C_ZX → N_ZX is a morphism over Z"]
theorem normalConeToNormalBundle_toBase :
    normalConeToNormalBundle i ≫
        Scheme.Modules.vectorBundleToBase Z (conormalSheafDegreeOne i) =
      normalConeToBase i :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_toBase (normalBundleSituation i)
    (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (conormalSymmetricAlgebraSheafHom i)

/-- **The characterising property of the canonical morphism `C_ZX ⟶ N_ZX`**: over an affine open
`U` of `Z` it is the spectrum of the canonical map of algebra sheaves on the sections over `U`,
followed by the chart of `U` in the normal bundle. -/
theorem ι_normalConeToNormalBundle (U : Z.affineOpens) :
    (normalConeToBase i ⁻¹ᵁ U.1).ι ≫ normalConeToNormalBundle i =
      (normalConeToBase i ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map ((conormalSymmetricAlgebraSheafHom i).right.hom.app (op U.1) ≫
            (Stacks.RelativeSpec.universalAlgebraMap
              ((normalBundleSituation i).withAlgebra (conormalAlgebraSheaf i)
                  (isQuasicoherent_conormalAlgebraSheaf i))).right.app
                (op U.1)) ≫
          (Stacks.RelativeSpec.gluedSpectrum (normalBundleSituation i)).chart U :=
  Stacks.RelativeSpec.ι_relativeSpectrumMapOfAlgebraHom (normalBundleSituation i)
    (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (conormalSymmetricAlgebraSheafHom i) U

/-- **The canonical morphism `C_ZX ⟶ N_ZX`, read on sections over an affine open `U` of `Z`**: the
universal algebra map of `Sym(𝒞_{Z/X})` followed by the sections of the morphism is the sections
of the canonical map of algebra sheaves followed by the universal algebra map of `𝒞_{Z/X,*}`. -/
theorem normalConeToNormalBundle_appLE (U : Z.affineOpens)
    (h : normalConeToBase i ⁻¹ᵁ U.1 ≤
      normalConeToNormalBundle i ⁻¹ᵁ
        (Scheme.Modules.vectorBundleToBase Z (conormalSheafDegreeOne i) ⁻¹ᵁ U.1)) :
    (Stacks.RelativeSpec.universalAlgebraMap (normalBundleSituation i)).right.app (op U.1) ≫
        (normalConeToNormalBundle i).appLE
          (Scheme.Modules.vectorBundleToBase Z (conormalSheafDegreeOne i) ⁻¹ᵁ U.1)
          (normalConeToBase i ⁻¹ᵁ U.1) h =
      (conormalSymmetricAlgebraSheafHom i).right.hom.app (op U.1) ≫
        (Stacks.RelativeSpec.universalAlgebraMap
          ((normalBundleSituation i).withAlgebra (conormalAlgebraSheaf i)
              (isQuasicoherent_conormalAlgebraSheaf i))).right.app
            (op U.1) :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_appLE (normalBundleSituation i)
    (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (conormalSymmetricAlgebraSheafHom i) U h

end Stacks.Conormal

end
