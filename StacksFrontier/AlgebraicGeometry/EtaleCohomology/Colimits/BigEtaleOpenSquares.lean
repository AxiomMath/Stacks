module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.CategoryTheory.Sites.Pretopology.AsSmallSite
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ColimitDescent

/-!
# Mayer--Vietoris squares of preimages of opens in the big étale site

Let `h : Y ⟶ X` be a morphism of schemes and let `U`, `V` be open subschemes of `X`. The four
open subschemes `h⁻¹(U ⊓ V)`, `h⁻¹U`, `h⁻¹V`, `h⁻¹(U ⊔ V)` of `Y` form a Mayer--Vietoris square
for the big étale topology: the square is cartesian, because the intersection of two opens is
their fibre product inside a third, and the two inclusions into `h⁻¹(U ⊔ V)` are étale, being
open immersions, and jointly surjective, because taking preimages commutes with unions.

The site on which this is stated is the category of **all** schemes with its big étale topology,
raised by `CategoryTheory.AsSmall` so that objects and morphisms share a universe; abelian sheaves
on it then have sheafification and `Ext`-groups.

## Main definitions

* `Stacks.EtaleCohomology.BigEtale.Site` and `.topology`: the big étale site of schemes, raised
  to a single universe.
* `Stacks.EtaleCohomology.BigEtale.preimageToSite`: the functor `X.Opens ⥤ Site` attached to a
  morphism `h : Y ⟶ X`, sending an open `U` of `X` to the open subscheme `h⁻¹U` of `Y`.
* `Stacks.EtaleCohomology.BigEtale.opensSquare`: the square `U ⊓ V`, `U`, `V`, `U ⊔ V` of opens.
* `Stacks.EtaleCohomology.BigEtale.preimageMVSquare`: **the Mayer--Vietoris square of the
  preimages.**

## Main results

* `Stacks.EtaleCohomology.BigEtale.preimageSquare_isPullback`: the square is cartesian.
* `Stacks.EtaleCohomology.BigEtale.preimageSquare_cover`: the two inclusions generate a covering
  sieve.
* `Stacks.EtaleCohomology.BigEtale.preimageSquare_isPushout`: the pushout condition, which is the
  remaining field of `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`.

## References

* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open TopologicalSpace

universe u

namespace Stacks.EtaleCohomology.BigEtale

/-! ### The big étale site in a single universe -/

/-- The category of all schemes, with its objects and its morphisms in one and the same
universe. -/
abbrev Site : Type (u + 1) := AsSmall.{u + 1} Scheme.{u}

/-- The big étale topology, transported to `Stacks.EtaleCohomology.BigEtale.Site`. -/
abbrev topology : GrothendieckTopology Site.{u} :=
  (AsSmall.down : Site.{u} ⥤ Scheme.{u}).inducedTopology Scheme.etaleTopology

/-- Reading an object of the raised big étale site as a scheme is an equivalence. -/
instance asSmallDown_isEquivalence : (AsSmall.down : Site.{u} ⥤ Scheme.{u}).IsEquivalence :=
  AsSmall.equiv.isEquivalence_inverse

/-- Raising a scheme to an object of the raised big étale site is an equivalence. -/
instance asSmallUp_isEquivalence : (AsSmall.up : Scheme.{u} ⥤ Site.{u}).IsEquivalence :=
  AsSmall.equiv.isEquivalence_functor

/-- Abelian sheaves on the raised big étale site have all `Ext`-groups: the site is small in the
coefficient universe, so the category of abelian sheaves on it is a Grothendieck abelian category
and in particular has enough injectives. -/
instance hasExt_sheaf_topology :
    HasExt.{u + 1} (Sheaf topology.{u} AddCommGrpCat.{u + 1}) := by
  have : IsGrothendieckAbelian.{u + 1} (Sheaf topology.{u} AddCommGrpCat.{u + 1}) :=
    inferInstance
  exact hasExt_of_enoughInjectives _

/-- The open subschemes of a scheme, included into the raised big étale site. -/
def opensToSite (Y : Scheme.{u}) : Y.Opens ⥤ Site.{u} :=
  Y.restrictFunctor ⋙ Over.forget Y ⋙ AsSmall.up

/-- The preimages of the opens of `X` along `h`, as a functor into the raised big étale site. -/
def preimageToSite {X Y : Scheme.{u}} (h : Y ⟶ X) : X.Opens ⥤ Site.{u} :=
  Opens.map h.base ⋙ opensToSite Y

/-! ### The square of two opens -/

/-- The square `U ⊓ V`, `U`, `V`, `U ⊔ V` in the lattice of open subschemes. -/
def opensSquare {X : Scheme.{u}} (U V : X.Opens) : Square X.Opens where
  X₁ := U ⊓ V
  X₂ := U
  X₃ := V
  X₄ := U ⊔ V
  f₁₂ := homOfLE inf_le_left
  f₁₃ := homOfLE inf_le_right
  f₂₄ := homOfLE le_sup_left
  f₃₄ := homOfLE le_sup_right
  fac := Subsingleton.elim _ _

/-- The square of the preimages of two opens, in the raised big étale site. -/
def preimageSquare {X Y : Scheme.{u}} (h : Y ⟶ X) (U V : X.Opens) : Square Site.{u} :=
  (opensSquare U V).map (preimageToSite h)

section

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (U V : X.Opens)

/-- An inclusion of open subschemes is a monomorphism of the raised big étale site: it is a
monomorphism of schemes, and reading an object of the raised site as a scheme is faithful. -/
theorem mono_opensToSite_map {Y : Scheme.{u}} {U V : Y.Opens} (f : U ⟶ V) :
    Mono ((opensToSite Y).map f) := by
  apply Functor.mono_of_mono_map (AsSmall.down : Site.{u} ⥤ Scheme.{u})
  show Mono (Y.homOfLE f.le)
  infer_instance

/-- The inclusion of the preimage of `U ⊓ V` into the preimage of `V` is a monomorphism. -/
instance mono_preimageSquare_f₁₃ : Mono (preimageSquare h U V).f₁₃ :=
  mono_opensToSite_map ((Opens.map h.base).map (homOfLE inf_le_right))

/-- The inclusion of the preimage of `U` into the preimage of `U ⊔ V` is a monomorphism. -/
instance mono_preimageSquare_f₂₄ : Mono (preimageSquare h U V).f₂₄ :=
  mono_opensToSite_map ((Opens.map h.base).map (homOfLE le_sup_left))

/-- The inclusion of the preimage of `V` into the preimage of `U ⊔ V` is a monomorphism. -/
instance mono_preimageSquare_f₃₄ : Mono (preimageSquare h U V).f₃₄ :=
  mono_opensToSite_map ((Opens.map h.base).map (homOfLE le_sup_right))

/-- **The square of preimages is cartesian.** The intersection of two open subschemes is their
fibre product inside a third, and reading an object of the raised big étale site as a scheme
reflects this limit. -/
theorem preimageSquare_isPullback : (preimageSquare h U V).IsPullback := by
  apply Square.IsPullback.of_map (AsSmall.down : Site.{u} ⥤ Scheme.{u})
  show IsPullback (Y.homOfLE inf_le_left) (Y.homOfLE inf_le_right)
    (Y.homOfLE (show h ⁻¹ᵁ U ≤ h ⁻¹ᵁ U ⊔ h ⁻¹ᵁ V from le_sup_left))
    (Y.homOfLE (show h ⁻¹ᵁ V ≤ h ⁻¹ᵁ U ⊔ h ⁻¹ᵁ V from le_sup_right))
  exact isPullback_opens_inf_le _ _

/-- The sieve generated by two morphisms is carried to the sieve generated by their images by
the pushforward along a functor. -/
private theorem functorPushforward_ofTwoArrows {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B W : C} (a : A ⟶ W) (b : B ⟶ W) :
    (Sieve.ofTwoArrows a b).functorPushforward F =
      Sieve.ofTwoArrows (F.map a) (F.map b) := by
  ext Z g
  simp only [Sieve.ofTwoArrows, Sieve.functorPushforward_ofArrows, Sieve.mem_ofArrows_iff]
  constructor <;> rintro ⟨i, c, hc⟩ <;> cases i <;>
    first | exact ⟨WalkingPair.left, c, hc⟩ | exact ⟨WalkingPair.right, c, hc⟩

/-- **The two inclusions of the preimages generate a covering sieve of the big étale topology.**
They are open immersions, hence étale, and their images cover the preimage of `U ⊔ V`, because
taking preimages commutes with unions. -/
private theorem ofTwoArrows_mem_etaleTopology :
    Sieve.ofTwoArrows
        (Y.homOfLE (show h ⁻¹ᵁ U ≤ h ⁻¹ᵁ (U ⊔ V) from
          Scheme.Hom.preimage_mono h le_sup_left))
        (Y.homOfLE (show h ⁻¹ᵁ V ≤ h ⁻¹ᵁ (U ⊔ V) from
          Scheme.Hom.preimage_mono h le_sup_right)) ∈
      Scheme.etaleTopology ((h ⁻¹ᵁ (U ⊔ V) : Y.Opens) : Scheme.{u}) :=
  by
  refine (Scheme.Cover.mkOfCovers (P := @Etale) WalkingPair
    (fun j => WalkingPair.casesOn j (((h ⁻¹ᵁ U : Y.Opens) : Scheme.{u}))
      (((h ⁻¹ᵁ V : Y.Opens) : Scheme.{u})))
    (fun j => WalkingPair.casesOn j _ _) ?_ fun j => ?_).mem_grothendieckTopology
  · intro x
    rcases x.property with hx | hx
    · exact ⟨WalkingPair.left, ⟨x.val, hx⟩, Scheme.homOfLE_apply' _ x.val hx⟩
    · exact ⟨WalkingPair.right, ⟨x.val, hx⟩, Scheme.homOfLE_apply' _ x.val hx⟩
  · cases j <;> infer_instance

/-- **The two inclusions generate a covering sieve**, read on the raised big étale site. -/
theorem preimageSquare_cover :
    Sieve.ofTwoArrows (preimageSquare h U V).f₂₄ (preimageSquare h U V).f₃₄ ∈
      topology.{u} (preimageSquare h U V).X₄ := by
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, functorPushforward_ofTwoArrows]
  exact ofTwoArrows_mem_etaleTopology h U V

/-- **The Mayer--Vietoris square of the preimages of two opens.** -/
def preimageMVSquare : topology.{u}.MayerVietorisSquare :=
  GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback (J := topology.{u})
    (preimageSquare h U V) (preimageSquare_isPullback h U V) (preimageSquare_cover h U V)

/-- The underlying square of `preimageMVSquare h U V` is `preimageSquare h U V`. -/
@[simp] theorem preimageMVSquare_toSquare :
    (preimageMVSquare h U V).toSquare = preimageSquare h U V := rfl

/-- The pushout condition for the square of preimages: the remaining field of a
Mayer--Vietoris square. -/
theorem preimageSquare_isPushout :
    ((preimageSquare h U V).map
      (yoneda ⋙ presheafToSheaf topology.{u} (Type (u + 1)))).IsPushout :=
  (preimageMVSquare h U V).isPushout

end

end Stacks.EtaleCohomology.BigEtale

end
