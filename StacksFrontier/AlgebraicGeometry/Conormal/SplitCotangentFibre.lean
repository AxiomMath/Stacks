module

public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Conormal.StalkSplitting
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators

/-!
# Injectivity of the map of cotangent fibres of a split conormal sequence

Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes whose conormal sequence
`i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` is exact and locally split, let `z : Z` and write
`x = j (i z)`.  The stalks at `x` of the defining ideals of `j` and of `i ≫ j` satisfy
`I_x ⊆ J_x`, and this file proves that the induced map `I_x / 𝔪_x I_x ⟶ J_x / 𝔪_x J_x` of
cotangent fibres is injective, which is the key step in [Stacks Project, Tag 068Z].

## Main results

* `Stacks.AlgebraicGeometry.injective_idealCotangentFiberMap`: the map of cotangent fibres of a
  pair of immersions with an exact and locally split conormal sequence is injective.
* `Stacks.Conormal.germ_canonicalConormalQuotientMap`: the identification of the stalk of the
  conormal sheaf with a cotangent module carries the germ of the conormal class of a section of
  the defining ideal to the class of the germ of that section.
* `Stacks.Conormal.conormalClass_homEquiv_immersionConormalSheafMap`: the transpose of the
  morphism of conormal sheaves induced by a commutative square of immersions carries conormal
  classes to conormal classes.

## Implementation notes

An immersion `f` factors as the closed immersion `f.liftCoborder` into the open subscheme
`f.coborderRange`, and the stalk of its conormal sheaf is described in
`StacksFrontier.AlgebraicGeometry.Conormal.Stalk` through the kernel of the map of local rings of
that closed factor.  `Stacks.Conormal.coborderStalkEquiv` is the resulting identification of the
local ring of `X` at `f z` with the local ring of the coborder, and every statement below is
transported along it.

The local ring of `Z` at `z` is a quotient of the local ring of `X` at `x`, so the cotangent
fibre `I_x / 𝔪_x I_x` is a module over the residue field at `x` on which `𝒪_{Z,z}` acts through
that quotient; `Stacks.Conormal.exists_tensorLift` is the resulting map out of the base change
`𝒪_{Z,z} ⊗_{𝒪_{Y,i z}} (𝒞_{Y/X})_{i z}`, which is the stalk at `z` of `i^* 𝒞_{Y/X}`.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 068Z)](https://stacks.math.columbia.edu/tag/068Z)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction 

universe u

namespace Stacks.Conormal

open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.ClosedImmersion Stacks.Immersion
open Stacks.AlgebraicGeometry (idealCotangentFiberMap conormalSequenceLeftMap)


section Coborder

/-- Transporting a germ along an equality of points is again a germ. -/
theorem germ_eqToHom {W : Scheme.{u}} (A : W.Opens) {p q : W} (h : p = q)
    (hp : p ∈ A) (hq : q ∈ A) (c : Γ(W, A)) :
    (eqToHom (congrArg W.presheaf.stalk h)).hom (W.presheaf.germ A p hp c) =
      W.presheaf.germ A q hq c := by
  subst h
  rfl

variable {Z X : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] (z : Z)

/-- The image in `X` of the lift of `z` to the coborder neighbourhood is `f z`. -/
theorem coborderBase : f.coborderRange.ι.base (f.liftCoborder.base z) = f.base z :=
  congrArg (fun m : Z ⟶ X => m.base z) f.liftCoborder_ι

/-- The local ring of `X` at `f z` is the local ring of the coborder neighbourhood. -/
def coborderStalkEquiv :
    X.presheaf.stalk (f.base z) ≅
      f.coborderRange.toScheme.presheaf.stalk (f.liftCoborder.base z) :=
  eqToIso (congrArg X.presheaf.stalk (coborderBase f z).symm) ≪≫
    asIso (f.coborderRange.ι.stalkMap (f.liftCoborder.base z))

/-- The identification with the local ring of the coborder carries germs to germs. -/
theorem coborderStalkEquiv_germ (A : X.Opens) (hA : f.base z ∈ A)
    (hA' : f.liftCoborder.base z ∈ f.coborderRange.ι ⁻¹ᵁ A) (c : Γ(X, A)) :
    (coborderStalkEquiv f z).hom.hom (X.presheaf.germ A (f.base z) hA c) =
      f.coborderRange.toScheme.presheaf.germ (f.coborderRange.ι ⁻¹ᵁ A)
        (f.liftCoborder.base z) hA' ((f.coborderRange.ι.app A).hom c) := by
  rw [← AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply f.coborderRange.ι A
    (f.liftCoborder.base z) hA' c, coborderStalkEquiv]
  simp only [Iso.trans_hom, asIso_hom, CommRingCat.comp_apply]
  exact congrArg (f.coborderRange.ι.stalkMap (f.liftCoborder.base z)).hom
    (germ_eqToHom A (coborderBase f z).symm hA hA' c)

/-- The map of local rings of an immersion factors through its coborder neighbourhood. -/
theorem stalkMap_coborderStalkEquiv (c : X.presheaf.stalk (f.base z)) :
    (f.liftCoborder.stalkMap z).hom ((coborderStalkEquiv f z).hom.hom c) =
      (f.stalkMap z).hom c := by
  have key : ∀ (m : Z ⟶ X) (hm : m = f),
      ∀ c : X.presheaf.stalk (f.base z),
        (m.stalkMap z).hom
            ((eqToHom (congrArg X.presheaf.stalk
              (congrArg (fun p : Z ⟶ X => p.base z) hm).symm)).hom c) =
          (f.stalkMap z).hom c := by
    rintro m rfl c
    rfl
  have h := Scheme.Hom.stalkMap_comp f.liftCoborder f.coborderRange.ι z
  rw [coborderStalkEquiv]
  simp only [Iso.trans_hom, asIso_hom, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, ← h]
  exact key _ f.liftCoborder_ι c

end Coborder


section ConormalClassGerm

variable {Z X : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] (z : Z)

/-- The identification with the local ring of the coborder preserves the two kernels. -/
theorem coborderStalkEquiv_mem_ker (c : X.presheaf.stalk (f.base z))
    (hc : c ∈ RingHom.ker (f.stalkMap z).hom) :
    (coborderStalkEquiv f z).hom.hom c ∈ RingHom.ker (f.liftCoborder.stalkMap z).hom := by
  rw [RingHom.mem_ker, stalkMap_coborderStalkEquiv]
  exact hc

/-- The lift of `z` to the coborder lies over every open neighbourhood of `f z`. -/
theorem mem_coborder_preimage (A : X.Opens) (hA : f.base z ∈ A) :
    f.liftCoborder.base z ∈ f.coborderRange.ι ⁻¹ᵁ A := by
  change f.coborderRange.ι.base (f.liftCoborder.base z) ∈ A
  rw [coborderBase]
  exact hA

/-- The preimage of an open under an immersion is its preimage under the closed factor. -/
theorem preimage_eq_coborder (A : X.Opens) :
    f ⁻¹ᵁ A = f.liftCoborder ⁻¹ᵁ (f.coborderRange.ι ⁻¹ᵁ A) := by
  rw [← Scheme.Hom.comp_preimage, f.liftCoborder_ι]

/-- **The stalk of the conormal sheaf carries conormal classes to cotangent classes.** The germ
at `z` of the conormal class of a section of the ideal sheaf over `A` is the class modulo `I²` of
the germ of that section, read in the coborder neighbourhood. -/
theorem germ_canonicalConormalQuotientMap (A : X.Opens) (hA : f.base z ∈ A)
    (y : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (op A)) :
    Stacks.Conormal.conormalSheafStalkEquivCotangent f z
        (TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf f).val.presheaf
          (f ⁻¹ᵁ A) z hA
          ((Stacks.Immersion.canonicalConormalQuotientMap f).val.app (op A) y))
      = (RingHom.ker (f.liftCoborder.stalkMap z).hom).toCotangent
          ⟨(coborderStalkEquiv f z).hom.hom
              (X.presheaf.germ A (f.base z) hA (Stacks.Conormal.idealSection f A y)),
            coborderStalkEquiv_mem_ker f z _
              (Stacks.Conormal.germ_idealSection_mem_ker_stalkMap f z A hA y)⟩ := by
  have hz' := mem_coborder_preimage f z A hA
  have hTeq := preimage_eq_coborder f A
  have hkey := Stacks.Immersion.conormalQuotientMap_apply_idealSheafComparison f
    f.coborderRange f.liftCoborder f.liftCoborder_ι A (f ⁻¹ᵁ A) le_rfl (le_of_eq hTeq) y
  rw [Stacks.Conormal.OpenFactorizations.conormalQuotientMap_liftCoborder f] at hkey
  have step1 : TopCat.Presheaf.germ (C := Ab.{u})
        (Stacks.Conormal.conormalSheaf f).val.presheaf (f ⁻¹ᵁ A) z hA
        ((Stacks.Immersion.canonicalConormalQuotientMap f).val.app (op A) y) =
      TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf f).val.presheaf
        ((opensMap f.liftCoborder.toLRSHom.toShHom).obj (f.coborderRange.ι ⁻¹ᵁ A)) z hz'
        (((modulePullbackPushforwardAdjunction f.liftCoborder.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf f.liftCoborder.toLRSHom.toShHom)).val.app
          (op (f.coborderRange.ι ⁻¹ᵁ A))
          ((Stacks.Immersion.idealSheafComparison f f.coborderRange f.liftCoborder
            f.liftCoborder_ι).val.app (op A) y)) := by
    refine Eq.trans (Eq.trans (TopCat.Presheaf.germ_res_apply
      (Stacks.Conormal.conormalSheaf f).val.presheaf (homOfLE (le_refl (f ⁻¹ᵁ A))) z hA _).symm
      (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
        (Stacks.Conormal.conormalSheaf f).val.presheaf (f ⁻¹ᵁ A) z hA) hkey.symm)) ?_
    exact TopCat.Presheaf.germ_res_apply (Stacks.Conormal.conormalSheaf f).val.presheaf
      (homOfLE (le_of_eq hTeq)) z hA _
  refine Eq.trans (congrArg (fun t => Stacks.Conormal.conormalSheafStalkEquivCotangent f z t)
    step1) ?_
  refine Eq.trans (Stacks.Conormal.conormalSheafStalkEquivCotangent_germ f z
    (f.coborderRange.ι ⁻¹ᵁ A) hz' _) ?_
  refine congrArg (RingHom.ker (f.liftCoborder.stalkMap z).hom).toCotangent (Subtype.ext ?_)
  have hcmp := congr($(Stacks.Immersion.idealSheafComparison_comp_ι f f.coborderRange
    f.liftCoborder f.liftCoborder_ι).val.app (op A) y)
  exact (congrArg (f.coborderRange.toScheme.presheaf.germ (f.coborderRange.ι ⁻¹ᵁ A)
      (f.liftCoborder.base z) hz') hcmp).trans
    (coborderStalkEquiv_germ f z A hA hz' _).symm

end ConormalClassGerm


section SquareTranspose

open Stacks.ClosedImmersion Stacks.Immersion

/-- **The transpose of the induced map of conormal sheaves carries conormal classes to conormal
classes.** -/
theorem conormalClass_homEquiv_immersionConormalSheafMap
    {Z Z' W W' : Scheme.{u}} (i : Z ⟶ Z') (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W')
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ k = f ≫ j)
    (V : W'.Opens) (C : Z.Opens)
    (hC : C ≤ i ⁻¹ᵁ (k ⁻¹ᵁ V)) (hC' : C ≤ f ⁻¹ᵁ (j ⁻¹ᵁ V))
    (y : (idealSheaf j.toLRSHom.toShHom).val.obj (op V))
    (E : (idealSheaf i.toLRSHom.toShHom).val.obj (op (k ⁻¹ᵁ V)))
    (hE : (idealSheafι i.toLRSHom.toShHom).val.app (op (k ⁻¹ᵁ V)) E =
      (Scheme.Hom.app k V).hom ((idealSheafι j.toLRSHom.toShHom).val.app (op V) y)) :
    (Stacks.Conormal.conormalSheaf i).val.map (homOfLE hC').op
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (immersionConormalSheafMap i j f k (toShHom_square hcomm))).val.app (op (j ⁻¹ᵁ V))
          ((canonicalConormalQuotientMap j).val.app (op V) y)) =
      (Stacks.Conormal.conormalSheaf i).val.map (homOfLE hC).op
        ((canonicalConormalQuotientMap i).val.app (op (k ⁻¹ᵁ V)) E) := by
  have hK := congr($(canonicalConormalQuotientMap_comp_pushforward_homEquiv i j f k
    (toShHom_square hcomm)).val.app (op V) y)
  have hI := congr($(unit_comp_pushforward_idealSheafMap_comp_ι
    (toShHom_square hcomm)).val.app (op V) y)
  have hEE : (idealSheafMap (toShHom_square hcomm)).val.app (op (k ⁻¹ᵁ V))
      (((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).unit.app
        (idealSheaf j.toLRSHom.toShHom)).val.app (op V) y) = E :=
    injective_idealSheafι_val_app i.toLRSHom.toShHom (k ⁻¹ᵁ V)
      (hI.trans ((structureSheafModuleHom_val_app k V _).trans hE.symm))
  refine Eq.trans (congrArg ((Stacks.Conormal.conormalSheaf i).val.map (homOfLE hC').op) hK) ?_
  refine Eq.trans (modulePushforwardSquareIso_hom_val_app_restrict f.toLRSHom.toShHom
    k.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom (toShHom_square hcomm)
    (Stacks.Conormal.conormalSheaf i) V (homOfLE hC') (homOfLE hC) _) ?_
  exact congrArg ((Stacks.Conormal.conormalSheaf i).val.map (homOfLE hC).op)
    (congrArg ((canonicalConormalQuotientMap i).val.app (op (k ⁻¹ᵁ V))) hEE)

section Germ

variable {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z)

/-- **The stalk of the left-hand map of the conormal sequence carries conormal classes to
conormal classes.** -/
theorem stalkHom_conormalSequenceLeftMap_conormalClass (A : X.Opens)
    (hA : z ∈ (i ≫ j) ⁻¹ᵁ A) (hAi : z ∈ (opensMap i.toLRSHom.toShHom).obj (j ⁻¹ᵁ A))
    (y : (idealSheaf j.toLRSHom.toShHom).val.obj (op A))
    (E : (idealSheaf (i ≫ j).toLRSHom.toShHom).val.obj (op A))
    (hE : (idealSheafι (i ≫ j).toLRSHom.toShHom).val.app (op A) E =
      (idealSheafι j.toLRSHom.toShHom).val.app (op A) y) :
    Stacks.AlgebraicGeometry.stalkHom (Stacks.AlgebraicGeometry.conormalSequenceLeftMap i j) z
        (TopCat.Presheaf.germ (C := Ab.{u})
          ((modulePullback i.toLRSHom.toShHom).obj
            (Stacks.Conormal.conormalSheaf j)).val.presheaf
          ((opensMap i.toLRSHom.toShHom).obj (j ⁻¹ᵁ A)) z hAi
          (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
              (Stacks.Conormal.conormalSheaf j)).val.app (op (j ⁻¹ᵁ A))
            ((canonicalConormalQuotientMap j).val.app (op A) y))) =
      TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf (i ≫ j)).val.presheaf
        ((i ≫ j) ⁻¹ᵁ A) z hA
        ((canonicalConormalQuotientMap (i ≫ j)).val.app (op A) E) := by
  have hcomm : (i ≫ j) ≫ 𝟙 X = i ≫ j := Category.comp_id _
  have hC : ((i ≫ j) ⁻¹ᵁ A) ≤ (i ≫ j) ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ A) := le_rfl
  have hC' : ((i ≫ j) ⁻¹ᵁ A) ≤ i ⁻¹ᵁ (j ⁻¹ᵁ A) := le_rfl
  have hD := conormalClass_homEquiv_immersionConormalSheafMap (i ≫ j) j i (𝟙 X) hcomm A
    ((i ≫ j) ⁻¹ᵁ A) hC hC' y E hE
  have hhe := congr($(Adjunction.homEquiv_unit
      (adj := modulePullbackPushforwardAdjunction i.toLRSHom.toShHom)
      (f := Stacks.AlgebraicGeometry.conormalSequenceLeftMap i j)).val.app (op (j ⁻¹ᵁ A))
    ((canonicalConormalQuotientMap j).val.app (op A) y))
  refine Eq.trans (Stacks.AlgebraicGeometry.stalkHom_germ
    (Stacks.AlgebraicGeometry.conormalSequenceLeftMap i j) z _ hAi _) ?_
  refine Eq.trans (TopCat.Presheaf.germ_res_apply (C := Ab.{u})
    (Stacks.Conormal.conormalSheaf (i ≫ j)).val.presheaf (homOfLE hC') z hA _).symm ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
    (Stacks.Conormal.conormalSheaf (i ≫ j)).val.presheaf ((i ≫ j) ⁻¹ᵁ A) z hA)
    ((congrArg (fun w => (Stacks.Conormal.conormalSheaf (i ≫ j)).val.map (homOfLE hC').op w)
      hhe.symm).trans hD)) ?_
  exact TopCat.Presheaf.germ_res_apply (C := Ab.{u})
    (Stacks.Conormal.conormalSheaf (i ≫ j)).val.presheaf (homOfLE hC) z hA _

end Germ

end SquareTranspose


section CotangentFibre

open Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- Scalars act on `M ⧸ m M` through their classes modulo `m`. -/
theorem quotientMk_smul {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (c : R) (t : M ⧸ m • (⊤ : Submodule R M)) :
    (Ideal.Quotient.mk m c) • t = c • t := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [Module.Quotient.mk_smul_mk, Submodule.Quotient.mk_smul]

/-- The class of a sum of elements of an ideal, in a cotangent fibre of that ideal. -/
theorem mk_eq_add {R : Type u} [CommRing R] {I m : Ideal R} {a b c : R}
    (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hceq : c = a + b) :
    (Submodule.Quotient.mk ⟨c, hc⟩ : I ⧸ m • (⊤ : Submodule R I)) =
      Submodule.Quotient.mk ⟨a, ha⟩ + Submodule.Quotient.mk ⟨b, hb⟩ := by
  subst hceq
  exact map_add (Submodule.mkQ (m • (⊤ : Submodule R I))) ⟨a, ha⟩ ⟨b, hb⟩

/-- The class of a multiple of an element of an ideal, in a cotangent fibre of that ideal. -/
theorem mk_eq_smul {R : Type u} [CommRing R] {I m : Ideal R} {a c : R} (r : R)
    (ha : a ∈ I) (hc : c ∈ I) (hceq : c = r * a) :
    (Submodule.Quotient.mk ⟨c, hc⟩ : I ⧸ m • (⊤ : Submodule R I)) =
      r • Submodule.Quotient.mk ⟨a, ha⟩ := by
  subst hceq
  rw [← Submodule.Quotient.mk_smul]
  rfl

/-- A product of two elements of an ideal contained in the maximal ideal has class zero in the
cotangent fibre. -/
theorem mk_eq_zero_of_mul {R : Type u} [CommRing R] [IsLocalRing R] {I : Ideal R}
    (hI : I ≤ IsLocalRing.maximalIdeal R) {a b c : R} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hceq : c = a * b) :
    (Submodule.Quotient.mk ⟨c, hc⟩ :
      I ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)) = 0 := by
  subst hceq
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (hI ha) (Submodule.mem_top (x := (⟨b, hb⟩ : I)))

variable {Z X : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] (z : Z)

/-- The transported kernel of a stalk map lies in the stalk of the defining ideal. -/
theorem coborderStalkEquiv_inv_mem_stalkIdeal
    (b : f.coborderRange.toScheme.presheaf.stalk (f.liftCoborder.base z))
    (hb : b ∈ RingHom.ker (f.liftCoborder.stalkMap z).hom) :
    (coborderStalkEquiv f z).inv.hom b ∈
      Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace) (definingIdealOfHom f)
        (f.base z) := by
  rw [stalkIdeal_definingIdealOfHom_eq_ker f z, RingHom.mem_ker,
    ← stalkMap_coborderStalkEquiv f z, Iso.inv_hom_id_apply (coborderStalkEquiv f z) b]
  exact hb

/-- The stalk of a defining ideal is a proper ideal of the local ring. -/
theorem stalkIdeal_le_maximalIdeal :
    Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace) (definingIdealOfHom f)
        (f.base z) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base z)) := by
  refine IsLocalRing.le_maximalIdeal fun h => ?_
  rw [stalkIdeal_definingIdealOfHom_eq_ker f z] at h
  have h1 : (1 : X.presheaf.stalk (f.base z)) ∈ RingHom.ker (f.stalkMap z).hom := by
    rw [h]; exact Submodule.mem_top
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

/-- **The cotangent module of the coborder kernel maps to the cotangent fibre of the defining
ideal.** -/
theorem exists_conormalCotangentFibreMap :
    ∃ θ : (RingHom.ker (f.liftCoborder.stalkMap z).hom).Cotangent →+
        Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
          (definingIdealOfHom f) (f.base z),
      ∀ (b : f.coborderRange.toScheme.presheaf.stalk (f.liftCoborder.base z))
        (hb : b ∈ RingHom.ker (f.liftCoborder.stalkMap z).hom),
        θ ((RingHom.ker (f.liftCoborder.stalkMap z).hom).toCotangent ⟨b, hb⟩) =
          Submodule.Quotient.mk ⟨(coborderStalkEquiv f z).inv.hom b,
            coborderStalkEquiv_inv_mem_stalkIdeal f z b hb⟩ := by
  let _ : Module (f.coborderRange.toScheme.presheaf.stalk (f.liftCoborder.base z))
      (Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom f) (f.base z)) :=
    Module.compHom _ (coborderStalkEquiv f z).inv.hom
  have hsmul : ∀ (r : f.coborderRange.toScheme.presheaf.stalk (f.liftCoborder.base z))
      (t : Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom f) (f.base z)),
      r • t = ((coborderStalkEquiv f z).inv.hom r) • t := fun _ _ => rfl
  refine ⟨(Ideal.Cotangent.lift
    (M := Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
      (definingIdealOfHom f) (f.base z))
    { toFun := fun b => Submodule.Quotient.mk
        ⟨(coborderStalkEquiv f z).inv.hom b.1,
          coborderStalkEquiv_inv_mem_stalkIdeal f z b.1 b.2⟩
      map_add' := fun b b' =>
        mk_eq_add (coborderStalkEquiv_inv_mem_stalkIdeal f z b.1 b.2)
          (coborderStalkEquiv_inv_mem_stalkIdeal f z b'.1 b'.2) _
          (map_add (coborderStalkEquiv f z).inv.hom b.1 b'.1)
      map_smul' := fun r b => by
        rw [hsmul, RingHom.id_apply]
        exact mk_eq_smul _ (coborderStalkEquiv_inv_mem_stalkIdeal f z b.1 b.2) _
          (map_mul (coborderStalkEquiv f z).inv.hom r b.1) } ?_).toAddMonoidHom, fun b hb => rfl⟩
  intro w w'
  exact mk_eq_zero_of_mul (stalkIdeal_le_maximalIdeal f z)
    (coborderStalkEquiv_inv_mem_stalkIdeal f z w.1 w.2)
    (coborderStalkEquiv_inv_mem_stalkIdeal f z w'.1 w'.2) _
    (map_mul (coborderStalkEquiv f z).inv.hom w.1 w'.1)

end CotangentFibre


section Residue

open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.ClosedImmersion Stacks.Immersion

attribute [local instance] Stacks.Conormal.idealSheafStalkModule
  Stacks.Conormal.conormalSheafStalkModule Stacks.Conormal.stalkMapAlgebra
  Stacks.Conormal.cotangentStalkModule Stacks.AlgebraicGeometry.ambientStalkModule

variable {Z X : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] (z : Z)

/-- **The residue field of `X` at `f z` is a quotient of the local ring of `Z` at `z`.** -/
theorem exists_residueHom :
    ∃ ρ : Z.presheaf.stalk z →+*
        (X.presheaf.stalk (f.base z) ⧸
          IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base z))),
      ∀ c, ρ ((f.stalkMap z).hom c) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base z))) c := by
  have hJm : RingHom.ker (f.stalkMap z).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base z)) := by
    rw [← stalkIdeal_definingIdealOfHom_eq_ker f z]
    exact stalkIdeal_le_maximalIdeal f z
  refine ⟨(Ideal.Quotient.factor hJm).comp
    (RingHom.quotientKerEquivOfSurjective (f.stalkMap_surjective z)).symm.toRingHom,
    fun c => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingHom.quotientKerEquivOfSurjective_symm_apply]
  exact Ideal.Quotient.factor_mk hJm c

/-- Scalars of `X` act on the cotangent module of the coborder kernel through the coborder. -/
theorem cotangentStalk_smul_eq (c : X.presheaf.stalk (f.base z))
    (w : (RingHom.ker (f.liftCoborder.stalkMap z).hom).Cotangent) :
    ((f.stalkMap z).hom c) • w = ((coborderStalkEquiv f z).hom.hom c) • w := by
  change (RingHom.quotientKerEquivOfSurjective
      (f.liftCoborder.stalkMap_surjective z)).symm ((f.stalkMap z).hom c) • w = _
  rw [← stalkMap_coborderStalkEquiv f z, RingHom.quotientKerEquivOfSurjective_symm_apply,
    ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

end Residue


section Injectivity

open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.ClosedImmersion Stacks.Immersion
open Stacks.AlgebraicGeometry (idealCotangentFiberMap conormalSequenceLeftMap)

/-! ### An additive map out of a base change -/

/-- **A base change maps to a module over a third ring.** Let `Q` be a `P`-algebra, `Ns` a
`P`-module and `T` a module over a ring `R` and over `R ⧸ m` compatibly.  From a surjection
`σ : R → P`, a ring map `η : R → Q` factoring `σ`, a ring map `ρ : Q → R ⧸ m` splitting `η` and
an additive `σ`-semilinear `Θ : Ns → T`, one gets an additive `η`-semilinear map
`Q ⊗_P Ns ⟶ T` sending `q ⊗ n` to `ρ q • Θ n`. -/
theorem exists_tensorLift {R P Q Ns T : Type u} [CommRing R] [CommRing P] [CommRing Q]
    [Algebra P Q] [AddCommGroup Ns] [Module P Ns] [AddCommGroup T] [Module R T]
    (m : Ideal R) [Module (R ⧸ m) T]
    (hcompat : ∀ (c : R) (t : T), (Ideal.Quotient.mk m c) • t = c • t)
    (σ : R →+* P) (hσ : Function.Surjective σ) (η : R →+* Q)
    (hη : ∀ c, algebraMap P Q (σ c) = η c)
    (ρ : Q →+* R ⧸ m) (hρ : ∀ c, ρ (η c) = Ideal.Quotient.mk m c)
    (Θ : Ns →+ T) (hΘ : ∀ (c : R) (n : Ns), Θ ((σ c) • n) = c • Θ n) :
    ∃ G : TensorProduct P Q Ns →+ T,
      (∀ q n, G (q ⊗ₜ[P] n) = ρ q • Θ n) ∧
      ∀ (c : R) (t : TensorProduct P Q Ns), G ((η c) • t) = c • G t := by
  have hcomm : ∀ (c : R) (w : R ⧸ m) (t : T), w • (c • t) = c • (w • t) := by
    intro c w t
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [hcompat, hcompat, smul_smul, smul_smul, mul_comm]
  obtain ⟨F, hF⟩ : ∃ F : Q →+ (Ns →+ T), ∀ q n, F q n = ρ q • Θ n := by
    have hadd1 : ∀ (q : Q) (n n' : Ns), ρ q • Θ (n + n') = ρ q • Θ n + ρ q • Θ n' := by
      intro q n n'
      rw [map_add, smul_add]
    refine ⟨AddMonoidHom.mk' (fun q => AddMonoidHom.mk' (fun n => ρ q • Θ n) (hadd1 q)) ?_,
      fun q n => rfl⟩
    intro q q'
    refine AddMonoidHom.ext fun n => ?_
    change ρ (q + q') • Θ n = ρ q • Θ n + ρ q' • Θ n
    rw [map_add, add_smul]
  have hbal : ∀ (d : P) (q : Q) (n : Ns), F (d • q) n = F q (d • n) := by
    intro d q n
    rw [hF, hF]
    obtain ⟨c, rfl⟩ := hσ d
    rw [hΘ, Algebra.smul_def, hη, map_mul ρ, hρ, mul_smul, hcompat, hcomm]
  refine ⟨TensorProduct.liftAddHom F hbal,
    fun q n => (TensorProduct.liftAddHom_tmul F hbal q n).trans (hF q n), ?_⟩
  intro c t
  induction t using TensorProduct.inductionOn with
  | tmul q n =>
    rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul,
      hF, hF, smul_eq_mul, map_mul ρ, hρ, mul_smul, hcompat]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, smul_add, ht, ht']

/-! ### The cotangent fibre of a nested pair of immersions -/

attribute [local instance] Stacks.Conormal.idealSheafStalkModule
  Stacks.Conormal.conormalSheafStalkModule Stacks.Conormal.stalkMapAlgebra
  Stacks.Conormal.cotangentStalkModule

variable {Z Y X : Scheme.{u}}

/-- The local ring of `Z` at `z` as an algebra over the local ring of `Y` at `i z`. -/
abbrev stalkAlgebra (i : Z ⟶ Y) (z : Z) :
    Algebra (ToType (Y.presheaf.stalk (i.base z))) (ToType (Z.presheaf.stalk z)) :=
  (i.stalkMap z).hom.toAlgebra

attribute [local instance] stalkAlgebra

variable (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z)

/-- The pullback along `i` of the conormal sheaf of `j`. -/
abbrev leftConormalSheaf : Z.Modules :=
  (modulePullback i.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf j)

/-- The conormal sheaf of `i ≫ j`. -/
abbrev rightConormalSheaf : Z.Modules := Stacks.Conormal.conormalSheaf (i ≫ j)

/-- The stalk at `z` of the pulled-back conormal sheaf, over the local ring of `Z` at `z`. -/
abbrev leftStalkModule :
    Module (ToType (Z.presheaf.stalk z))
      (ToType ((leftConormalSheaf i j).presheaf.stalk z)) :=
  Stacks.AlgebraicGeometry.stalkModule (leftConormalSheaf i j) z

/-- The stalk at `z` of the conormal sheaf of `i ≫ j`, over the local ring of `Z` at `z`. -/
abbrev rightStalkModule :
    Module (ToType (Z.presheaf.stalk z))
      (ToType ((rightConormalSheaf i j).presheaf.stalk z)) :=
  Stacks.AlgebraicGeometry.stalkModule (rightConormalSheaf i j) z

/-- The stalk at `z` of the pulled-back conormal sheaf, over the local ring of `X` at `j (i z)`. -/
abbrev leftAmbientStalkModule :
    Module (X.presheaf.stalk (j.base (i.base z)))
      (ToType ((leftConormalSheaf i j).presheaf.stalk z)) :=
  Stacks.AlgebraicGeometry.ambientStalkModule i j (leftConormalSheaf i j) z

/-- The stalk at `z` of the conormal sheaf of `i ≫ j`, over the local ring of `X` at `j (i z)`. -/
abbrev rightAmbientStalkModule :
    Module (X.presheaf.stalk (j.base (i.base z)))
      (ToType ((rightConormalSheaf i j).presheaf.stalk z)) :=
  Stacks.AlgebraicGeometry.ambientStalkModule i j (rightConormalSheaf i j) z

attribute [local instance] leftStalkModule rightStalkModule leftAmbientStalkModule
  rightAmbientStalkModule

omit [IsImmersion i] in
/-- The germ of a section of the stalk ideal of `j`, transported to the coborder of `j`. -/
theorem mem_ker_hom (a : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
    (definingIdealOfHom j) (j.base (i.base z))) :
    (coborderStalkEquiv j (i.base z)).hom.hom a.1 ∈
      RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom :=
  coborderStalkEquiv_mem_ker j (i.base z) a.1
    (by rw [← stalkIdeal_definingIdealOfHom_eq_ker j (i.base z)]; exact a.2)

/-- The germ of a section of the stalk ideal of `i ≫ j`, transported to its coborder. -/
theorem mem_ker_hom_comp (b : Stacks.RingedSpace.stalkIdeal
    (X := X.toLocallyRingedSpace) (definingIdealOfHom (i ≫ j)) (j.base (i.base z))) :
    (coborderStalkEquiv (i ≫ j) z).hom.hom b.1 ∈
      RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom :=
  coborderStalkEquiv_mem_ker (i ≫ j) z b.1
    (by rw [← stalkIdeal_definingIdealOfHom_eq_ker (i ≫ j) z]; exact b.2)

omit [IsImmersion i] in
/-- Scalars of `X` act on the stalk of the pulled-back conormal sheaf through `i ≫ j`. -/
theorem smul_leftStalk_eq (c : X.presheaf.stalk (j.base (i.base z)))
    (w : ToType ((leftConormalSheaf i j).presheaf.stalk z)) :
    (((i ≫ j).stalkMap z).hom c) • w = c • w := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- Scalars of `X` act on the stalk of the conormal sheaf of `i ≫ j` through `i ≫ j`. -/
theorem smul_rightStalk_eq (c : X.presheaf.stalk (j.base (i.base z)))
    (w : ToType ((rightConormalSheaf i j).presheaf.stalk z)) :
    (((i ≫ j).stalkMap z).hom c) • w = c • w := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

omit [IsImmersion i] [IsImmersion j] in
/-- The structure map of the algebra of local rings is the stalk map of the composite. -/
theorem algebraMap_stalk_eq (c : X.presheaf.stalk (j.base (i.base z))) :
    algebraMap (ToType (Y.presheaf.stalk (i.base z))) (ToType (Z.presheaf.stalk z))
        ((j.stalkMap (i.base z)).hom c) = ((i ≫ j).stalkMap z).hom c := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- The germ of a conormal class is the inverse image of the cotangent class of the germ of its
section. -/
private theorem germ_canonicalConormalQuotientMap_eq_symm {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsImmersion f] (z : Z) (A : X.Opens) (hA : f.base z ∈ A)
    (y : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (op A))
    (a : X.presheaf.stalk (f.base z))
    (ha : (coborderStalkEquiv f z).hom.hom a ∈ RingHom.ker (f.liftCoborder.stalkMap z).hom)
    (hg : X.presheaf.germ A (f.base z) hA (Stacks.Conormal.idealSection f A y) = a) :
    TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf f).val.presheaf
        (f ⁻¹ᵁ A) z hA
        ((Stacks.Immersion.canonicalConormalQuotientMap f).val.app (op A) y) =
      (Stacks.Conormal.conormalSheafStalkEquivCotangent f z).symm
        ((RingHom.ker (f.liftCoborder.stalkMap z).hom).toCotangent
          ⟨(coborderStalkEquiv f z).hom.hom a, ha⟩) :=
  (LinearEquiv.eq_symm_apply _).mpr
    ((germ_canonicalConormalQuotientMap f z A hA y).trans
      (congrArg (RingHom.ker (f.liftCoborder.stalkMap z).hom).toCotangent
        (Subtype.ext (congrArg (coborderStalkEquiv f z).hom.hom hg))))

/-- **Injectivity of the map of cotangent fibres, given the germ-level data.** -/
theorem injective_aux (V : Z.Opens) (hzV : z ∈ V)
    (rr : (Scheme.Modules.restrictFunctor V.ι).obj (rightConormalSheaf i j) ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj (leftConormalSheaf i j))
    (hrr : (Scheme.Modules.restrictFunctor V.ι).map (conormalSequenceLeftMap i j) ≫ rr = 𝟙 _)
    (θ : (RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom).Cotangent →+
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j.base (i.base z)))
    (hθ : ∀ (b : j.coborderRange.toScheme.presheaf.stalk (j.liftCoborder.base (i.base z)))
      (hb : b ∈ RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom),
      θ ((RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom).toCotangent ⟨b, hb⟩) =
        Submodule.Quotient.mk ⟨(coborderStalkEquiv j (i.base z)).inv.hom b,
          coborderStalkEquiv_inv_mem_stalkIdeal j (i.base z) b hb⟩)
    (ρ : Z.presheaf.stalk z →+* (X.presheaf.stalk (j.base (i.base z)) ⧸
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base (i.base z)))))
    (hρ : ∀ c, ρ (((i ≫ j).stalkMap z).hom c) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base (i.base z)))) c)
    (eA : ToType ((leftConormalSheaf i j).presheaf.stalk z) ≃ₗ[ToType (Z.presheaf.stalk z)]
      TensorProduct (ToType (Y.presheaf.stalk (i.base z))) (ToType (Z.presheaf.stalk z))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u})
          (Stacks.Conormal.conormalSheaf j).val.presheaf (i.base z))))
    (heA : ∀ (W : Y.Opens) (hy : i.base z ∈ W)
      (s : (Stacks.Conormal.conormalSheaf j).val.obj (op W)),
      eA (TopCat.Presheaf.germ (C := Ab.{u}) (leftConormalSheaf i j).presheaf
          ((opensMap i.toLRSHom.toShHom).obj W) z hy
          (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
            (Stacks.Conormal.conormalSheaf j)).val.app (op W) s)) =
        (1 : ToType (Z.presheaf.stalk z)) ⊗ₜ[ToType (Y.presheaf.stalk (i.base z))]
          TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf j).val.presheaf
            W (i.base z) hy s) :
    Function.Injective (idealCotangentFiberMap i j z) := by
  classical
  have hθsmul : ∀ (c : X.presheaf.stalk (j.base (i.base z)))
      (w : (RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom).Cotangent),
      θ (((coborderStalkEquiv j (i.base z)).hom.hom c) • w) = c • θ w := by
    intro c w
    obtain ⟨b, rfl⟩ :=
      (RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom).toCotangent_surjective w
    rw [← map_smul (RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom).toCotangent,
      hθ _ b.2, hθ _ _]
    exact mk_eq_smul _ (coborderStalkEquiv_inv_mem_stalkIdeal j (i.base z) b.1 b.2) _
      ((map_mul (coborderStalkEquiv j (i.base z)).inv.hom _ b.1).trans
        (congrArg (fun w => w * (coborderStalkEquiv j (i.base z)).inv.hom b.1)
          (Iso.hom_inv_id_apply (coborderStalkEquiv j (i.base z)) c)))
  obtain ⟨Θ, hΘeq⟩ : ∃ Θ : ToType (TopCat.Presheaf.stalk (C := Ab.{u})
        (Stacks.Conormal.conormalSheaf j).val.presheaf (i.base z)) →+
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j.base (i.base z)),
      ∀ n, Θ n = θ (Stacks.Conormal.conormalSheafStalkEquivCotangent j (i.base z) n) :=
    ⟨θ.comp (Stacks.Conormal.conormalSheafStalkEquivCotangent
      j (i.base z)).toLinearMap.toAddMonoidHom, fun n => rfl⟩
  have hΘ : ∀ (c : X.presheaf.stalk (j.base (i.base z))) (n), Θ
      (((j.stalkMap (i.base z)).hom c) • n) = c • Θ n := by
    intro c n
    rw [hΘeq, hΘeq, map_smul, cotangentStalk_smul_eq j (i.base z) c, hθsmul]
  obtain ⟨G, hGt, hGsmul⟩ := exists_tensorLift
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base (i.base z))))
    (quotientMk_smul _) (j.stalkMap (i.base z)).hom (j.stalkMap_surjective (i.base z))
    ((i ≫ j).stalkMap z).hom
    (algebraMap_stalk_eq i j z) ρ hρ Θ hΘ
  obtain ⟨pp, hpp⟩ : ∃ pp : ToType ((leftConormalSheaf i j).presheaf.stalk z) →ₗ[
      X.presheaf.stalk (j.base (i.base z))]
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j.base (i.base z)),
      ∀ ξ, pp ξ = G (eA ξ) :=
    ⟨{ toFun := fun ξ => G (eA ξ)
       map_add' := fun ξ η => (congrArg G (map_add eA ξ η)).trans (map_add G (eA ξ) (eA η))
       map_smul' := fun c ξ =>
         (congrArg G ((congrArg eA (smul_leftStalk_eq i j z c ξ).symm).trans
           (map_smul eA (((i ≫ j).stalkMap z).hom c) ξ))).trans (hGsmul c (eA ξ)) },
      fun ξ => rfl⟩
  refine Stacks.AlgebraicGeometry.injective_idealCotangentFiberMap_of_conormalClasses i j z
    (conormalSequenceLeftMap i j) V hzV rr hrr
    (fun a => eA.symm ((1 : ToType (Z.presheaf.stalk z)) ⊗ₜ
      ((Stacks.Conormal.conormalSheafStalkEquivCotangent j (i.base z)).symm
        ((RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom).toCotangent
          ⟨(coborderStalkEquiv j (i.base z)).hom.hom a.1, mem_ker_hom i j z a⟩))))
    (fun b => (Stacks.Conormal.conormalSheafStalkEquivCotangent (i ≫ j) z).symm
      ((RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom).toCotangent
        ⟨(coborderStalkEquiv (i ≫ j) z).hom.hom b.1, mem_ker_hom_comp i j z b⟩))
    ?_ ?_ ?_
    pp ?_
  · intro b b'
    refine Eq.trans (congrArg (fun w => (Stacks.Conormal.conormalSheafStalkEquivCotangent
      (i ≫ j) z).symm ((RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom).toCotangent w))
      (Subtype.ext (map_add (coborderStalkEquiv (i ≫ j) z).hom.hom b.1 b'.1) :
        (⟨_, mem_ker_hom_comp i j z (b + b')⟩ :
          RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom) =
          ⟨_, mem_ker_hom_comp i j z b⟩ + ⟨_, mem_ker_hom_comp i j z b'⟩)) ?_
    exact (congrArg (fun w => (Stacks.Conormal.conormalSheafStalkEquivCotangent (i ≫ j) z).symm w)
        (map_add (RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom).toCotangent _ _)).trans
      (map_add (Stacks.Conormal.conormalSheafStalkEquivCotangent (i ≫ j) z).symm _ _)
  · intro c b
    refine Eq.trans (congrArg (fun w => (Stacks.Conormal.conormalSheafStalkEquivCotangent
      (i ≫ j) z).symm ((RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom).toCotangent w))
      (Subtype.ext (map_mul (coborderStalkEquiv (i ≫ j) z).hom.hom c b.1) :
        (⟨_, mem_ker_hom_comp i j z (c • b)⟩ :
          RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom) =
          (coborderStalkEquiv (i ≫ j) z).hom.hom c • ⟨_, mem_ker_hom_comp i j z b⟩)) ?_
    exact (congrArg (fun w => (Stacks.Conormal.conormalSheafStalkEquivCotangent (i ≫ j) z).symm w)
        ((map_smul (RingHom.ker ((i ≫ j).liftCoborder.stalkMap z).hom).toCotangent _ _).trans
          (cotangentStalk_smul_eq (i ≫ j) z c _).symm)).trans
      ((map_smul (Stacks.Conormal.conormalSheafStalkEquivCotangent (i ≫ j) z).symm _ _).trans
        (smul_rightStalk_eq i j z c _))
  · intro a ha
    obtain ⟨A₀, hA₀, s, hs, hgerm⟩ := (Stacks.RingedSpace.mem_stalkIdeal_iff _).mp a.2
    obtain ⟨y₀, hy₀⟩ := (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff
      (f := j) (O := A₀) s).mpr ((mem_definingIdealOfHom j A₀ s).mp hs)
    obtain ⟨E, hE⟩ := (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff
      (f := i ≫ j) (O := A₀) s).mpr
        ((congrArg (Scheme.Hom.app i (j ⁻¹ᵁ A₀)).hom ((mem_definingIdealOfHom j A₀ s).mp hs)).trans
          (map_zero (Scheme.Hom.app i (j ⁻¹ᵁ A₀)).hom))
    have hgj : X.presheaf.germ A₀ (j.base (i.base z)) hA₀
        (Stacks.Conormal.idealSection j A₀ y₀) = a.1 :=
      (congrArg (X.presheaf.germ A₀ (j.base (i.base z)) hA₀) hy₀).trans hgerm
    have hgf : X.presheaf.germ A₀ ((i ≫ j).base z) hA₀
        (Stacks.Conormal.idealSection (i ≫ j) A₀ E) = a.1 :=
      (congrArg (X.presheaf.germ A₀ ((i ≫ j).base z) hA₀) hE).trans hgerm
    have hn := germ_canonicalConormalQuotientMap_eq_symm j (i.base z) A₀ hA₀ y₀ a.1
      (mem_ker_hom i j z a) hgj
    have hcIa : eA.symm ((1 : ToType (Z.presheaf.stalk z)) ⊗ₜ
        ((Stacks.Conormal.conormalSheafStalkEquivCotangent j (i.base z)).symm
          ((RingHom.ker (j.liftCoborder.stalkMap (i.base z)).hom).toCotangent
            ⟨(coborderStalkEquiv j (i.base z)).hom.hom a.1, mem_ker_hom i j z a⟩))) =
        TopCat.Presheaf.germ (C := Ab.{u}) (leftConormalSheaf i j).presheaf
          ((opensMap i.toLRSHom.toShHom).obj (j ⁻¹ᵁ A₀)) z hA₀
          (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
            (Stacks.Conormal.conormalSheaf j)).val.app (op (j ⁻¹ᵁ A₀))
            ((Stacks.Immersion.canonicalConormalQuotientMap j).val.app (op A₀) y₀)) :=
      (LinearEquiv.symm_apply_eq eA).mpr
        ((congrArg (fun w => TensorProduct.tmul (ToType (Y.presheaf.stalk (i.base z)))
            (1 : ToType (Z.presheaf.stalk z)) w) hn.symm).trans
          (heA (j ⁻¹ᵁ A₀) hA₀ _).symm)
    have hfin := germ_canonicalConormalQuotientMap_eq_symm (i ≫ j) z A₀ hA₀ E a.1
      (mem_ker_hom_comp i j z ⟨a.1, ha⟩) hgf
    exact (congrArg (fun w => Stacks.AlgebraicGeometry.stalkHom
          (conormalSequenceLeftMap i j) z w) hcIa).trans
      ((stalkHom_conormalSequenceLeftMap_conormalClass i j z A₀ hA₀ hA₀ y₀ E
        (hE.trans hy₀.symm)).trans hfin)
  · intro a
    refine (hpp _).trans ((congrArg G (eA.apply_symm_apply _)).trans ((hGt _ _).trans ?_))
    refine (congrArg (fun w => w • Θ _) (map_one ρ)).trans ((one_smul _ _).trans ?_)
    refine (hΘeq _).trans ((congrArg θ
      ((Stacks.Conormal.conormalSheafStalkEquivCotangent
        j (i.base z)).apply_symm_apply _)).trans ?_)
    refine (hθ _ (mem_ker_hom i j z a)).trans ?_
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (Iso.hom_inv_id_apply (coborderStalkEquiv j (i.base z)) a.1) :
        (⟨_, _⟩ : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
          (definingIdealOfHom j) (j.base (i.base z))) = ⟨_, a.2⟩)

end Injectivity


end Stacks.Conormal

namespace Stacks.AlgebraicGeometry

open Stacks.Conormal

/-- **The map of cotangent fibres of a locally split conormal sequence is injective.**
Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions whose conormal sequence is exact and locally
split and let `z : Z`.  Then the map `I_x / 𝔪_x I_x ⟶ J_x / 𝔪_x J_x` of cotangent fibres at
`x = j (i z)` of the defining ideals of `j` and of `i ≫ j` is injective.

This is the step of [Stacks Project, Tag 068Z] that makes the local generators of the ideal of
`Y` part of a minimal generating family of the ideal of `Z`. -/
theorem injective_idealCotangentFiberMap {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.IsImmersion j]
    (hS : IsSplitExactConormalSequence i j) (z : Z) :
    Function.Injective (idealCotangentFiberMap i j z) := by
  obtain ⟨V, hzV, rr, hrr⟩ := hS.locallySplit z
  obtain ⟨θ, hθ⟩ := exists_conormalCotangentFibreMap j (i.base z)
  obtain ⟨ρ, hρ⟩ := exists_residueHom (i ≫ j) z
  obtain ⟨eA, heA⟩ := exists_modulePullbackStalkLinearEquiv i.toLRSHom.toShHom
    (Stacks.Conormal.conormalSheaf j) z
  exact injective_aux i j z V hzV rr hrr θ hθ ρ hρ eA heA

end Stacks.AlgebraicGeometry

end
