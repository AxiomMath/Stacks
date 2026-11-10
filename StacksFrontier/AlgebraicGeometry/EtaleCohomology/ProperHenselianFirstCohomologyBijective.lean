module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteDirectImageEffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomology
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFiniteCase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# First étale cohomology of a proper scheme over a henselian local ring

Let `A` be a henselian local ring, `f : X ⟶ Spec A` proper with closed fibre `X₀`, and `M` a
finite abelian group. This file proves [Stacks, Tag 0A5G]: restriction
`H¹(X, M) ⟶ H¹(X₀, M)` is bijective. A class on either side is the class of an `M`-torsor, a
torsor is represented by a scheme finite étale over the base (Stacks 03AJ, 03RV), and base change
to the closed fibre is an equivalence on finite étale covers (Stacks 0A48,
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing`). The
cohomological half of the argument is
`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_constantSheaf_one`.

The same argument gives surjectivity of restriction on `H¹(X, g_* M)` for `g : Y ⟶ X` finite,
the form in which Stacks 0A5G is used in the proof of Stacks 0A5H.

The argument uses Grothendieck existence in the form of this library's Stacks 0A48.

## Main results

* `Stacks.EtaleCohomology.exists_closedFibreInclusion_mem_of_isClosed` — every nonempty closed
  subset of a scheme universally closed over a local ring meets the closed fibre.
* `Stacks.EtaleCohomology.bijective_etaleConstantCohomologyRestriction_one_of_isProper` —
  [Stacks, Tag 0A5G].
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_directImage_closedFibre_one`
  — surjectivity of restriction on `H¹` of the pushforward of a finite constant sheaf along a
  finite morphism.

## Implementation notes

Coefficients are `AddCommGrpCat.{u + 1}`, `M` lives in `Type`, and `Ext` is taken in the
universe `u + 1`; these are the universes of the torsor description of `H¹`.

## References

* [Stacks Project, Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Every nonempty closed subset of a scheme universally closed over a local ring meets the
closed fibre.** Its image in `Spec A` is closed and nonempty, so it contains the closed point,
which every point of `Spec A` specializes to. -/
theorem exists_closedFibreInclusion_mem_of_isClosed (A : Type u) [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [UniversallyClosed f] (C : Set X) (hC : IsClosed C)
    (hne : C.Nonempty) : ∃ z, (closedFibreInclusion A f).base z ∈ C := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨x', hx', hfx'⟩ := (IsLocalRing.specializes_closedPoint (f.base x)).mem_closed
    (f.isClosedMap C hC) ⟨x, hx, rfl⟩
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have : IsLocalHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let k₀ : Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)) :=
    IsLocalRing.closedPoint (A ⧸ IsLocalRing.maximalIdeal A)
  have hk : f.base x' = (residueFieldPoint A).base k₀ := by
    rw [hfx']
    exact (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).symm
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x' k₀ hk
  exact ⟨z, hz ▸ hx'⟩

/-- **The meeting property passes to the base change along a universally closed morphism.** If
every nonempty closed subset of `X` meets the image of `i : Z ⟶ X`, and `f : Y ⟶ X` is
universally closed, then every nonempty closed subset of `Y` meets the image of
`Y ×_X Z ⟶ Y`. -/
theorem exists_pullback_fst_mem_of_isClosed {X Y Z : Scheme.{u}} (i : Z ⟶ X)
    (hmeet : ∀ C : Set X, IsClosed C → C.Nonempty → ∃ z, i.base z ∈ C) (f : Y ⟶ X)
    [UniversallyClosed f] (C : Set Y) (hC : IsClosed C) (hne : C.Nonempty) :
    ∃ z, (pullback.fst f i).base z ∈ C := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z, y, hy, hyz⟩ := hmeet _ (f.isClosedMap C hC) ⟨f.base x, x, hx, rfl⟩
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y z hyz
  exact ⟨w, hw ▸ hy⟩

/-! ### Stacks 0A48 along the closed fibre -/

/-- **Stacks 0A48 for the closed-fibre inclusion**: for `A` henselian local and `f` proper, base
change along `X₀ ⟶ X` is an equivalence on finite étale covers. -/
theorem isEquivalence_finiteEtaleBaseChange_closedFibreInclusion (A : Type u) [CommRing A]
    [HenselianLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange (closedFibreInclusion A f)).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing A f

/-- **Stacks 0A48 for `Y ×_X X₀ ⟶ Y`**, for `X` proper over a henselian local ring `A` and
`f : Y ⟶ X` proper: `Y ×_X X₀` is the closed fibre of `Y` over `A`, by pasting of pullbacks, and
base change to the closed fibre of `Y` is an equivalence on finite étale covers. -/
@[sga "4 XII 5.9bis" "more general", sga "4½ Arcata 4.2.2" "more general"]
theorem isEquivalence_finiteEtaleBaseChange_pullback_fst_closedFibreInclusion
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsProper p] (f : Y ⟶ X) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f (closedFibreInclusion A p))).IsEquivalence := by
  have h : pullback.fst f (closedFibreInclusion A p) =
      (pullbackRightPullbackFstIso p (residueFieldPoint A) f).hom ≫
        closedFibreInclusion A (f ≫ p) :=
    (pullbackRightPullbackFstIso_hom_fst p (residueFieldPoint A) f).symm
  rw [h]
  exact isEquivalence_finiteEtaleBaseChange_isIso_comp
    (pullbackRightPullbackFstIso p (residueFieldPoint A) f).hom (closedFibreInclusion A (f ≫ p))
    (isEquivalence_finiteEtaleBaseChange_closedFibreInclusion A (f ≫ p))

/-! ### `H¹` of the pushforward of a finite constant sheaf along a finite morphism -/

section DirectImage

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {X Y Z : Scheme.{u}}

/-- In a commutative square `a ≫ b = c ≫ d` of abelian groups, `c` is surjective as soon as `a`
and `b` are surjective and `d` is injective. -/
theorem surjective_of_comp_eq_comp {A B C D : AddCommGrpCat.{u + 1}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D) (h : a ≫ b = c ≫ d) (ha : Function.Surjective a)
    (hb : Function.Surjective b) (hd : Function.Injective d) : Function.Surjective c := by
  intro y
  obtain ⟨x, hx⟩ := (hb.comp ha) (d y)
  refine ⟨x, hd ?_⟩
  rwa [← ConcreteCategory.comp_apply c d x, ← h, ConcreteCategory.comp_apply]

/-- An étale scheme with finite structure morphism stays one under base change. -/
theorem isFinite_smallEtaleBaseChange_obj_hom {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Etale)
    [IsFinite V.hom] : IsFinite ((smallEtaleBaseChange f).obj V).hom :=
  inferInstanceAs (IsFinite (pullback.snd V.hom f))

/-- The comparison of the two composite direct images around the base change square of
`f : Y ⟶ X` along `i : Z ⟶ X`, as a 2-square. -/
def directImageCompTwoSquare {X Y : Scheme.{u}} (i : Z ⟶ X) (f : Y ⟶ X) :
    TwoSquare (etaleAbelianDirectImage.{u, 0} (pullback.fst f i))
      (etaleAbelianDirectImage.{u, 0} (pullback.snd f i)) (etaleAbelianDirectImage.{u, 0} f)
      (etaleAbelianDirectImage.{u, 0} i) :=
  TwoSquare.mk _ _ _ _
    ((etaleAbelianDirectImageCompIso'.{u, 0} (pullback.fst f i) f
        (pullback.fst f i ≫ f) rfl).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, 0} (pullback.snd f i) i
        (pullback.fst f i ≫ f) pullback.condition).inv)

/-- The comparison of the two composite direct images around the base change square of
`f : Y ⟶ X` along `i : Z ⟶ X` is an isomorphism. -/
instance {X Y : Scheme.{u}} (i : Z ⟶ X) (f : Y ⟶ X) :
    IsIso (directImageCompTwoSquare i f) :=
  inferInstanceAs (IsIso ((etaleAbelianDirectImageCompIso'.{u, 0} (pullback.fst f i) f
      (pullback.fst f i ≫ f) rfl).hom ≫
    (etaleAbelianDirectImageCompIso'.{u, 0} (pullback.snd f i) i
      (pullback.fst f i ≫ f) pullback.condition).inv))

/-- **The unit along `i` at a direct image, followed by the base change map, is the direct image
of the unit along `Y ×_X Z ⟶ Y`**, up to the comparison of the two composite direct images. This
is the base change map as the mate along the horizontal adjunctions. -/
theorem etaleAbelianDirectImage_map_unit_comp_directImageCompTwoSquare {X Y : Scheme.{u}}
    (i : Z ⟶ X) (f : Y ⟶ X) (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianDirectImage.{u, 0} f).map
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (pullback.fst f i)).unit.app Q) ≫
        (directImageCompTwoSquare i f).app
          ((etaleAbelianInverseImage.{u, 0} (pullback.fst f i)).obj Q) =
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app
          ((etaleAbelianDirectImage.{u, 0} f).obj Q) ≫
        (etaleAbelianDirectImage.{u, 0} i).map
          ((etaleAbelianBaseChange.{u, 0} f i (pullback.fst f i) (pullback.snd f i)
            pullback.condition).app Q) := by
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0} f i
    (pullback.fst f i) (pullback.snd f i) pullback.condition (pullback.fst f i ≫ f) rfl
    pullback.condition]
  exact unit_mateEquiv_symm _ _ (directImageCompTwoSquare i f) Q

/-- A component of an isomorphism of abelian sheaves is bijective on sections. -/
theorem bijective_hom_app_of_isIso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [IsIso φ]
    (U : X.Etale) : Function.Bijective (φ.hom.app (op U)) :=
  ConcreteCategory.bijective_of_isIso (((sheafToPresheaf _ _).map φ).app (op U))

/-- The direct image of the unit along `Y ×_X Z ⟶ Y`, on global sections, is the unit on sections
over the finite étale `Y`-scheme `Y ×_X X`; it is surjective on a finite locally constant sheaf. -/
theorem surjective_etaleAbelianDirectImage_map_unit_app_terminal {X Y P : Scheme.{u}}
    (i' : P ⟶ Y) (f : Y ⟶ X) [(finiteEtaleBaseChange i').Full]
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj Q)] :
    Function.Surjective (((etaleAbelianDirectImage.{u, 0} f).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i').unit.app Q)).hom.app
        (op (⊤_ X.Etale))) := by
  have := isFinite_terminal_hom X
  exact surjective_etaleAbelianUnit_app_of_isFiniteLocallyConstant i' Q
    (isFinite_smallEtaleBaseChange_obj_hom f (⊤_ X.Etale))

/-- The mate identity of `etaleAbelianDirectImage_map_unit_comp_directImageCompTwoSquare` on
global sections. -/
theorem etaleAbelianDirectImage_map_unit_comp_directImageCompTwoSquare_app {X Y : Scheme.{u}}
    (i : Z ⟶ X) (f : Y ⟶ X) (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((etaleAbelianDirectImage.{u, 0} f).map
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (pullback.fst f i)).unit.app Q)).hom.app
          (op (⊤_ X.Etale)) ≫
      ((directImageCompTwoSquare i f).app
        ((etaleAbelianInverseImage.{u, 0} (pullback.fst f i)).obj Q)).hom.app (op (⊤_ X.Etale)) =
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app
        ((etaleAbelianDirectImage.{u, 0} f).obj Q)).hom.app (op (⊤_ X.Etale)) ≫
      ((etaleAbelianDirectImage.{u, 0} i).map
        ((etaleAbelianBaseChange.{u, 0} f i (pullback.fst f i) (pullback.snd f i)
          pullback.condition).app Q)).hom.app (op (⊤_ X.Etale)) :=
  congrArg (fun k => k.hom.app (op (⊤_ X.Etale)))
    (etaleAbelianDirectImage_map_unit_comp_directImageCompTwoSquare i f Q)

/-- The comparison of the two composite direct images is bijective on global sections. -/
theorem bijective_directImageCompTwoSquare_app {X Y : Scheme.{u}} (i : Z ⟶ X) (f : Y ⟶ X)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (((directImageCompTwoSquare i f).app
      ((etaleAbelianInverseImage.{u, 0} (pullback.fst f i)).obj Q)).hom.app (op (⊤_ X.Etale))) :=
  bijective_hom_app_of_isIso _ _

/-- The base change map of a finite morphism is injective on global sections after direct image
along `i`. -/
theorem injective_directImage_map_etaleAbelianBaseChange_app {X Y : Scheme.{u}} (i : Z ⟶ X)
    (f : Y ⟶ X) [IsFinite f] (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Injective (((etaleAbelianDirectImage.{u, 0} i).map
      ((etaleAbelianBaseChange.{u, 0} f i (pullback.fst f i) (pullback.snd f i)
        pullback.condition).app Q)).hom.app (op (⊤_ X.Etale))) := by
  have : IsIso (etaleAbelianBaseChange.{u, 0} f i (pullback.fst f i) (pullback.snd f i)
      pullback.condition) :=
    isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite f i _ _ (IsPullback.of_hasPullback f i)
  exact (bijective_hom_app_of_isIso _ _).1

/-- **Restriction of global sections of `f_* Q` to `Z` is surjective**, for `f : Y ⟶ X` finite and
`Q` a finite locally constant sheaf on `Y_étale`, when base change along `Y ×_X Z ⟶ Y` is full on
finite étale covers. By the base change isomorphism `(f_* Q)|_Z ≅ f'_* (Q|_{Y ×_X Z})` (Stacks
0959), read as the mate along the two horizontal adjunctions
(`etaleAbelianDirectImage_map_unit_comp_directImageCompTwoSquare`), the unit of `f_* Q` on global
sections is the unit of `Q` on sections over the finite étale `Y`-scheme `Y ×_X X`, up to
isomorphisms. -/
theorem surjective_etaleAbelianUnit_app_directImage_terminal {X Y : Scheme.{u}} (i : Z ⟶ X)
    (f : Y ⟶ X) [IsFinite f] [(finiteEtaleBaseChange (pullback.fst f i)).Full]
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj Q)] :
    Function.Surjective (((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app
      ((etaleAbelianDirectImage.{u, 0} f).obj Q)).hom.app (op (⊤_ X.Etale))) :=
  surjective_of_comp_eq_comp _ _ _ _
    (etaleAbelianDirectImage_map_unit_comp_directImageCompTwoSquare_app i f Q)
    (surjective_etaleAbelianDirectImage_map_unit_app_terminal (pullback.fst f i) f Q)
    (bijective_directImageCompTwoSquare_app i f Q).2
    (injective_directImage_map_etaleAbelianBaseChange_app i f Q)

/-- **Restriction `H¹(X, f_* M) ⟶ H¹(Z, (f_* M)|_Z)` is surjective for `f` finite and `M` a finite
abelian group**, when base change along `Y ×_X Z ⟶ Y` is an equivalence of categories of finite
étale covers and every nonempty closed subset of `Y` meets its image.

A class `ζ` is read on `Y ×_X Z` (Stacks 0959 and the finiteness of `Y ×_X Z ⟶ Z`), where it dies
on the base change of a surjective finite étale `π : W ⟶ Y`
(`exists_finite_etale_surjective_restriction_eq_zero`); hence `ζ` dies in
`(f_* π_* π⁻¹ M)|_Z` (`comp_directImage_unit_eq_zero_of_restriction_eq_zero`). The short exact
sequence `f_*` of `0 → M → π_* π⁻¹ M → Q → 0` has quotient `f_* Q`, on whose global sections
restriction to `Z` is surjective: by the base change isomorphism, read as the mate along the two
horizontal adjunctions (`etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`), it is
restriction of the sections of the finite locally constant sheaf `Q` over the finite étale
`Y`-scheme `Y ×_X X`. So `ζ` is the restriction of a boundary
(`exists_etaleCohomologyRestrictionMap_one_eq_of_comp_eq_zero`). -/
theorem surjective_etaleCohomologyRestrictionMap_directImage_constantSheaf_one {X Y : Scheme.{u}}
    (i : Z ⟶ X) (f : Y ⟶ X) [IsFinite f]
    [(finiteEtaleBaseChange (pullback.fst f i)).IsEquivalence]
    (hmeet : ∀ C : Set Y, IsClosed C → C.Nonempty → ∃ z, (pullback.fst f i).base z ∈ C)
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i
      ((etaleAbelianDirectImage.{u, 0} f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) 1) := by
  intro ζ
  let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  have sq := IsPullback.of_hasPullback f i
  let θ := finiteDirectImageTransport f i (pullback.fst f i) (pullback.snd f i) sq A 1 ζ
  let cI := (etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst f i)).app M
  obtain ⟨W, π, hπf, hπe, hπs, hres⟩ := exists_finite_etale_surjective_restriction_eq_zero
    (pullback.fst f i) hmeet M (θ.comp (Ext.mk₀ cI.hom) (add_zero 1))
  have h0 : etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π (pullback.fst f i)) _ 1
      θ = 0 := by
    rw [etaleCohomologyRestrictionMap_comp_mk₀] at hres
    exact (Stacks.ExtAdjunction.comp_mk₀_eq_zero_iff_of_isIso _ _).1 hres
  have hk := comp_directImage_unit_eq_zero_of_restriction_eq_zero f i (pullback.fst f i)
    (pullback.snd f i) sq π (pullback.fst π (pullback.fst f i))
    (pullback.snd π (pullback.fst f i)) (IsPullback.of_hasPullback _ _) A 1 ζ h0
  have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app A) :=
    mono_etaleAbelianUnit_of_surjective π A
  let S₀ := ShortComplex.mk ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app A)
    (cokernel.π _) (cokernel.condition _)
  have hS₀ : S₀.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have : (etaleAbelianDirectImage.{u, 0} f).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).isRightAdjoint
  have hS := hS₀.map_of_exact (etaleAbelianDirectImage.{u, 0} f)
  have := isFiniteLocallyConstant_forget_cokernel_unit π M
  exact exists_etaleCohomologyRestrictionMap_one_eq_of_comp_eq_zero i hS
    ((surjective_etaleCohomologyRestrictionMap_zero_iff i
      ((etaleAbelianDirectImage.{u, 0} f).obj S₀.X₃)).2
        (surjective_etaleAbelianUnit_app_directImage_terminal i f S₀.X₃)) ζ hk

end DirectImage

/-! ### Stacks 0A5G -/

section FirstCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Restriction `H¹(X, f_* M) ⟶ H¹(X₀, (f_* M)|_{X₀})` to the closed fibre is surjective**, for
`X` proper over a henselian local ring `A`, `f : Y ⟶ X` finite and `M` a finite abelian group,
through Stacks 0A48 for `Y`. -/
theorem surjective_etaleCohomologyRestrictionMap_directImage_closedFibre_one
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsProper p] (f : Y ⟶ X) [IsFinite f]
    (N : AddCommGrpCat.{u + 1}) [Finite N] :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion A p)
      ((etaleAbelianDirectImage.{u, 0} f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N)) 1) := by
  have := isEquivalence_finiteEtaleBaseChange_pullback_fst_closedFibreInclusion A p f
  exact surjective_etaleCohomologyRestrictionMap_directImage_constantSheaf_one
    (closedFibreInclusion A p) f
    (exists_pullback_fst_mem_of_isClosed _ (exists_closedFibreInclusion_mem_of_isClosed A p) f) N

/-- Composing degree-one `Ext`-classes with an isomorphism in degree zero is bijective. -/
private theorem bijective_comp_mk₀_hom {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C]
    {P Y Z : C} (e : Y ≅ Z) :
    Function.Bijective fun z : Ext.{u + 1} P Y 1 => z.comp (Ext.mk₀ e.hom) (add_zero 1) :=
  ⟨fun x y h => by
    simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Ext.comp_mk₀_id] using congrArg (fun z => z.comp (Ext.mk₀ e.inv) (add_zero 1)) h,
   fun y => ⟨y.comp (Ext.mk₀ e.inv) (add_zero 1), by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id,
      Ext.comp_mk₀_id]⟩⟩

/-- **The surjective half of [Stacks, Tag 0A5G]**: for `A` a henselian local ring, `X` proper over
`A` and `M` a finite abelian group, restriction `H¹(X, M) ⟶ H¹(X₀, M)` to the closed fibre is
surjective.

A class on `X₀` is the class of an `M`-torsor, which is represented by a scheme finite étale over
`X₀` ([Stacks, Tag 03AJ], [Stacks, Tag 03RV]); by Stacks 0A48 that scheme is the closed fibre of a
finite étale cover of `X`, and the class is the restriction of a boundary in the short exact
sequence attached to that cover
(`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_constantSheaf_one`). -/
@[sga "4 XII 5.5" "(ii), (iii)", sga "4 XII 5.9.0" "partial"]
theorem surjective_etaleConstantCohomologyRestriction_one_of_isProper
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (M : Type) [AddCommGroup M] [Finite M] :
    Function.Surjective (etaleConstantCohomologyRestriction.{u, 0, u + 1} A f M 1) := by
  have := isEquivalence_finiteEtaleBaseChange_closedFibreInclusion A f
  have : Finite (AddCommGrpCat.of (ULift.{u + 1, 0} M)) := inferInstanceAs (Finite (ULift M))
  exact (bijective_comp_mk₀_hom _).2.comp
    (surjective_etaleCohomologyRestrictionMap_constantSheaf_one (closedFibreInclusion A f)
      (exists_closedFibreInclusion_mem_of_isClosed A f) (AddCommGrpCat.of (ULift.{u + 1, 0} M)))

/-- For `A` a henselian local ring, `X` proper over `A` and `M` a finite abelian group,
restriction `H¹(X, M) ⟶ H¹(X₀, M)` to the closed fibre is bijective.

Surjectivity is `surjective_etaleConstantCohomologyRestriction_one_of_isProper`. Injectivity
(`Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_constantSheaf_one`): a class on
`X` dies on a surjective finite étale cover `π`, hence is a boundary of a section of the quotient
`Q` of `M ⟶ π_* π⁻¹ M`; restriction to `X₀` is surjective on sections of `π_* π⁻¹ M` and injective
on sections of `Q`, both being finite locally constant and base change to `X₀` being fully faithful
on finite étale covers (Stacks 0A48). -/
@[stacks 0A5G]
theorem bijective_etaleConstantCohomologyRestriction_one_of_isProper
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (M : Type) [AddCommGroup M] [Finite M] :
    Function.Bijective (etaleConstantCohomologyRestriction.{u, 0, u + 1} A f M 1) := by
  refine ⟨?_, surjective_etaleConstantCohomologyRestriction_one_of_isProper A f M⟩
  have := isEquivalence_finiteEtaleBaseChange_closedFibreInclusion A f
  have : Finite (AddCommGrpCat.of (ULift.{u + 1, 0} M)) := inferInstanceAs (Finite (ULift M))
  exact (bijective_comp_mk₀_hom _).1.comp
    (injective_etaleCohomologyRestrictionMap_constantSheaf_one (closedFibreInclusion A f)
      (AddCommGrpCat.of (ULift.{u + 1, 0} M)))

end FirstCohomology

end Stacks.EtaleCohomology

end
