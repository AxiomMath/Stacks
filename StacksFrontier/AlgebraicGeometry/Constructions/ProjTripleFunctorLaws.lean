module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTriplePullback
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict

/-!
# The two functor laws for the pullback of a triple

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring. A *triple* over a scheme `Y`, in the sense of Section
27.12, is an integer `d ≥ 1`, an invertible `𝒪_Y`-module `L` and a graded ring map
`ψ : A^{(d)} ⟶ Γ_*(Y, L)` whose degree-`d` values generate `L`, and
`Stacks.AlgebraicGeometry.ProjTriplePullback.pullbackTriple` pulls a triple back along a morphism
of schemes. The pullback of a triple along an identity is strictly equivalent
(`Stacks.AlgebraicGeometry.ProjTripleClassifying.SectionsEquiv`) to the triple, and the pullback
along a composite is strictly equivalent to the twice-pulled-back triple.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackNatTensorPowIso_inv_comp_congr`: the
  comparison `(𝟙 Y)^*(L ^⊗ n) ⟶ ((𝟙 Y)^*L) ^⊗ n` of [Stacks, Tag 01CD] iterated, followed by the
  `n`-th tensor power of the identity law `β : (𝟙 Y)^*L ≅ L`, is the identity law at `L ^⊗ n`.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.congr_hom_app_pullSection_id`: the `n`-th tensor
  power of `β` carries the pullback along `𝟙 Y` of a global section of `L ^⊗ n` to that section.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.sectionsEquiv_pullbackSections_id`:
  `(𝟙 Y)^* ∘ ψ` is strictly equivalent to `ψ`.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.sectionsEquiv_pullbackTriple_id`: the identity
  functor law of Section 27.12.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackCompIso_hom_app_tensorUnit` and
  `pullbackCompIso_comp_pullbackNatTensorPowIso_inv`: the composition law for the comparison of
  the tensor powers, in degree zero and in every degree.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackSectionHom_comp`: pulling a global
  section back along a composite is pulling it back twice, read through the composition law.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.congr_hom_app_pullSection_comp` and
  `sectionsEquiv_pullbackSections_comp`: the same on sections, and for the graded map of a
  triple.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackNatTensorPowIso_inv_one_comp_unitorPow`
  and `unitorPow_hom_app_pullSection_one`: in degree one the comparison of [Stacks, Tag 01CD] is
  compatible with the two left unitors, as an identity of morphisms and on sections.
* `Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.sectionsEquiv_pullbackTriple_comp`: the
  composition functor law of Section 27.12.

## Implementation notes

`Stacks.PullbackUnitSection.unitPullbackHom` is by definition
`Stacks.PullbackTensorCoherence.pullbackUnitComparison` conjugated by the comparison of the two
unit objects, but a goal in which a tactic has performed that unfolding is not type-correct at the
transparency the rewriting tactics check their motives at, and every later `rw` and `simp` then
fails with a missing pattern. So `pullbackUnitComparison_comp_conj` is stated in the unfolded
spelling and the folded form is obtained from it by `:=`.

## References

* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.Ample (IsInvertibleModule)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator
  pullbackNatTensorPowIso_inv_succ)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso
  top_le_preimage_top)
open Stacks.AlgebraicGeometry.ProjChartSectionPullback (pullbackNatTensorPowIso_inv_zero)
open Stacks.TensorSheafSpellingIso (pullbackIdIso pullbackCotensorator_id
  pullbackIdIso_hom_app_tensorUnit)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleFunctorLaws

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable {Y : Scheme.{u}}

/-! ### The identity law on the pullback of a section -/

/-- The identity law carries the pullback along `𝟙 Y` of a global section to that section. -/
theorem pullbackIdIso_hom_app_pullbackSectionHom (M : Y.Modules) (x : Γ(M, ⊤)) :
    ((pullbackIdIso Y).hom.app M).app ⊤
        (pullbackSectionHom (𝟙 Y) M ⊤ ⊤ (top_le_preimage_top (𝟙 Y)) x) = x :=
  (congrArg (fun z => ((pullbackIdIso Y).hom.app M).app ⊤ z)
      (Stacks.PullbackUnitSection.pullbackSectionHom_top_eq (𝟙 Y) M
        (top_le_preimage_top (𝟙 Y)) x)).trans
    (Stacks.PullbackTensorCoherence.pullbackIdIso_hom_app_pullbackUnit Y.toRingedSpace M (op ⊤) x)

/-- Equal morphisms out of a pullback agree on the pullback of a global section. -/
private theorem app_pullbackSectionHom_congr {X Z : Scheme.{u}} (j : X ⟶ Z) {M : Z.Modules}
    {N : X.Modules} {φ φ' : (Scheme.Modules.pullback j).obj M ⟶ N} (h : φ = φ') (x : Γ(M, ⊤)) :
    φ.app ⊤ (pullbackSectionHom j M ⊤ ⊤ (top_le_preimage_top j) x)
      = φ'.app ⊤ (pullbackSectionHom j M ⊤ ⊤ (top_le_preimage_top j) x) := by
  rw [h]

/-! ### The identity law on the comparison of the tensor powers -/

variable (L : Y.Modules) [IsInvertibleModule Y L]

/-- The comparison `(𝟙 Y)^*(L ^⊗ n) ⟶ ((𝟙 Y)^*L) ^⊗ n` of [Stacks, Tag 01CD] iterated, followed by
the `n`-th tensor power of the identity law `β : (𝟙 Y)^*L ≅ L`, is the identity law at `L ^⊗ n`. -/
theorem pullbackNatTensorPowIso_inv_comp_congr (n : ℕ) :
    (pullbackNatTensorPowIso (𝟙 Y) L n).inv ≫
        (natTensorPowCongr ((pullbackIdIso Y).app L) n).hom
      = (pullbackIdIso Y).hom.app (natTensorPow L n) := by
  induction n with
  | zero =>
      refine Eq.trans (Category.comp_id _) ?_
      exact (pullbackNatTensorPowIso_inv_zero (𝟙 Y) L).trans
        (pullbackIdIso_hom_app_tensorUnit Y).symm
  | succ n ih =>
      refine Eq.trans ?_ (pullbackCotensorator_id Y (natTensorPow L n) L).symm
      rw [pullbackNatTensorPowIso_inv_succ, Category.assoc]
      refine congrArg (fun z => pullbackCotensorator (𝟙 Y) (natTensorPow L n) L ≫ z) ?_
      rw [show (natTensorPowCongr ((pullbackIdIso Y).app L) (n + 1)).hom
            = (natTensorPowCongr ((pullbackIdIso Y).app L) n).hom
              ⊗ₘ ((pullbackIdIso Y).app L).hom from rfl,
        ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, ih,
        Category.id_comp]
      exact rfl

/-- The `n`-th tensor power of the identity law `β : (𝟙 Y)^*L ≅ L` carries the pullback along `𝟙 Y`
of a global section of `L ^⊗ n` to that section. -/
theorem congr_hom_app_pullSection_id (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    (natTensorPowCongr ((pullbackIdIso Y).app L) n).hom.app ⊤ (pullSection (𝟙 Y) L n x) = x := by
  refine Eq.trans ?_
    ((app_pullbackSectionHom_congr (𝟙 Y) (pullbackNatTensorPowIso_inv_comp_congr L n) x).trans
      (pullbackIdIso_hom_app_pullbackSectionHom (natTensorPow L n) x))
  exact rfl

/-! ### The identity functor law -/

variable {L}

/-- The pullback of `ψ` along `𝟙 Y` is strictly equivalent to `ψ`, the strict equivalence being the
identity law `(𝟙 Y)^*L ≅ L`. -/
theorem sectionsEquiv_pullbackSections_id {d : ℕ} (ψ : VeroneseSections 𝒜 d L) :
    ProjTripleClassifying.SectionsEquiv 𝒜
      (ProjTriplePullback.pullbackSections 𝒜 ψ (𝟙 Y)) ψ :=
  ⟨(pullbackIdIso Y).app L, fun n x => congr_hom_app_pullSection_id L n (ψ.toFun n x)⟩

/-- The identity functor law for the pullback of a triple: the pullback
`(d, (𝟙 Y)^*L, (𝟙 Y)^* ∘ ψ)` of a triple `(d, L, ψ)` along `𝟙 Y` is strictly equivalent to it. -/
@[stacks 01N4 "the identity functor law for the pullback of a triple of this section: the \
pullback along the identity is STRICTLY EQUIVALENT to the triple, in the SectionsEquiv sense of \
the section; the composition law is sectionsEquiv_pullbackTriple_comp below"]
theorem sectionsEquiv_pullbackTriple_id (t : ProjTripleClassifying.Triple 𝒜 Y) :
    ProjTripleClassifying.SectionsEquiv 𝒜 (ProjTriplePullback.pullbackTriple 𝒜 t (𝟙 Y)).psi
      t.psi :=
  have := t.isInvertible
  sectionsEquiv_pullbackSections_id 𝒜 t.psi

/-! ### The composition law -/

section CompLaw

open Stacks.PullbackUnitSection (unitPullbackHom)
open Stacks.SectionRingGeometric (unitComparison unitModule)
open Stacks.TensorSheafSpellingIso (pullbackCompIso pullbackCotensorator_comp
  unitPullbackHom_eq_pullbackUnitComparison)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator_whiskerRight)

variable {W W' W'' : Scheme.{u}} (f : W ⟶ W') (g : W' ⟶ W'')

/-- The composition law is compatible with the comparison at the unit object, with the
comparison `Stacks.PullbackUnitSection.unitPullbackHom` written out as
`Stacks.PullbackTensorCoherence.pullbackUnitComparison` conjugated by the comparison of the two
unit objects. -/
private theorem pullbackUnitComparison_comp_conj :
    (pullbackCompIso f g).hom.app (𝟙_ W''.Modules) ≫
        ((Scheme.Modules.pullback (f ≫ g)).map (unitComparison W'').hom ≫
          Stacks.PullbackTensorCoherence.pullbackUnitComparison
              (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom (f ≫ g))) ≫
            (unitComparison W).inv)
      = (Scheme.Modules.pullback f).map
            ((Scheme.Modules.pullback g).map (unitComparison W'').hom ≫
              Stacks.PullbackTensorCoherence.pullbackUnitComparison
                  (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g)) ≫
                (unitComparison W').inv) ≫
          ((Scheme.Modules.pullback f).map (unitComparison W').hom ≫
            Stacks.PullbackTensorCoherence.pullbackUnitComparison
                (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f)) ≫
              (unitComparison W).inv) := by
  have hcomp : (pullbackCompIso f g).hom.app (unitModule W'') ≫
        Stacks.PullbackTensorCoherence.pullbackUnitComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom (f ≫ g)))
      = (Scheme.Modules.pullback f).map
            (Stacks.PullbackTensorCoherence.pullbackUnitComparison
              (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g))) ≫
          Stacks.PullbackTensorCoherence.pullbackUnitComparison
            (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f)) :=
    Stacks.PullbackTensorCoherence.pullbackUnitComparison_comp _ _
  have hcomp' : (pullbackCompIso f g).hom.app (unitModule W'') ≫
        Stacks.PullbackTensorCoherence.pullbackUnitComparison
            (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom (f ≫ g))) ≫
          (unitComparison W).inv
      = (Scheme.Modules.pullback f).map
            (Stacks.PullbackTensorCoherence.pullbackUnitComparison
              (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g))) ≫
          Stacks.PullbackTensorCoherence.pullbackUnitComparison
              (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f)) ≫
            (unitComparison W).inv :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (unitComparison W).inv) hcomp).trans (Category.assoc _ _ _))
  have hnat : (pullbackCompIso f g).hom.app (𝟙_ W''.Modules) ≫
        (Scheme.Modules.pullback (f ≫ g)).map (unitComparison W'').hom
      = (Scheme.Modules.pullback f).map
            ((Scheme.Modules.pullback g).map (unitComparison W'').hom) ≫
          (pullbackCompIso f g).hom.app (unitModule W'') :=
    ((pullbackCompIso f g).hom.naturality (unitComparison W'').hom).symm
  have hsplit : (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback g).map (unitComparison W'').hom ≫
          Stacks.PullbackTensorCoherence.pullbackUnitComparison
              (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g)) ≫
            (unitComparison W').inv)
      = (Scheme.Modules.pullback f).map
            ((Scheme.Modules.pullback g).map (unitComparison W'').hom) ≫
          (Scheme.Modules.pullback f).map
              (Stacks.PullbackTensorCoherence.pullbackUnitComparison
                (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g))) ≫
            (Scheme.Modules.pullback f).map (unitComparison W').inv :=
    ((Scheme.Modules.pullback f).map_comp _ _).trans
      (congrArg (fun z => (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback g).map (unitComparison W'').hom) ≫ z)
        ((Scheme.Modules.pullback f).map_comp _ _))
  have htail : (Scheme.Modules.pullback f).map (unitComparison W').inv ≫
        (Scheme.Modules.pullback f).map (unitComparison W').hom ≫
          (Stacks.PullbackTensorCoherence.pullbackUnitComparison
            (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f)) ≫ (unitComparison W).inv)
      = Stacks.PullbackTensorCoherence.pullbackUnitComparison
          (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f)) ≫ (unitComparison W).inv :=
    Iso.map_inv_hom_id_assoc (unitComparison W') (Scheme.Modules.pullback f) _
  rw [hsplit, reassoc_of% hnat, hcomp']
  simp only [Category.assoc]
  exact congrArg (fun z => (Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullback g).map (unitComparison W'').hom) ≫
    (Scheme.Modules.pullback f).map
      (Stacks.PullbackTensorCoherence.pullbackUnitComparison
        (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g))) ≫ z) htail.symm

/-- The comparison `f^*g^*𝒪 ⟶ 𝒪` of [Stacks, Tag 01CD] is the composition law followed by the
comparison for the composite. -/
theorem pullbackCompIso_hom_app_tensorUnit :
    (pullbackCompIso f g).hom.app (𝟙_ W''.Modules) ≫ unitPullbackHom (f ≫ g)
      = (Scheme.Modules.pullback f).map (unitPullbackHom g) ≫ unitPullbackHom f :=
  pullbackUnitComparison_comp_conj f g

variable (L : W''.Modules) [IsInvertibleModule W'' L]

/-- The composition law at `L ^⊗ n` followed by the comparison
`(f ≫ g)^*(L ^⊗ n) ⟶ ((f ≫ g)^*L) ^⊗ n` of [Stacks, Tag 01CD] iterated is the two comparisons in
turn, followed by the `n`-th tensor power of the composition law at `L`. -/
theorem pullbackCompIso_comp_pullbackNatTensorPowIso_inv (n : ℕ) :
    (pullbackCompIso f g).hom.app (natTensorPow L n) ≫
        (pullbackNatTensorPowIso (f ≫ g) L n).inv
      = (Scheme.Modules.pullback f).map (pullbackNatTensorPowIso g L n).inv ≫
        (pullbackNatTensorPowIso f ((Scheme.Modules.pullback g).obj L) n).inv ≫
          (natTensorPowCongr ((pullbackCompIso f g).app L) n).hom := by
  induction n with
  | zero =>
      rw [pullbackNatTensorPowIso_inv_zero, pullbackNatTensorPowIso_inv_zero,
        pullbackNatTensorPowIso_inv_zero,
        show (natTensorPowCongr ((pullbackCompIso f g).app L) 0).hom
          = 𝟙 (natTensorPow ((Scheme.Modules.pullback (f ≫ g)).obj L) 0) from rfl]
      exact (pullbackCompIso_hom_app_tensorUnit f g).trans
        (congrArg (fun z => (Scheme.Modules.pullback f).map (unitPullbackHom g) ≫ z)
          (Category.comp_id (unitPullbackHom f)).symm)
  | succ n ih =>
      have key : (pullbackCompIso f g).hom.app (natTensorPow L (n + 1)) ≫
            pullbackCotensorator (f ≫ g) (natTensorPow L n) L
          = (Scheme.Modules.pullback f).map (pullbackCotensorator g (natTensorPow L n) L) ≫
            pullbackCotensorator f ((Scheme.Modules.pullback g).obj (natTensorPow L n))
                ((Scheme.Modules.pullback g).obj L) ≫
              ((pullbackCompIso f g).hom.app (natTensorPow L n) ⊗ₘ
                (pullbackCompIso f g).hom.app L) :=
        pullbackCotensorator_comp f g (natTensorPow L n) L
      rw [pullbackNatTensorPowIso_inv_succ, pullbackNatTensorPowIso_inv_succ,
        pullbackNatTensorPowIso_inv_succ,
        show (natTensorPowCongr ((pullbackCompIso f g).app L) (n + 1)).hom
            = (natTensorPowCongr ((pullbackCompIso f g).app L) n).hom
              ⊗ₘ ((pullbackCompIso f g).app L).hom from rfl,
        reassoc_of% key, Functor.map_comp_assoc]
      simp only [Category.assoc]
      rw [reassoc_of% (pullbackCotensorator_whiskerRight f (pullbackNatTensorPowIso g L n).inv
        ((Scheme.Modules.pullback g).obj L))]
      simp only [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
      rw [ih]
      exact rfl

/-- Pulling a global section back along a composite is pulling it back twice, read through the
composition law. -/
theorem pullbackSectionHom_comp (M : W''.Modules) (x : Γ(M, ⊤)) :
    pullbackSectionHom f ((Scheme.Modules.pullback g).obj M) ⊤ ⊤ (top_le_preimage_top f)
        (pullbackSectionHom g M ⊤ ⊤ (top_le_preimage_top g) x)
      = (((pullbackCompIso f g).app M).inv).app ⊤
          (pullbackSectionHom (f ≫ g) M ⊤ ⊤ (top_le_preimage_top (f ≫ g)) x) :=
  (congrArg
      (fun z => pullbackSectionHom f ((Scheme.Modules.pullback g).obj M) ⊤ ⊤
        (top_le_preimage_top f) z)
      (Stacks.PullbackUnitSection.pullbackSectionHom_top_eq g M
        (top_le_preimage_top g) x)).trans
    ((Stacks.PullbackUnitSection.pullbackSectionHom_top_eq f
          ((Scheme.Modules.pullback g).obj M) (top_le_preimage_top f) _).trans
      ((Stacks.PullbackTensorCoherence.pullbackCompIso_app_inv_pullbackUnit
            (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f))
            (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom g)) M (op ⊤) x).symm.trans
        (congrArg (fun z => (((pullbackCompIso f g).app M).inv).app ⊤ z)
          (Stacks.PullbackUnitSection.pullbackSectionHom_top_eq (f ≫ g) M
            (top_le_preimage_top (f ≫ g)) x).symm)))

/-- The `n`-th tensor power of the composition law
`(pullbackCompIso f g).app L : f^*g^*L ≅ (f ≫ g)^*L` carries the twice-pulled-back global section
of `L ^⊗ n` to the section pulled back along the composite. -/
theorem congr_hom_app_pullSection_comp (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    (natTensorPowCongr ((pullbackCompIso f g).app L) n).hom.app ⊤
        (pullSection f ((Scheme.Modules.pullback g).obj L) n (pullSection g L n x))
      = pullSection (f ≫ g) L n x := by
  have hmod : ((pullbackCompIso f g).app (natTensorPow L n)).inv ≫
        ((Scheme.Modules.pullback f).map (pullbackNatTensorPowIso g L n).inv ≫
          (pullbackNatTensorPowIso f ((Scheme.Modules.pullback g).obj L) n).inv ≫
            (natTensorPowCongr ((pullbackCompIso f g).app L) n).hom)
      = (pullbackNatTensorPowIso (f ≫ g) L n).inv :=
    (Iso.inv_comp_eq ((pullbackCompIso f g).app (natTensorPow L n))).mpr
      (pullbackCompIso_comp_pullbackNatTensorPowIso_inv f g L n).symm
  refine Eq.trans ?_ (app_pullbackSectionHom_congr (f ≫ g) hmod x)
  refine congrArg (fun z => (natTensorPowCongr ((pullbackCompIso f g).app L) n).hom.app ⊤
    ((pullbackNatTensorPowIso f ((Scheme.Modules.pullback g).obj L) n).inv.app ⊤ z)) ?_
  exact (Stacks.PullbackUnitSection.pullbackSectionHom_app f
      (pullbackNatTensorPowIso g L n).inv ⊤ ⊤ (top_le_preimage_top f)
      (pullbackSectionHom g (natTensorPow L n) ⊤ ⊤ (top_le_preimage_top g) x)).trans
    (congrArg (fun z => ((Scheme.Modules.pullback f).map
        (pullbackNatTensorPowIso g L n).inv).app ⊤ z)
      (pullbackSectionHom_comp f g (natTensorPow L n) x))

variable {L}

/-- The pullback of `ψ` along `f ≫ g` is strictly equivalent to the pullback along `g` followed by
the pullback along `f`, the strict equivalence being the composition law `f^*g^*L ≅ (f ≫ g)^*L`. -/
theorem sectionsEquiv_pullbackSections_comp {d : ℕ} (ψ : VeroneseSections 𝒜 d L) :
    ProjTripleClassifying.SectionsEquiv 𝒜
      (ProjTriplePullback.pullbackSections 𝒜
        (ProjTriplePullback.pullbackSections 𝒜 ψ g) f)
      (ProjTriplePullback.pullbackSections 𝒜 ψ (f ≫ g)) :=
  ⟨(pullbackCompIso f g).app L, fun n x => congr_hom_app_pullSection_comp f g L n (ψ.toFun n x)⟩

/-- The composition functor law for the pullback of a triple: the pullback along `f` of the
pullback along `g` of a triple is strictly equivalent to its pullback along `f ≫ g`. -/
@[stacks 01N4 "the composition functor law for the pullback of a triple of this section: the \
pullback along f of the pullback along g is STRICTLY EQUIVALENT to the pullback along f ≫ g, in \
the SectionsEquiv sense of the section"]
theorem sectionsEquiv_pullbackTriple_comp (t : ProjTripleClassifying.Triple 𝒜 W'') :
    ProjTripleClassifying.SectionsEquiv 𝒜
      (ProjTriplePullback.pullbackTriple 𝒜 (ProjTriplePullback.pullbackTriple 𝒜 t g) f).psi
      (ProjTriplePullback.pullbackTriple 𝒜 t (f ≫ g)).psi :=
  have := t.isInvertible
  sectionsEquiv_pullbackSections_comp 𝒜 f g t.psi

end CompLaw

/-! ### The degree-one coherence of the pullback of a section -/

section DegreeOne

open Stacks.AlgebraicGeometry.MorphismToProjUniversal (unitorPow)

variable {Y' : Scheme.{u}} (j : Y' ⟶ Y) (L : Y.Modules) [IsInvertibleModule Y L]

/-- Evaluating a composite of two morphisms of `𝒪_{Y'}`-modules on a section is evaluating the
second on the value of the first. -/
private theorem hom_app_comp_apply {A₀ B₀ C₀ : Y'.Modules} (p : A₀ ⟶ B₀) (q : B₀ ⟶ C₀)
    (U : Y'.Opens) (x : Γ(A₀, U)) : (p ≫ q).app U x = q.app U (p.app U x) := by
  rw [Scheme.Modules.Hom.comp_app]
  exact CategoryTheory.comp_apply _ _ x

/-- The comparison `j^*(L ^⊗ 1) ⟶ (j^*L) ^⊗ 1` of [Stacks, Tag 01CD] is compatible with the two
left unitors. -/
theorem pullbackNatTensorPowIso_inv_one_comp_unitorPow :
    (pullbackNatTensorPowIso j L 1).inv ≫
        (unitorPow ((Scheme.Modules.pullback j).obj L)).hom
      = (Scheme.Modules.pullback j).map (unitorPow L).hom := by
  rw [pullbackNatTensorPowIso_inv_succ j L 0, pullbackNatTensorPowIso_inv_zero j L]
  exact (Category.assoc _ _ _).trans
    (Stacks.TensorSheafSpellingIso.pullbackCotensorator_leftUnitor Y j L).symm

/-- The left-unitor image of the pullback of a global section `y` of `L ^⊗ 1` is the pullback of
the left-unitor image of `y`. -/
theorem unitorPow_hom_app_pullSection_one (y : Γ(natTensorPow L 1, ⊤)) :
    (unitorPow ((Scheme.Modules.pullback j).obj L)).hom.app ⊤ (pullSection j L 1 y)
      = AlgebraicGeometry.pullbackSectionHom j L ⊤ ⊤ (top_le_preimage_top j)
          ((unitorPow L).hom.app ⊤ y) := by
  refine Eq.trans ?_
    ((app_pullbackSectionHom_congr j (pullbackNatTensorPowIso_inv_one_comp_unitorPow j L) y).trans
      ?_)
  · exact (hom_app_comp_apply (pullbackNatTensorPowIso j L 1).inv
      (unitorPow ((Scheme.Modules.pullback j).obj L)).hom ⊤ _).symm
  · exact (Stacks.PullbackUnitSection.pullbackSectionHom_app j (unitorPow L).hom ⊤ ⊤
      (top_le_preimage_top j) y).symm

end DegreeOne


end Stacks.AlgebraicGeometry.ProjTripleFunctorLaws

end
